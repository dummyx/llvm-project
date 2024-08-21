#include "clang/StaticAnalyzer/Checkers/BuiltinCheckerRegistration.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/BugReporter/CommonBugCategories.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include <optional>

using namespace clang;
using namespace ento;

namespace {
class RubyMissGuardChecker : public Checker<check::PostStmt<DeclStmt>> {
  const BugType BT{this, "Missing RB_GC_GUARD", categories::MemoryError};

public:
  void checkPostStmt(const DeclStmt *DS, CheckerContext &C) const;

private:
  bool isValueType(const VarDecl *VD) const;
  bool hasGuard(const VarDecl *VD, CheckerContext &C) const;
  bool hasGuardMacro(const DeclStmt *DS, CheckerContext &C) const;
  void reportBug(StringRef Msg, CheckerContext &C) const;
};

void RubyMissGuardChecker::checkPostStmt(const DeclStmt *DS,
                                        CheckerContext &C) const {
  for (const auto *D : DS->decls()) {
    if (const auto *VD = dyn_cast<VarDecl>(D)) {
      if (isValueType(VD) && !(hasGuard(VD, C) || hasGuardMacro(DS, C))) {
        reportBug("VALUE variable is not guarded by RB_GC_GUARD", C);
      }
    }
  }
}

bool RubyMissGuardChecker::isValueType(const VarDecl *VD) const {
  return VD->getType().getAsString() == "VALUE";
}

bool RubyMissGuardChecker::hasGuardMacro(const DeclStmt *DS, CheckerContext &C) const {
  const SourceManager &SM = C.getSourceManager();
  for (const auto *D : DS->decls()) {
    if (const auto *VD = dyn_cast<VarDecl>(D)) {
      const Expr *Init = VD->getInit();
      if (!Init)
        continue;

      SourceLocation Loc = Init->getExprLoc();
      if (SM.isMacroBodyExpansion(Loc)) {
        StringRef MacroName = Lexer::getImmediateMacroName(Loc, SM, C.getLangOpts());
        if (MacroName == "RB_GC_GUARD")
          return true;
      }
    }
  }
  return false;
}

bool RubyMissGuardChecker::hasGuard(const VarDecl *VD, CheckerContext &C) const {
  const Expr *Init = VD->getInit();
  if (!Init)
    return false;

  if (const auto *CE = dyn_cast<CallExpr>(Init)) {
    const FunctionDecl *FD = CE->getDirectCallee();
    if (FD) {
      std::string funcName = FD->getNameAsString();
      if (funcName == "rb_gc_guarded_ptr" ||
          funcName == "rb_gc_guarded_ptr_val") {
        return true;
      }
    }
  }
  return false;
}

void RubyMissGuardChecker::reportBug(StringRef Msg, CheckerContext &C) const {
  if (ExplodedNode *N = C.generateErrorNode()) {
    auto R = std::make_unique<PathSensitiveBugReport>(BT, Msg, N);
    C.emitReport(std::move(R));
  }
}
} // end anonymous namespace

void ento::registerRubyMissGuardChecker(CheckerManager &mgr) {
  mgr.registerChecker<RubyMissGuardChecker>();
}

bool ento::shouldRegisterRubyMissGuardChecker(const CheckerManager &mgr) {
  return true;
}
