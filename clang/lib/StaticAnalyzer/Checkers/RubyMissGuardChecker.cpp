#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Type.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Lex/Lexer.h"
#include "clang/StaticAnalyzer/Checkers/BuiltinCheckerRegistration.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/BugReporter/CommonBugCategories.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"

using namespace clang;
using namespace ento;
using namespace clang::ast_matchers;

namespace {
class RubyMissGuardChecker : public Checker<check::PostStmt<DeclStmt>> {
  const BugType BT{this, "Missing RB_GC_GUARD", categories::MemoryError};

public:
  void checkPostStmt(const DeclStmt *DS, CheckerContext &C) const;

private:
  bool isValueType(const VarDecl *VD) const;
  bool hasGuard(const VarDecl *DS, CheckerContext &C) const;
  bool hasGuardMacro(const DeclStmt *DS, CheckerContext &C) const;
  bool isShouldHaveGuard(const VarDecl *VD, CheckerContext &C) const;
  void reportBug(StringRef Msg, CheckerContext &C) const;
};

void RubyMissGuardChecker::checkPostStmt(const DeclStmt *DS,
                                         CheckerContext &C) const {
  for (const auto *D : DS->decls()) {
    if (const auto *VD = dyn_cast<VarDecl>(D)) {
      if (isValueType(VD)) {
        if (!isShouldHaveGuard(VD, C)) {
          continue;
        }
        if (!(hasGuard(VD, C) || hasGuardMacro(DS, C))) {
          reportBug("VALUE variable is not guarded by RB_GC_GUARD", C);
        }
      }
    }
  }
}

bool RubyMissGuardChecker::isValueType(const VarDecl *VD) const {
  return VD->getType().getAsString() == "VALUE";
}

bool RubyMissGuardChecker::isShouldHaveGuard(const VarDecl *VD,
                                             CheckerContext &C) const {
  bool isValueInnerPointerUsed = false;
  bool isValueDereferenced = false;
  bool isGCMightHappen = false;

  auto analysisDeclContext = C.getCurrentAnalysisDeclContext();
  const CFG *cfg = analysisDeclContext->getCFG();

  if (!cfg)
    return false;

  for (const auto *block : *cfg) {

    for (const auto &elem : *block) {
      if (std::optional<CFGStmt> stmtElem = elem.getAs<CFGStmt>()) {
        const Stmt *stmt = stmtElem->getStmt();

        if (const auto *CE = dyn_cast<CallExpr>(stmt)) {
          const FunctionDecl *FD = CE->getDirectCallee();
          if (FD) {
            std::string funcName = FD->getNameAsString();
            if (funcName.find("new") != std::string::npos ||
                funcName.find("alloc") != std::string::npos) {
              isGCMightHappen = true;
            }
          }
        }
        if (const auto *UO = dyn_cast<UnaryOperator>(stmt)) {
          if (UO->getOpcode() == UO_Deref || UO->getOpcode() == UO_AddrOf) {
            if (const auto *DRE =
                    dyn_cast<DeclRefExpr>(UO->getSubExpr()->IgnoreImpCasts())) {
              if (DRE->getDecl() == VD) {
                isValueDereferenced = true;
              }
            }
          }
        }
        if (const auto *ME = dyn_cast<MemberExpr>(stmt)) {
          if (const auto *DRE =
                  dyn_cast<DeclRefExpr>(ME->getBase()->IgnoreImpCasts())) {
            if (DRE->getDecl() == VD) {
              isValueInnerPointerUsed = true;
            }
          }
        }

        if (const auto *CE = dyn_cast<CastExpr>(stmt)) {
          const Expr *subExpr = CE->getSubExpr()->IgnoreImpCasts();
          if (const auto *DRE = dyn_cast<DeclRefExpr>(subExpr)) {
            if (DRE->getDecl() == VD) {
              isValueInnerPointerUsed = true;
            }
          }
        }

        if (const auto *UO = dyn_cast<UnaryOperator>(stmt)) {
          if (UO->getOpcode() == UO_Deref || UO->getOpcode() == UO_AddrOf) {
            if (const auto *DRE =
                    dyn_cast<DeclRefExpr>(UO->getSubExpr()->IgnoreImpCasts())) {
              if (DRE->getDecl() == VD) {
                isValueInnerPointerUsed = true;
              }
            }
          }
        }

        if (const auto *ME = dyn_cast<MemberExpr>(stmt)) {
          if (const auto *DRE =
                  dyn_cast<DeclRefExpr>(ME->getBase()->IgnoreImpCasts())) {
            if (DRE->getDecl() == VD) {
              isValueInnerPointerUsed = true;
            }
          }
        }

        if (const auto *CE = dyn_cast<CallExpr>(stmt)) {
          for (unsigned i = 0; i < CE->getNumArgs(); ++i) {
            const Expr *arg = CE->getArg(i)->IgnoreImpCasts();
            if (const auto *DRE = dyn_cast<DeclRefExpr>(arg)) {
              if (DRE->getDecl() == VD) {
                isValueInnerPointerUsed = true;
              }
            }
          }
        }
      }
    }
  }

  bool shouldHaveGuard =
      (isValueInnerPointerUsed) && (isGCMightHappen) && (!isValueDereferenced);

  return shouldHaveGuard;
}

bool RubyMissGuardChecker::hasGuardMacro(const DeclStmt *DS,
                                         CheckerContext &C) const {
  const SourceManager &SM = C.getSourceManager();
  for (const auto *D : DS->decls()) {
    if (const auto *VD = dyn_cast<VarDecl>(D)) {
      const Expr *Init = VD->getInit();
      if (!Init)
        continue;

      SourceLocation Loc = Init->getExprLoc();
      if (SM.isMacroBodyExpansion(Loc)) {
        StringRef MacroName =
            Lexer::getImmediateMacroName(Loc, SM, C.getLangOpts());
        if (MacroName == "RB_GC_GUARD")
          return true;
      }
    }
  }
  return false;
}

bool RubyMissGuardChecker::hasGuard(const VarDecl *VD,
                                    CheckerContext &C) const {
  auto analysisDeclContext = C.getCurrentAnalysisDeclContext();
  const CFG *cfg = analysisDeclContext->getCFG();
  if (!cfg)
    return false;

  for (const auto *block : *cfg) {
    for (const auto &elem : *block) {
      if (std::optional<CFGStmt> stmtElem = elem.getAs<CFGStmt>()) {
        const Stmt *stmt = stmtElem->getStmt();
        if (const auto *CE = dyn_cast<CallExpr>(stmt)) {
          const FunctionDecl *FD = CE->getDirectCallee();
          if (FD) {
            std::string funcName = FD->getNameAsString();
            if (funcName == "rb_gc_guarded_ptr" ||
                funcName == "rb_gc_guarded_ptr_val") {
              return true;
            }
          }
        }
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
