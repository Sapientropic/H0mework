import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.EmploymentIndependentExit

/-!
# Source-owned exit-repair compiler

An exit repair is selected from the exact failure kind, not from a visible
capacity readout.  This module fixes only the finite policy language and its
source compiler.  It contains no failure witness, capacity, effectiveness
proof, outcome table, root, ledger, or completed temporal family.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace UBI
namespace Policy

/-- Two source distinctions which require opposite geometry repairs.  A
downstream origin must still prove which constructor its exact source facts
generate; this carrier alone is not causal evidence. -/
inductive ExactExitFailureKind
  | tenureCapture
  | routeBottleneck
  deriving DecidableEq, Repr

/-- Exact geometry transformations available to the fixed UBI policy. -/
inductive ExactExitRepair
  | removeCapture
  | restoreRoute
  deriving DecidableEq, Repr

/-- A source-owned policy compiler.  Correctness is deliberately absent:
downstream geometry must compute the outcome of the generated repair. -/
structure SourceOwnedExitRepairCompiler where
  FailureKind : Type
  Repair : Type
  compile : FailureKind → Repair

/-- The fixed cause-sensitive repair law. -/
def exactExitRepairCompiler : SourceOwnedExitRepairCompiler where
  FailureKind := ExactExitFailureKind
  Repair := ExactExitRepair
  compile
    | .tenureCapture => .removeCapture
    | .routeBottleneck => .restoreRoute

@[simp] theorem exactExitRepairCompiler_tenureCapture :
    exactExitRepairCompiler.compile .tenureCapture = .removeCapture :=
  rfl

@[simp] theorem exactExitRepairCompiler_routeBottleneck :
    exactExitRepairCompiler.compile .routeBottleneck = .restoreRoute :=
  rfl

theorem exact_failure_kinds_generate_different_repairs :
    exactExitRepairCompiler.compile .tenureCapture ≠
      exactExitRepairCompiler.compile .routeBottleneck := by
  intro equality
  cases equality

end Policy
end UBI
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.UBI.Policy.exact_failure_kinds_generate_different_repairs
