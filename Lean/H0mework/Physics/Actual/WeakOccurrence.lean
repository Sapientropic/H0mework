import Mathlib.Analysis.InnerProductSpace.Defs

/-! The original countable Hilbert weak-limit occurrence, kept under its
existing declaration namespace so all historical and live consumers share it. -/

set_option autoImplicit false

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterFriedrichsAllOrderWeakLimitOccurrence

open Filter

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [TopologicalSpace.SeparableSpace H]

structure CountableHilbertWeakLimitOccurrence
    (sequence : ℕ → ℕ → H) where
  limit : ℕ → H
  subsequence : ℕ → ℕ
  subsequenceStrict : StrictMono subsequence
  weakConvergence : ∀ coordinate test,
    Tendsto
      (fun index => inner ℝ (sequence (subsequence index) coordinate) test)
      atTop (nhds (inner ℝ (limit coordinate) test))

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterFriedrichsAllOrderWeakLimitOccurrence
