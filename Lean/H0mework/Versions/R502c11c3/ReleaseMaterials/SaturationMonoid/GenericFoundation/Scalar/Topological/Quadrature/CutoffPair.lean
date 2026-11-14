import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedQuadrature

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The second actual cutoff is twice the first positive cutoff. -/
def doubledCut (m : Nat) : Nat := 2 * m + 1

theorem doubledCut_tendsto : Tendsto doubledCut atTop atTop :=
  tendsto_atTop_mono (fun m => by change m ≤ 2*m+1; omega) tendsto_id

/-- The two actual cutoffs determine the first correction without reading the leading field. -/
def cutoffPair (observed : Nat → E) (m : Nat) : E :=
  (2*((m : ℝ)+1)) • (observed m-observed (doubledCut m))

theorem cutoff_pair_tendsto {observed : Nat → E} {leading velocity : E}
    (firstCorrection : Tendsto (fun m : Nat => ((m : ℝ)+1) • (observed m-leading))
      atTop (𝓝 velocity)) :
    Tendsto (cutoffPair observed) atTop (𝓝 velocity) := by
  let scaled := fun m : Nat => ((m : ℝ)+1) • (observed m-leading)
  have forward := firstCorrection.const_smul (2 : ℝ)
  have second := firstCorrection.comp doubledCut_tendsto
  have result := forward.sub second
  have read : (2 : ℝ) • velocity - velocity = velocity := by
    rw [two_smul, add_sub_cancel_left]
  rw [read] at result
  apply result.congr'
  filter_upwards with m
  change (2 : ℝ) • scaled m - scaled (doubledCut m) = cutoffPair observed m
  have double : ((doubledCut m : ℕ) : ℝ) + 1 = 2*((m : ℝ)+1) := by
    unfold doubledCut
    push_cast
    ring
  simp only [scaled, cutoffPair, double, smul_smul, ← smul_sub, sub_sub_sub_cancel_right]

end SourceGeneratedQuadrature
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
