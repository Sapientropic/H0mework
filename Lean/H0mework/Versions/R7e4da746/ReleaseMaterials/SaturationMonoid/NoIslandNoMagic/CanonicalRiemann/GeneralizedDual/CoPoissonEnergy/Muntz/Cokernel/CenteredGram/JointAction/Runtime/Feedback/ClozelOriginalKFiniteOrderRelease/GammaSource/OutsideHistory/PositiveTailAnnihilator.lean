import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.DilationFromPowers

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRSourceJointContact.OutsideHistory

open Filter Set
open scoped Topology

local notation "R" => burnolDirectRightResolventCLM
local notation "D" => burnolMultiplicativeDilation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

private theorem observation_zero_of_positive_powers (read : BurnolL2 →L[ℂ] E)
    (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (silent : ∀ n : Nat, read (((R c)^(n+1)) v) = 0) : read v = 0 := by
  let orbit : ℝ → E := fun h => read (D (-h/2) v)
  have continuous : Continuous orbit :=
    read.continuous.comp ((burnolMultiplicativeDilation_stronglyContinuous v).comp (by fun_prop))
  have limit : Tendsto orbit (𝓝[>] (0 : ℝ)) (𝓝 (read v)) := by
    have atZero : orbit 0 = read v := by
      simp only [orbit, neg_zero, zero_div, burnolMultiplicativeDilation_zero]
    rw [← atZero]
    exact continuous.continuousAt.continuousWithinAt
  have positive : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioi 0 := self_mem_nhdsWithin
  have quiet : orbit =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => (0 : E)) :=
    positive.mono fun h pos =>
      DilationFromPowers.observed_inward_zero read c v silent h pos
  exact tendsto_nhds_unique_of_eventuallyEq limit tendsto_const_nhds quiet

/-- The original inward clock propagates silence from a whole tail back to every source power. -/
theorem original_power_read_zero_of_tail (read : BurnolL2 →L[ℂ] E)
    (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) (cutoff : Nat)
    (silent : ∀ n ≥ cutoff, read (((R c)^n) v) = 0) (n : Nat) :
    read (((R c)^n) v) = 0 := by
  induction cutoff with
  | zero => exact silent n (Nat.zero_le n)
  | succ k previous =>
    apply previous
    intro j hj
    rcases eq_or_lt_of_le hj with eq | lt
    · subst j
      apply observation_zero_of_positive_powers read c
      intro l
      rw [← mul_apply_eq_comp, ← pow_add]
      exact silent _ (by omega)
    · exact silent j lt

end OriginalRSourceJointContact.OutsideHistory
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
