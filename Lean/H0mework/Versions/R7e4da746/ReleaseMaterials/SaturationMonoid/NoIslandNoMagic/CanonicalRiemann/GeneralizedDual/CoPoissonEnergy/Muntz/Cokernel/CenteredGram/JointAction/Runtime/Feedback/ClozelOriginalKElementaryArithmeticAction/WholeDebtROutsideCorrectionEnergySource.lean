import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtROutsideCorrectionRConsumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtROutsideCorrectionEnergySource
open BurnolPhysicalState
open scoped InnerProductSpace
open private correction_outside from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRCorrectionActionSource
open private original_R_real_energy from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyEnergySource
namespace C
export OriginalWholeDebtROutsideCorrectionRConsumer
  (actualInput actualResult actual_input_source actual_source_equation)
end C
namespace Energy
export OriginalKCrossParameterRAdjointSource.CayleyEnergySource (sourceDamping sourceDamping_pos)
end Energy
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "x" => C.actualInput observation nontrivial half depth ordinal
local notation "y" => C.actualResult observation nontrivial half depth ordinal

theorem actual_input_outside : O x = x := by
  rw [C.actual_input_source]
  exact correction_outside c

private theorem actual_pairing (value : BurnolL2) :
    inner ℂ x (O value) = inner ℂ x value := by
  have member : x ∈ (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ :=
    Submodule.starProjection_eq_self_iff.mp
      (actual_input_outside observation nontrivial half depth ordinal)
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left
    ⟨x, member⟩ value

/-- The original whole-R Gram law pays the actual projected outside pairing. -/
theorem actual_outside_balance :
    2 * (inner ℂ x (O y)).re = -Energy.sourceDamping c * ‖y‖ ^ 2 := by
  rw [actual_pairing, C.actual_source_equation]
  exact original_R_real_energy c x

theorem actual_outside_bound :
    Energy.sourceDamping c * ‖y‖ ^ 2 ≤ 2 * ‖x‖ * ‖O y‖ := by
  have energy := actual_outside_balance observation nontrivial half depth ordinal
  have realBound := (abs_le.mp (Complex.abs_re_le_norm (inner ℂ x (O y)))).1
  have pairingBound : ‖inner ℂ x (O y)‖ ≤ ‖x‖ * ‖O y‖ := norm_inner_le_norm x (O y)
  nlinarith

/-- Vanishing of the full B complement reflects the same actual input, including a zero input. -/
theorem actual_outside_zero_iff : O y = 0 ↔ x = 0 := by
  constructor
  · intro zero
    have energy := actual_outside_balance observation nontrivial half depth ordinal
    rw [zero, inner_zero_right, Complex.zero_re, mul_zero] at energy
    have damping := Energy.sourceDamping_pos c
    have productZero : Energy.sourceDamping c * ‖y‖ ^ 2 = 0 := by linarith [energy]
    have squaredZero : ‖y‖ ^ 2 = 0 :=
      (mul_eq_zero.mp productZero).resolve_left (ne_of_gt damping)
    have normZero : ‖y‖ = 0 := by nlinarith [norm_nonneg y]
    have resultZero := norm_eq_zero.mp normZero
    have originalZero : burnolDirectRightResolvent ((c).value / 2) x = 0 :=
      (C.actual_source_equation observation nontrivial half depth ordinal).symm.trans resultZero
    apply burnolDirectRightResolvent_reflects_zero ((c).value / 2) _ x originalZero
    rw [Complex.div_re]
    norm_num
    linarith [(c).rightHalf]
  · intro zero
    have resultZero : y = 0 :=
      (C.actual_source_equation observation nontrivial half depth ordinal).trans
        ((congrArg (burnolDirectRightResolventCLM c) zero).trans (map_zero _))
    rw [resultZero]
    exact map_zero _

end OriginalWholeDebtROutsideCorrectionEnergySource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalWholeDebtROutsideCorrectionEnergySource"

