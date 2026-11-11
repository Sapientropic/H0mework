import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKForcedInverseSourceFields
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusForcedPriceConsumer

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusForcedRegisteredRConsumer
open Complex BurnolPhysicalState
open OriginalKSourceResolventReconstruction OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalKCrossParameterRAdjointSource.UnweightedCayleySource
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open scoped InnerProductSpace
open private outsideColumn_ne_zero from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusRActionSource
namespace W
export OriginalKForcedInverseSourceWriteback
  (actualValue actualInput actualResponseInput actual_input_value actual_response_value actual_value_generated)
end W
namespace P
export OriginalWholeDebtRJointMobiusForcedPriceConsumer
  (nativeProgramme actual_source_price actual_native_programme actual_native_programme_ne_zero
   actual_forcing_response_not_Pa physicalInput)
end P
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "next" => W.actualValue observation nontrivial half depth
local notation "price" => P.nativeProgramme c
local notation "outside" => OriginalKCombPhysicalAction.physicalRemainder

def actualPhysicalInput : BurnolPaAmbientCarrier :=
  ⟨(W.actualInput observation nontrivial half depth).1, by
    rw [W.actual_input_value observation nontrivial half depth]
    exact (P.physicalInput observation nontrivial half).property⟩

def actualResponse : BurnolL2 := (W.actualResponseInput observation nontrivial half depth).1

local notation "input" => (actualPhysicalInput observation nontrivial half depth : BurnolL2)
local notation "response" => actualResponse observation nontrivial half depth

/-- The final R equation comes from this execution's child and result. -/
theorem actual_source_equation : burnolDirectRightResolventCLM c input = next :=
  (W.actualInput observation nontrivial half depth).2.2.down

theorem actual_response_equation : fourierL2 response = input :=
  (W.actualResponseInput observation nontrivial half depth).2.2.down

theorem actual_response_price : inner ℂ (generatedK c) response = -price := by
  rw [actualResponse, W.actual_response_value observation nontrivial half depth]
  exact P.actual_source_price c

theorem actual_input_price : inner ℂ (fourierL2 (generatedK c)) input = -price := by
  rw [← actual_response_equation observation nontrivial half depth,
    fourierL2.inner_map_map, actual_response_price observation nontrivial half depth]

/-- The original physical-R consumer acts on the actual child, before reading its whole B output. -/
theorem actual_B_effect : outside next = (2 * price) • physicalOutsideColumn c := by
  have action := original_R_physical_outside_source c (actualPhysicalInput observation nontrivial half depth)
  change outside (burnolDirectRightResolventCLM c input) =
    (-2 * inner ℂ (fourierL2 (generatedK c)) input) • physicalOutsideColumn c at action
  rw [actual_source_equation observation nontrivial half depth,
    actual_input_price observation nontrivial half depth] at action
  convert action using 1
  congr 1
  ring

theorem actual_complete_update : next = (burnolEvenAmbientProjection next : BurnolL2) +
    (2 * price) • physicalOutsideColumn c := by
  have whole : outside next = next - (burnolEvenAmbientProjection next : BurnolL2) :=
    Submodule.starProjection_orthogonal_val _
  rw [actual_B_effect observation nontrivial half depth] at whole
  linear_combination (norm := module) -whole

/-- The complete original B cost is retained on the same physical input and actual R result. -/
theorem actual_native_energy : ‖input‖^2 -
    ‖input + (sourceDamping c : ℂ) • (burnolEvenAmbientProjection next : BurnolL2)‖^2 =
      4 * (sourceDamping c)^2 * ‖hPowerPhysicalCorrection (barC c)‖^2 * ‖price‖^2 := by
  have action := physical_forward_exact_loss c (actualPhysicalInput observation nontrivial half depth)
  change ‖input‖^2 - ‖input + (sourceDamping c : ℂ) •
    (burnolEvenAmbientProjection (burnolDirectRightResolventCLM c input) : BurnolL2)‖^2 =
      4 * (sourceDamping c)^2 * ‖hPowerPhysicalCorrection (barC c)‖^2 *
        ‖inner ℂ (fourierL2 (generatedK c)) input‖^2 at action
  rw [actual_source_equation observation nontrivial half depth,
    actual_input_price observation nontrivial half depth, norm_neg] at action
  exact action

theorem actual_native_energy_pos : 0 < ‖input‖^2 -
    ‖input + (sourceDamping c : ℂ) • (burnolEvenAmbientProjection next : BurnolL2)‖^2 := by
  rw [actual_native_energy observation nontrivial half depth]
  have damping := sourceDamping_pos c
  have power : 0 < ‖hPowerPhysicalCorrection (barC c)‖^2 :=
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (powerCorrection_ne_zero (barC c)))
  have price_positive : 0 < ‖price‖^2 :=
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (P.actual_native_programme_ne_zero observation nontrivial half))
  positivity

theorem actual_outside_ne_zero : outside next ≠ 0 := by
  rw [actual_B_effect observation nontrivial half depth]
  exact smul_ne_zero (mul_ne_zero two_ne_zero
    (P.actual_native_programme_ne_zero observation nontrivial half))
    (outsideColumn_ne_zero observation nontrivial half)

theorem actual_not_physical : next ∉ evenBurnolClosedFace (1 / 4 : ℝ) := by
  intro physical
  exact actual_outside_ne_zero observation nontrivial half depth
    (Submodule.starProjection_orthogonal_apply_eq_zero physical)

/-- This output property does not admit the response to a Pa or old cofinal actor. -/
theorem actual_response_not_Pa :
    ¬ ∃ physical : response ∈ evenBurnolClosedFace burnolUnscaledCommonGapRadius,
      (⟨response, physical⟩ : BurnolPaAmbientCarrier) ∈ burnolCompactCoPoissonClosedRange := by
  rw [actualResponse, W.actual_response_value observation nontrivial half depth]
  exact P.actual_forcing_response_not_Pa observation nontrivial half

end OriginalWholeDebtRJointMobiusForcedRegisteredRConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
