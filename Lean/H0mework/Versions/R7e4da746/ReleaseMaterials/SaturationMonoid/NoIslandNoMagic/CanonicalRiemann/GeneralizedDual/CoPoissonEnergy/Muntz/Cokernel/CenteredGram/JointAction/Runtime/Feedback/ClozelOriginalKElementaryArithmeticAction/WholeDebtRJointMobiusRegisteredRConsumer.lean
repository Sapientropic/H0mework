import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKJointMobiusSourceFields
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKJointMobiusRSourceCalculation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusStrictSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusRPrefixSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusRPrefixKConsumer

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusRegisteredRConsumer
open Complex MeasureTheory BurnolPhysicalState OriginalKDirectRCofinalOutsideVolterraSource
open scoped InnerProductSpace
namespace W
export OriginalKJointMobiusSourceWriteback
  (actualValue bound_code_value actualRInput actualRResponseInput actual_R_input_value actual_R_response_value)
end W
namespace R
export OriginalWholeDebtRJointMobiusRActionSource
  (sourceInput sourceNext actual_source_effect actual_complete_update actual_programme_energy actual_effect_zero_iff)
end R
namespace S
export OriginalWholeDebtRJointMobiusStrictSource (actual_programme_ne_zero actual_physical_strict_loss)
end S
namespace Energy
export OriginalKCrossParameterRAdjointSource.CayleyEnergySource (sourceDamping)
end Energy
namespace Prefix
export OriginalWholeDebtRJointMobiusRPrefixSource
  (nextRaw nextCoefficient actual_zero_end_from_Tate_source actual_next_inverse_source)
end Prefix
namespace Price
export OriginalWholeDebtRJointMobiusRPrefixKConsumer
  (actual_K_prefix_integrable actual_K_adjoint_consumer actual_FK_adjoint_consumer)
end Price
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "programme" => OriginalNextEndpointProgramme.programmePrice c (Real.log stageZeroSonineQ)
local notation "outside" => OriginalKCombPhysicalAction.physicalRemainder
local notation "column" => OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource.physicalOutsideColumn c
local notation "point" => Sigma.fst (W.actualRInput observation nontrivial half depth)
local notation "next" => W.actualValue observation nontrivial half depth 1

theorem actual_input : point = (R.sourceInput observation nontrivial half : BurnolL2) :=
  W.actual_R_input_value observation nontrivial half depth

theorem actual_field : next = R.sourceNext observation nontrivial half := by
  rw [W.actualValue, W.bound_code_value]
  exact OriginalKJointMobiusRSourceCalculation.actual_code_field observation nontrivial half

/-- This action equation comes directly from the same executed Trace and its actual child. -/
theorem actual_source_equation : burnolDirectRightResolventCLM c point = next :=
  (W.actualRInput observation nontrivial half depth).2.2.down

theorem actual_outside_effect : outside next = (2 * programme) • column := by
  rw [actual_field]
  exact R.actual_source_effect observation nontrivial half

theorem actual_complete_update : next =
    (burnolEvenAmbientProjection next : BurnolL2) + (2 * programme) • column := by
  rw [actual_field]
  exact R.actual_complete_update observation nontrivial half

theorem actual_programme_energy :
    ‖point‖ ^ 2 -
      ‖point + (Energy.sourceDamping c : ℂ) • (burnolEvenAmbientProjection next : BurnolL2)‖ ^ 2 =
      4 * Energy.sourceDamping c ^ 2 *
        ‖hPowerPhysicalCorrection (OriginalPrimitiveRankBalance.conjugateCoordinate c)‖ ^ 2 * ‖programme‖ ^ 2 := by
  rw [actual_input, actual_field]
  exact R.actual_programme_energy observation nontrivial half

theorem actual_effect_zero_iff : outside next = 0 ↔ programme = 0 := by
  rw [actual_field]
  exact R.actual_effect_zero_iff observation nontrivial half

theorem actual_effect_ne_zero : outside next ≠ 0 := by
  intro zero
  exact S.actual_programme_ne_zero observation nontrivial half
    ((actual_effect_zero_iff observation nontrivial half depth).mp zero)

theorem actual_strict_loss :
    ‖point + (Energy.sourceDamping c : ℂ) • (burnolEvenAmbientProjection next : BurnolL2)‖ ^ 2 <
      ‖point‖ ^ 2 := by
  rw [actual_input, actual_field]
  exact S.actual_physical_strict_loss observation nontrivial half

theorem actual_raw : (next : ℝ → ℂ) =ᵐ[volume] Prefix.nextRaw observation nontrivial half := by
  rw [actual_field]
  exact OriginalWholeDebtRJointMobiusRPrefixSource.actual_next_raw observation nontrivial half

theorem actual_position_restriction :
    burnolQuarterRestriction next =
      Prefix.nextCoefficient observation nontrivial half • intervalConstant (1 / 4 : ℝ) := by
  rw [actual_field]
  exact OriginalWholeDebtRJointMobiusRPrefixSource.actual_next_restriction observation nontrivial half

theorem actual_positionGap : next ∈ locallyConstantFace (1 / 4 : ℝ) := by
  rw [actual_field]
  exact OriginalWholeDebtRJointMobiusRPrefixSource.actual_next_positionGap observation nontrivial half

theorem actual_position_mean :
    burnolAmbientGapCoefficient (1 / 4 : ℝ) next = Prefix.nextCoefficient observation nontrivial half := by
  rw [actual_field]
  exact OriginalWholeDebtRJointMobiusRPrefixSource.actual_next_mean observation nontrivial half

theorem actual_physical_position_update :
    burnolQuarterRestriction (burnolEvenAmbientProjection next : BurnolL2) =
      Prefix.nextCoefficient observation nontrivial half • intervalConstant (1 / 4 : ℝ) -
        (2 * programme) • burnolQuarterRestriction column := by
  rw [actual_field]
  exact OriginalWholeDebtRJointMobiusRPrefixSource.actual_physical_next_position_update observation nontrivial half

theorem actual_K_prefix_price :
    inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) next =
      ∫ x : ℝ, inner ℂ ((burnolCompletedMellinRieszVector c : BurnolL2) x)
        (Prefix.nextRaw observation nontrivial half x) := by
  rw [actual_field]
  exact OriginalWholeDebtRJointMobiusRPrefixKConsumer.actual_K_prefix_price observation nontrivial half

theorem actual_physical_K_prefix_price :
    inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) (burnolEvenAmbientProjection next : BurnolL2) =
      ∫ x : ℝ, inner ℂ ((burnolCompletedMellinRieszVector c : BurnolL2) x)
        (Prefix.nextRaw observation nontrivial half x) := by
  rw [actual_field]
  exact OriginalWholeDebtRJointMobiusRPrefixKConsumer.actual_physical_K_prefix_price observation nontrivial half

theorem actual_not_physical : next ∉ evenBurnolClosedFace (1 / 4 : ℝ) := by
  rw [actual_field]
  exact OriginalWholeDebtRJointMobiusRPrefixKConsumer.actual_next_not_physical observation nontrivial half

end OriginalWholeDebtRJointMobiusRegisteredRConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
