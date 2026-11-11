import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusReturnAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRAdjointContactSource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusReturnJordanSource
open Complex MeasureTheory BurnolPhysicalState
open OriginalKCrossParameterRAdjointSource.SharedOutsideSource
open OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKFiniteOrderRelease
open scoped InnerProductSpace
open private coordinate_eq from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusUnitSource
open private paCoefficientSource_mem from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.PaAdjointSource
open private allPa_fourier_power_zero power_succ_left from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerSource
namespace PA
export OriginalKCombCofinalPaAction (E Q)
end PA
namespace J
export UnitPowerJordanSource (sourceStep sourceField sourceField_actual sourceQ sourceOutside source_full_inventory)
end J
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "coord" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "u" => OriginalWholeDebtRJointMobiusUnitSource.response coord
local notation "eta" => OriginalWholeDebtRJointMobiusReturnAction.returnAmplitude observation nontrivial half
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation
local notation "K" => (burnolCompletedMellinRieszVector coord : BurnolL2)
local notation "FK" => fourierL2 K
local notation "Rpow" => CombSource.Division.rawIterate observation half.down

private theorem coordinate_is_division : coord = burnolDivisionZeroCompletedMellinCoordinate observation half.down := by
  apply coordinate_eq
  rfl

/-- Constructor: only the actual source return and its same-occurrence Fourier face are read. -/
def returnDifference : BurnolL2 := (OriginalWholeDebtRJointMobiusReturnAction.returned observation nontrivial half : BurnolL2) - u

def returnSource : BurnolL2 :=
  jQuarterAmplitude coord • returnDifference observation nontrivial half -
    hQuarterAmplitude coord • fourierL2 (returnDifference observation nontrivial half)

/-- Each step executes the original outward source operation, with no supplied jet or endpoint. -/
def jet : Nat → BurnolL2
  | 0 => returnSource observation nontrivial half
  | j+1 => J.sourceStep coord (jet j)

def paJet (j : Nat) : BurnolPaAmbientCarrier := PA.E (jet observation nontrivial half j)

/-- The rank-one K identity is an output of the complete original source return. -/
theorem actual_return_source : returnSource observation nontrivial half = eta • sourceKernelCombo coord := by
  have difference : returnDifference observation nontrivial half = eta • K := by
    rw [returnDifference, OriginalWholeDebtRJointMobiusReturnAction.actual_complete_return]
    module
  rw [returnSource, difference, map_smul, sourceKernelCombo_actual]
  module

theorem actual_jet (j : Nat) : jet observation nontrivial half j = eta • J.sourceField coord j := by
  induction j with
  | zero => exact actual_return_source observation nontrivial half
  | succ j previous =>
    rw [jet, previous, map_smul]
    rfl

/-- Every jet retains its actual original R adjoint action on the return-generated source. -/
theorem actual_jet_action (j : Nat) : jet observation nontrivial half j =
    ((burnolDirectRightResolventCLM coord)^j).adjoint (returnSource observation nontrivial half) := by
  rw [actual_jet, J.sourceField_actual, actual_return_source, map_smul]

theorem actual_jet_next (j : Nat) : jet observation nontrivial half (j+1) =
    (burnolDirectRightResolventCLM coord).adjoint (jet observation nontrivial half j) :=
  (UnitPowerJordanSource.sourceStep_actual coord _).symm

theorem actual_pa_member (j : Nat) : paJet observation nontrivial half j ∈ burnolCompactCoPoissonClosedRange :=
  Submodule.starProjection_apply_mem _ _

theorem actual_lower_Pa (j : Nat) (before : j < m) : paJet observation nontrivial half j = 0 := by
  have paid := UnitPowerSource.actual_adjoint_lower_Pa_zero observation nontrivial half j before
  rw [← coordinate_is_division observation nontrivial half] at paid
  rw [paJet, actual_jet, J.sourceField_actual, map_smul, paid, smul_zero]

private theorem native_top : J.sourceField coord m = UnitPowerSource.fulladjointPowerZ observation half :=
  UnitPowerJordanSource.actual_sourceField observation half

theorem actual_exact_order_Pa : paJet observation nontrivial half m = eta • UnitPowerSource.paPowerField observation half := by
  rw [paJet, actual_jet, native_top, map_smul,
    UnitPowerSource.actual_adjoint_power_Pa_source observation nontrivial half]

/-- The exact-m full carrier retains the original Pa, complete Q and every original outside/log column. -/
theorem actual_complete_inventory : jet observation nontrivial half m =
    eta • ((UnitPowerSource.paPowerField observation half : BurnolL2) +
      J.sourceQ observation half + J.sourceOutside coord m) := by
  rw [actual_jet, native_top, J.source_full_inventory, coordinate_is_division]

def feedback : ℂ := burnolPaResolventSourceCoefficient coord (paJet observation nontrivial half m)

/-- The actual Pa coefficient comes from the generated covector's norm, not a terminal premise. -/
theorem actual_feedback : feedback observation nontrivial half = eta * UnitPowerSource.paPowerCoefficient observation half *
    inner ℂ (paCoefficientSource coord) (paCoefficientSource coord) := by
  rw [feedback, actual_exact_order_Pa, map_smul, UnitPowerSource.paPowerField, map_smul,
    ← coordinate_is_division observation nontrivial half]
  rw [← paCoefficientSource_read coord (paCoefficientSource coord) (paCoefficientSource_mem coord)]
  simp only [smul_eq_mul]
  ring

theorem actual_feedback_ne_zero : feedback observation nontrivial half ≠ 0 := by
  rw [actual_feedback]
  exact mul_ne_zero (mul_ne_zero
    (OriginalWholeDebtRJointMobiusReturnAction.actual_return_amplitude_ne_zero observation nontrivial half)
    (UnitPowerSource.paPowerCoefficient_ne_zero observation nontrivial half))
    (inner_self_ne_zero.mpr (UnitPowerSource.actual_pa_covector_ne_zero observation nontrivial half))

theorem actual_exact_order_Pa_ne_zero : paJet observation nontrivial half m ≠ 0 := by
  intro vanished
  apply actual_feedback_ne_zero observation nontrivial half
  rw [feedback, vanished, map_zero]

def nextPa : BurnolPaAmbientCarrier := burnolPaSourceCorrection coord
  ⟨paJet observation nontrivial half m, actual_pa_member observation nontrivial half m⟩

def actualNext : BurnolL2 := burnolDirectRightResolventCLM coord (paJet observation nontrivial half m : BurnolL2)

theorem actual_next_Pa_member : nextPa observation nontrivial half ∈ burnolCompactCoPoissonClosedRange :=
  burnolPaSourceCorrection_mem coord _

/-- The new exact-order Pa source generates its own literal original R update and true whole-unit foot. -/
theorem actual_next_source_update : actualNext observation nontrivial half =
    (nextPa observation nontrivial half : BurnolL2) + feedback observation nontrivial half • burnolUnitTailResponse coord 4 := by
  change burnolDirectRightResolvent ((coord).value/2) (paJet observation nontrivial half m : BurnolL2) =
    (burnolDirectRightResolvent ((coord).value/2) (paJet observation nontrivial half m : BurnolL2) -
      feedback observation nontrivial half • burnolUnitTailResponse coord 4) + _
  abel

/-- The original independent Pa consumer now consumes the source-generated first return, not a borrowed cofinal delta. -/
theorem actual_original_Pa_first_release :
    (∀ k : Nat, k < m → inner ℂ (OriginalWholeDebtRAdjointContactSource.sourceEffect coord coord)
      (Rpow k (paJet observation nontrivial half m : BurnolL2)) = 0) ∧
    inner ℂ (OriginalWholeDebtRAdjointContactSource.sourceEffect coord coord)
      (Rpow m (paJet observation nontrivial half m : BurnolL2)) =
        star (OriginalWholeDebtRAdjointContactSource.sigma coord coord) * feedback observation nontrivial half *
          inner ℂ (OriginalKPairedBEulerJunctionSource.BandFullStockEuler.correctionRaw coord)
            (UnitPowerSource.unitPower observation half m) :=
  OriginalWholeDebtRAdjointContactSource.original_Pa_first_release observation nontrivial half
    (paJet observation nontrivial half m) (actual_pa_member observation nontrivial half m)

/-- The same Pa first-return input has the original source-calculated exact-m Fourier release. -/
theorem actual_exact_order_Fourier : inner ℂ FK (Rpow m (paJet observation nontrivial half m : BurnolL2)) =
    feedback observation nontrivial half * e := by
  have positive := generatedRiemannXiZeroOrder_pos observation nontrivial
  have native := UnitPowerSource.actual_Pa_power_split observation half
    (paJet observation nontrivial half m) (actual_pa_member observation nontrivial half m) (m-1)
  rw [← coordinate_is_division observation nontrivial half] at native
  have split := congrArg (inner ℂ FK) native
  have lower := allPa_fourier_power_zero observation nontrivial half _
    (actual_next_Pa_member observation nontrivial half) (m-1) (by omega)
  rw [← coordinate_is_division observation nontrivial half] at lower
  unfold nextPa at lower
  have top := UnitPowerSource.unitPower_fourier_top observation nontrivial half
  rw [← coordinate_is_division observation nontrivial half] at top
  rw [show m-1+1=m by omega, inner_add_right, inner_smul_right, lower, top, zero_add] at split
  exact split

/-- At m+1 the actual original R action writes its complete outside column with the generated nonzero coefficient. -/
theorem actual_first_outside : OriginalKCombPhysicalAction.physicalRemainder
    (Rpow (m+1) (paJet observation nontrivial half m : BurnolL2)) =
      (-2 * feedback observation nontrivial half * e) •
        OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource.physicalOutsideColumn coord := by
  let input : BurnolPaAmbientCarrier := ⟨Rpow m (paJet observation nontrivial half m : BurnolL2),
    CombSource.Division.whole_pa_physical observation nontrivial half.down m le_rfl
      (paJet observation nontrivial half m) (actual_pa_member observation nontrivial half m)⟩
  have source := OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource.original_R_physical_outside_source coord input
  rw [OriginalKSourceResolventReconstruction.generatedK_eq_original] at source
  have read : inner ℂ FK (input : BurnolL2) = feedback observation nontrivial half * e :=
    actual_exact_order_Fourier observation nontrivial half
  rw [read] at source
  have step := power_succ_left observation half m (paJet observation nontrivial half m : BurnolL2)
  change Rpow (m+1) (paJet observation nontrivial half m : BurnolL2) =
    burnolDirectRightResolventCLM coord (input : BurnolL2) at step
  rw [step]
  exact source.trans (by congr 1; ring)

theorem actual_first_outside_coefficient_ne_zero : -2 * feedback observation nontrivial half * e ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) (actual_feedback_ne_zero observation nontrivial half))
    (burnolAnalyticComplementExpectedPhysicalFourierRead_ne_zero observation nontrivial)

/-- The terminal source update keeps both its actual physical projection and the full original outside field. -/
theorem actual_first_whole_update : Rpow (m+1) (paJet observation nontrivial half m : BurnolL2) =
    (burnolEvenAmbientProjection (Rpow (m+1) (paJet observation nontrivial half m : BurnolL2)) : BurnolL2) +
      (-2 * feedback observation nontrivial half * e) •
        OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource.physicalOutsideColumn coord := by
  have whole : OriginalKCombPhysicalAction.physicalRemainder
      (Rpow (m+1) (paJet observation nontrivial half m : BurnolL2)) =
        Rpow (m+1) (paJet observation nontrivial half m : BurnolL2) -
          (burnolEvenAmbientProjection (Rpow (m+1) (paJet observation nontrivial half m : BurnolL2)) : BurnolL2) :=
    Submodule.starProjection_orthogonal_val _
  rw [actual_first_outside] at whole
  linear_combination (norm := module) -whole

end OriginalWholeDebtRJointMobiusReturnJordanSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
