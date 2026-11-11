import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusReturnJordanSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKReturnJordanSourceFields

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusReturnRegisteredRConsumer
open Complex MeasureTheory BurnolPhysicalState
open OriginalKDirectRCofinalOutsideVolterraSource
open scoped InnerProductSpace
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
open private allPa_fourier_power_zero from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerSource
open private coordinate_is_division from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusReturnJordanSource
namespace S
export OriginalWholeDebtRJointMobiusReturnJordanSource
  (returnSource jet paJet feedback nextPa actual_pa_member actual_lower_Pa actual_exact_order_Pa
   actual_complete_inventory actual_feedback actual_feedback_ne_zero actual_exact_order_Pa_ne_zero
   actual_next_source_update actual_original_Pa_first_release actual_exact_order_Fourier
   actual_first_outside actual_first_outside_coefficient_ne_zero actual_first_whole_update)
end S
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation
local notation "pa" => S.paJet observation nontrivial half m
local notation "Rpow" => CombSource.Division.rawIterate observation half.down
local notation "FK" => fourierL2 (burnolCompletedMellinRieszVector c : BurnolL2)
local notation "outside" => OriginalKCombPhysicalAction.physicalRemainder

private theorem source_prefix_physical (j : Nat) (before : j ≤ m) :
    Rpow j (pa : BurnolL2) ∈ evenBurnolClosedFace (1 / 4 : ℝ) :=
  CombSource.Division.whole_pa_physical observation nontrivial half.down j before pa
    (S.actual_pa_member observation nontrivial half m)

private theorem source_prefix_FK_ne_zero : inner ℂ FK (Rpow m (pa : BurnolL2)) ≠ 0 := by
  rw [S.actual_exact_order_Fourier]
  exact mul_ne_zero (S.actual_feedback_ne_zero observation nontrivial half)
    (burnolAnalyticComplementExpectedPhysicalFourierRead_ne_zero observation nontrivial)

/-- The exact-m actor is physical, but its actual Fourier release rejects a second Pa admission. -/
private theorem source_prefix_not_Pa :
    ¬ ∃ physical : Rpow m (pa : BurnolL2) ∈ evenBurnolClosedFace (1 / 4 : ℝ),
      (⟨Rpow m (pa : BurnolL2), physical⟩ : BurnolPaAmbientCarrier) ∈
        burnolCompactCoPoissonClosedRange := by
  rintro ⟨physical, inside⟩
  have zero := allPa_fourier_power_zero observation nontrivial half
    (⟨Rpow m (pa : BurnolL2), physical⟩ : BurnolPaAmbientCarrier) inside 0
    (generatedRiemannXiZeroOrder_pos observation nontrivial)
  exact source_prefix_FK_ne_zero observation nontrivial half zero

private theorem source_first_outside_ne_zero : outside (Rpow (m + 1) (pa : BurnolL2)) ≠ 0 := by
  rw [S.actual_first_outside]
  apply smul_ne_zero (S.actual_first_outside_coefficient_ne_zero observation nontrivial half)
  intro zero
  have reflected := congrArg fourierL2 zero
  change fourierL2 (fourierL2.symm
    (hPowerPhysicalCorrection (OriginalPrimitiveRankBalance.conjugateCoordinate c))) = fourierL2 0 at reflected
  rw [fourierL2.apply_symm_apply, map_zero] at reflected
  exact OriginalKCrossParameterRAdjointSource.UnweightedCayleySource.powerCorrection_ne_zero _ reflected

private theorem source_first_not_physical :
    Rpow (m + 1) (pa : BurnolL2) ∉ evenBurnolClosedFace (1 / 4 : ℝ) := by
  intro physical
  exact source_first_outside_ne_zero observation nontrivial half
    (Submodule.starProjection_orthogonal_apply_eq_zero physical)

namespace W
export OriginalKReturnJordanSourceWriteback
  (actualValue actualPaInput actualPrefixInput actual_pa_input_value actual_pa_value actual_prefix_value
   actual_next_value actual_prefix_pa actual_value_runtime borrowedResponseInput borrowedRResult
   actual_borrowed_response actual_borrowed_result actualJetPrefix actual_jet_prefix_value
   actualDifferenceInput actual_difference_value)
end W
variable (depth : Nat)
private abbrev actualJetAt := (W.actualPaInput observation nontrivial half depth).1
private abbrev actualPrefixAt := (W.actualPrefixInput observation nontrivial half depth).1
local notation "actualJet" => actualJetAt observation nontrivial half depth
local notation "prefix" => actualPrefixAt observation nontrivial half depth
local notation "next" => W.actualValue observation nontrivial half depth 1

theorem actual_borrowed_R_field : W.borrowedRResult observation nontrivial half depth =
    OriginalKJointMobiusSourceWriteback.actualValue observation nontrivial half depth 1 := by
  unfold W.borrowedRResult runtimeJointMobiusRCalculationResultAt
  exact (OriginalKJointMobiusSourceWriteback.actual_value_runtime observation nontrivial half depth 1).symm

theorem actual_source_faces :
    OriginalKCrossParameterRAdjointSource.SharedOutsideSource.jQuarterAmplitude c •
        (W.actualDifferenceInput observation nontrivial half depth).1 -
      hQuarterAmplitude c • fourierL2 (W.actualDifferenceInput observation nontrivial half depth).1 =
        (W.actualJetPrefix observation nontrivial half depth 0 (Nat.zero_le m)).1 := by
  change OriginalKReturnJordanSourceCalculation.sourceAction c
    (W.actualDifferenceInput observation nontrivial half depth).1 = _
  exact (W.actualDifferenceInput observation nontrivial half depth).2.2.down

/-- The K field is an output read of this actual difference child. -/
theorem actual_difference_kernel : (W.actualDifferenceInput observation nontrivial half depth).1 =
    OriginalWholeDebtRJointMobiusReturnAction.returnAmplitude observation nontrivial half •
      (burnolCompletedMellinRieszVector c : BurnolL2) := by
  rw [W.actual_difference_value]
  change (OriginalWholeDebtRJointMobiusReturnAction.returned observation nontrivial half : BurnolL2) -
    OriginalWholeDebtRJointMobiusUnitSource.response c = _
  rw [OriginalWholeDebtRJointMobiusReturnAction.actual_complete_return]
  module

theorem actual_difference_ne_zero : (W.actualDifferenceInput observation nontrivial half depth).1 ≠ 0 := by
  rw [W.actual_difference_value]
  intro vanished
  apply OriginalWholeDebtRJointMobiusReturnAction.actual_return_not_fixed observation nontrivial half
  exact sub_eq_zero.mp vanished

theorem actual_jet_step (index : Nat) (before : index + 1 ≤ m) :
    (W.actualJetPrefix observation nontrivial half depth (index + 1) before).1 =
      (burnolDirectRightResolventCLM c).adjoint
        (W.actualJetPrefix observation nontrivial half depth index
          (Nat.le_trans (Nat.le_succ index) before)).1 := by
  rw [W.actual_jet_prefix_value, W.actual_jet_prefix_value]
  exact OriginalWholeDebtRJointMobiusReturnJordanSource.actual_jet_next observation nontrivial half index

theorem actual_lower_Pa (index : Nat) (before : index < m) :
    OriginalKCombCofinalPaAction.E
      (W.actualJetPrefix observation nontrivial half depth index before.le).1 = 0 := by
  rw [W.actual_jet_prefix_value]
  exact S.actual_lower_Pa observation nontrivial half index before

/-- This projection equation is taken from the executed Pa node and its actual adjoint-jet child. -/
theorem actual_Pa_equation : OriginalKReturnJordanSourceCalculation.paAction actualJet =
    W.actualValue observation nontrivial half depth 0 :=
  (W.actualPaInput observation nontrivial half depth).2.2.down

theorem actual_jet_inventory : actualJet =
    OriginalWholeDebtRJointMobiusReturnAction.returnAmplitude observation nontrivial half •
      ((OriginalKFiniteOrderRelease.UnitPowerSource.paPowerField observation half : BurnolL2) +
        OriginalKFiniteOrderRelease.UnitPowerJordanSource.sourceQ observation half +
        OriginalKFiniteOrderRelease.UnitPowerJordanSource.sourceOutside c m) := by
  exact (W.actual_pa_input_value observation nontrivial half depth).trans
    (S.actual_complete_inventory observation nontrivial half)

def actualPa : BurnolPaAmbientCarrier :=
  OriginalKCombCofinalPaAction.E (W.actualPaInput observation nontrivial half depth).1

theorem actual_Pa_value : (actualPa observation nontrivial half depth : BurnolL2) =
    W.actualValue observation nontrivial half depth 0 :=
  actual_Pa_equation observation nontrivial half depth

theorem actual_Pa_source : actualPa observation nontrivial half depth = pa := by
  rw [actualPa, W.actual_pa_input_value]
  rfl

theorem actual_Pa_member : actualPa observation nontrivial half depth ∈ burnolCompactCoPoissonClosedRange :=
  Submodule.starProjection_apply_mem _ _

theorem actual_Pa_ne_zero : W.actualValue observation nontrivial half depth 0 ≠ 0 := by
  intro vanished
  apply S.actual_exact_order_Pa_ne_zero observation nontrivial half
  apply Subtype.ext
  rw [← W.actual_pa_value]
  exact vanished

def actualCorrectedPa : BurnolPaAmbientCarrier := burnolPaSourceCorrection c
  ⟨actualPa observation nontrivial half depth, actual_Pa_member observation nontrivial half depth⟩

theorem actual_corrected_Pa_member :
    actualCorrectedPa observation nontrivial half depth ∈ burnolCompactCoPoissonClosedRange :=
  burnolPaSourceCorrection_mem c _

local notation "feedback" => burnolPaResolventSourceCoefficient c (actualPa observation nontrivial half depth)

theorem actual_feedback : feedback = S.feedback observation nontrivial half := by
  rw [actual_Pa_source]
  rfl

theorem actual_feedback_ne_zero : feedback ≠ 0 := by
  rw [actual_feedback]
  exact S.actual_feedback_ne_zero observation nontrivial half

theorem actual_prefix_actor : prefix = Rpow m (actualPa observation nontrivial half depth : BurnolL2) := by
  rw [actual_Pa_source]
  exact W.actual_prefix_value observation nontrivial half depth

theorem actual_next_actor : next = Rpow (m + 1) (actualPa observation nontrivial half depth : BurnolL2) := by
  rw [actual_Pa_source]
  exact W.actual_next_value observation nontrivial half depth

/-- This last R equation is the actual executed node, before any physical identification. -/
theorem actual_source_equation : burnolDirectRightResolventCLM c prefix = next :=
  (W.actualPrefixInput observation nontrivial half depth).2.2.down

/-- The forward actor keeps its own complete corrected-Pa and whole-unit vector split. -/
theorem actual_prefix_inventory : prefix =
    Rpow (m - 1) (actualCorrectedPa observation nontrivial half depth : BurnolL2) +
      feedback • OriginalKFiniteOrderRelease.UnitPowerSource.unitPower observation half (m - 1) := by
  have split := OriginalKFiniteOrderRelease.UnitPowerSource.actual_Pa_power_split observation half
    (actualPa observation nontrivial half depth) (actual_Pa_member observation nontrivial half depth) (m - 1)
  rw [← coordinate_is_division observation nontrivial half] at split
  have positive := generatedRiemannXiZeroOrder_pos observation nontrivial
  rw [show m - 1 + 1 = m by omega] at split
  exact (actual_prefix_actor observation nontrivial half depth).trans split

theorem actual_next_inventory : next =
    Rpow m (actualCorrectedPa observation nontrivial half depth : BurnolL2) +
      feedback • OriginalKFiniteOrderRelease.UnitPowerSource.unitPower observation half m := by
  have split := OriginalKFiniteOrderRelease.UnitPowerSource.actual_Pa_power_split observation half
    (actualPa observation nontrivial half depth) (actual_Pa_member observation nontrivial half depth) m
  rw [← coordinate_is_division observation nontrivial half] at split
  exact (actual_next_actor observation nontrivial half depth).trans split

theorem actual_original_Pa_first_release :
    (∀ k : Nat, k < m → inner ℂ (OriginalWholeDebtRAdjointContactSource.sourceEffect c c)
      (Rpow k (actualPa observation nontrivial half depth : BurnolL2)) = 0) ∧
    inner ℂ (OriginalWholeDebtRAdjointContactSource.sourceEffect c c) prefix =
      star (OriginalWholeDebtRAdjointContactSource.sigma c c) * feedback *
        inner ℂ (OriginalKPairedBEulerJunctionSource.BandFullStockEuler.correctionRaw c)
          (OriginalKFiniteOrderRelease.UnitPowerSource.unitPower observation half m) := by
  have released := OriginalWholeDebtRAdjointContactSource.original_Pa_first_release observation nontrivial half
    (actualPa observation nontrivial half depth) (actual_Pa_member observation nontrivial half depth)
  exact ⟨released.1, by rw [actual_prefix_actor]; exact released.2⟩

theorem actual_exact_order_Fourier : inner ℂ FK prefix = feedback * e := by
  unfold actualPrefixAt
  rw [W.actual_prefix_value, actual_feedback]
  exact S.actual_exact_order_Fourier observation nontrivial half

theorem actual_physical_prefix (j : Nat) (before : j ≤ m) :
    Rpow j (actualPa observation nontrivial half depth : BurnolL2) ∈ evenBurnolClosedFace (1 / 4 : ℝ) := by
  rw [actual_Pa_source]
  exact source_prefix_physical observation nontrivial half j before

theorem actual_prefix_physical : prefix ∈ evenBurnolClosedFace (1 / 4 : ℝ) := by
  rw [actual_prefix_actor]
  exact actual_physical_prefix observation nontrivial half depth m le_rfl

theorem actual_prefix_not_Pa :
    ¬ ∃ physical : prefix ∈ evenBurnolClosedFace (1 / 4 : ℝ),
      (⟨prefix, physical⟩ : BurnolPaAmbientCarrier) ∈ burnolCompactCoPoissonClosedRange := by
  rintro ⟨physical, inside⟩
  have zero := allPa_fourier_power_zero observation nontrivial half
    (⟨prefix, physical⟩ : BurnolPaAmbientCarrier) inside 0
    (generatedRiemannXiZeroOrder_pos observation nontrivial)
  have nonzero : inner ℂ FK prefix ≠ 0 := by
    rw [actual_exact_order_Fourier]
    exact mul_ne_zero (actual_feedback_ne_zero observation nontrivial half depth)
      (burnolAnalyticComplementExpectedPhysicalFourierRead_ne_zero observation nontrivial)
  exact nonzero zero

theorem actual_outside_effect : outside next = (-2 * feedback * e) •
    OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource.physicalOutsideColumn c := by
  rw [W.actual_next_value, actual_feedback]
  exact S.actual_first_outside observation nontrivial half

theorem actual_complete_update : next = (burnolEvenAmbientProjection next : BurnolL2) +
    (-2 * feedback * e) • OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource.physicalOutsideColumn c := by
  rw [W.actual_next_value, actual_feedback]
  exact S.actual_first_whole_update observation nontrivial half

theorem actual_outside_ne_zero : outside next ≠ 0 := by
  rw [W.actual_next_value]
  exact source_first_outside_ne_zero observation nontrivial half

theorem actual_not_physical : next ∉ evenBurnolClosedFace (1 / 4 : ℝ) := by
  rw [W.actual_next_value]
  exact source_first_not_physical observation nontrivial half

end OriginalWholeDebtRJointMobiusReturnRegisteredRConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalWholeDebtRJointMobiusReturnRegisteredRConsumer"
