import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.FixedShell
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRPowerWaveDilationSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.OutsideContact
open Complex MeasureTheory Set Filter BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalKFiniteOrderRelease OriginalKFiniteOrderRelease.UnitPowerSource
open OriginalKFiniteOrderRelease.UnitPowerJordanSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open OriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
open OriginalKPairedBEulerJunctionSource OriginalKPairedBEulerJunctionSource.BandFullStockEuler
open OriginalKDirectRCofinalOutsideVolterraSource OriginalKSourceResolventReconstruction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.FixedShell
open scoped InnerProductSpace Topology
local notation "q" => (1/4 : ℝ)
local notation "D" => burnolMultiplicativeDilation
local notation "R" => burnolDirectRightResolventCLM
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "F" => fourierL2
local notation "Rq" => burnolQuarterRestriction
local notation "E" => burnolQuarterZeroExtension
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

private theorem meanZero_pair (state : M) : inner ℂ (state : Hq) (intervalConstant q) = 0 :=
  (Submodule.mem_orthogonal' _ _).mp state.property _ (Submodule.mem_span_singleton_self _)

/-- This complete finite B price keeps the actual power normalizer as well as the resonant log column. -/
def adjointColumnPrice (source action : BurnolCompletedMellinCoordinate) : ℂ :=
  -2*inner ℂ (sourceSecond source : Hq) (dividedLogColumn (barC action) 1) +
    OriginalWholeDebtRColumnForwardSource.powerAmplitude action*
      inner ℂ (sourceSecond source : Hq) (SingularCounting.powerL2 (barC action))

/-- The full source/contact adjoint is read on its actual B-power input using its two whole quarter fields. -/
theorem actual_adjoint_column_price (source action : BurnolCompletedMellinCoordinate) :
    inner ℂ (OriginalWholeDebtRAdjointContactSource.sourceField source action) (physicalOutsideColumn action) =
      adjointColumnPrice source action := by
  rw [←OriginalWholeDebtRAdjointContactSource.actual_R_cotest,
    OriginalWholeDebtRColumnForwardSource.actual_column_action]
  have inverse : OriginalWholeDebtRColumnForwardSource.forwardField action =
      F (OriginalWholeDebtRColumnForwardSource.adjointField action) := by
    apply fourierL2.injective
    rw [OriginalWholeDebtRColumnForwardSource.forwardField,fourierL2.apply_symm_apply,
      fourierL2_fourierL2,OriginalWholeDebtRColumnForwardSource.adjoint_even]
  rw [inverse,correctionRaw,inner_add_left,fourierL2.inner_map_map]
  have extension (state : Hq) (value : BurnolL2) :
      inner ℂ (E state) value = inner ℂ state (Rq value) :=
    ContinuousLinearMap.adjoint_inner_left Rq _ _
  rw [extension,extension,(OriginalWholeDebtRColumnForwardSource.actual_quarters action).2,
    (OriginalWholeDebtRColumnForwardSource.actual_quarters action).1,
    inner_smul_right,meanZero_pair,mul_zero,zero_add,inner_add_right,inner_add_right,
    inner_smul_right,inner_smul_right,inner_smul_right,meanZero_pair,mul_zero,zero_add]
  rfl

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : ℕ, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation
include nontrivial

/-- Only the preceding Unit is physical: its actual Xi top generates the entire first outside field. -/
theorem actual_unit_four_top_outside :
    O (unitPower observation half m) = (-2*e) • physicalOutsideColumn c := by
  have positive := generatedRiemannXiZeroOrder_pos observation nontrivial
  let previous : BurnolPaAmbientCarrier := ⟨unitPower observation half (m-1),
    unitPower_physical observation nontrivial half (m-1) (by omega)⟩
  have source := original_R_physical_outside_source c previous
  rw [generatedK_eq_original] at source
  have top := unitPower_fourier_top observation nontrivial half
  change inner ℂ (F (burnolCompletedMellinRieszVector c : BurnolL2)) (previous : BurnolL2) = e at top
  rw [top] at source
  have step : unitPower observation half m =
      burnolDirectRightResolvent ((c).value/2) (unitPower observation half (m-1)) := by
    have same : m = (m-1)+1 := by omega
    conv_lhs => rw [same]
    simp only [unitPower,CombSource.Division.rawIterate,pow_succ',mul_apply_eq_comp,CombSource.Division.rawAction]
    rfl
  rw [step]
  exact source

/-- The original radius-one shell is a genuine Pa source through m, so its whole outside inventory is unchanged. -/
theorem actual_unit_one_top_outside :
    O (unitOnePower c m) = (-2*e) • physicalOutsideColumn c := by
  have shell := burnolUnitTailResponse_shell c 1 (by norm_num) (by norm_num)
  have source := congrArg (fun value : BurnolL2 => ((R c)^m) value) shell
  rw [map_sub] at source
  change unitOnePower c m-unitPower observation half m =
    CombSource.Division.rawIterate observation half.down m
      (burnolActualUnitPowerShellPaState c 1 (by norm_num) (by norm_num) : BurnolL2) at source
  have physical := CombSource.Division.whole_pa_physical observation nontrivial half.down m le_rfl
    (burnolActualUnitPowerShellPaState c 1 (by norm_num) (by norm_num))
    (burnolActualUnitPowerShellPaState_mem c 1 (by norm_num) (by norm_num))
  have killed : O (CombSource.Division.rawIterate observation half.down m
      (burnolActualUnitPowerShellPaState c 1 (by norm_num) (by norm_num) : BurnolL2)) = 0 :=
    Submodule.starProjection_orthogonal_apply_eq_zero physical
  have outside := congrArg O source
  rw [map_sub,killed,actual_unit_four_top_outside observation nontrivial half] at outside
  exact sub_eq_zero.mp outside

/-- Every literal outside contact is read by the generated whole B-power column of this same Unit. -/
theorem actual_unit_one_outside_price (field : BurnolL2) :
    inner ℂ (O field) (unitOnePower c m) = -2*e*inner ℂ field (physicalOutsideColumn c) := by
  have moved := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ.inner_starProjection_left_eq_right
    field (unitOnePower c m)
  change inner ℂ (O field) (unitOnePower c m) = inner ℂ field (O (unitOnePower c m)) at moved
  rw [moved,actual_unit_one_top_outside observation nontrivial half,inner_smul_right]

/-- The complete second O contact is computed from the actual two B drives; no Unit_m physical qualification enters. -/
theorem actual_original_adjoint_outside_contact (source : BurnolCompletedMellinCoordinate) :
    inner ℂ (O (OriginalWholeDebtRAdjointContactSource.sourceField source c)) (unitOnePower c m) =
      -2*e*adjointColumnPrice source c := by
  rw [actual_unit_one_outside_price observation nontrivial half,actual_adjoint_column_price]

/-- The first O contact retains the specific original moving source against the same generated B-power column. -/
theorem actual_original_paired_outside_contact (source : BurnolCompletedMellinCoordinate) (h : ℝ) :
    inner ℂ (O (OriginalWholeDebtRPowerWaveDilationSource.pairedSource source h)) (unitOnePower c m) =
      -2*e*inner ℂ (OriginalWholeDebtRPowerWaveDilationSource.pairedSource source h) (physicalOutsideColumn c) :=
  actual_unit_one_outside_price observation nontrivial half _

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.OutsideContact
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
