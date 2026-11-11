import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UpperWaveRGapSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKAmbientPricing

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRProjectionSource
open Complex BurnolPhysicalState
open OriginalKPairedBEulerJunctionSource
open OriginalCommonInverseForcing.SourceJoint
open OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKCrossParameterRAdjointSource.PhysicalDefectSource
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open scoped InnerProductSpace

local notation "P" => burnolEvenAmbientProjection
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "R" => burnolDirectRightResolventCLM
local notation "K" => burnolCompletedMellinRieszVector
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "h" => junctionShift
local notation "u" => upperSeedFactor h
local notation "D" => BandFullStockAction.wholeDebt
local notation "C" => BandFullStockEuler.correctionRaw

def projectedDebt (c : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier :=
  P (upperSourceCorrection c h)+u • FullStock.meanDebt c h

def powerReturnPrice (c : BurnolCompletedMellinCoordinate) : ℂ :=
  inner ℂ (hPowerPhysicalCorrection c) (C c)

def fourierDebtPrice (c : BurnolCompletedMellinCoordinate) : ℂ :=
  inner ℂ (fourierL2 (OriginalKSourceResolventReconstruction.generatedK c))
    (projectedDebt c : BurnolL2)

def kernelRBoundary (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  pairedBurnolMultiplicativeDilation h (R c (K c : BurnolL2))-
    pairedMellinTranslationCharacter (star c.value) h • R c (K c : BurnolL2)

/-- The two cross-channel charges remain part of the original whole-source word. -/
def sourceField (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  R c (upperSourceWave c h)-(2*u) • (P (kernelRBoundary c) : BurnolL2)-
    (4*u*powerReturnPrice c) •
      OriginalKSourceResolventReconstruction.generatedK (barC c)-
    (2*fourierDebtPrice c) • physicalOutsideColumn c

theorem projected_debt_source (c : BurnolCompletedMellinCoordinate) :
    (projectedDebt c : BurnolL2)=D c+(2*u) • C c := by
  rw [projectedDebt,← BandFullStockAction.whole_debt_projection]
  exact BandFullStockEuler.projected_debt_raw_source c

private theorem projected_debt_read (c : BurnolCompletedMellinCoordinate) :
    P (D c)=projectedDebt c := BandFullStockAction.whole_debt_projection c

theorem outside_debt_source (c : BurnolCompletedMellinCoordinate) :
    O (D c)=(-2*u) • C c := by
  have split : O (D c)=D c-(P (D c) : BurnolL2) :=
    Submodule.starProjection_orthogonal_val (D c)
  rw [split,projected_debt_read,projected_debt_source]
  module

/-- Both actual off-diagonal R blocks are consumed before the projected debt is advanced. -/
theorem whole_debt_projection_R_square (c : BurnolCompletedMellinCoordinate) :
    (P (R c (D c)) : BurnolL2)-R c (projectedDebt c : BurnolL2)=
      (4*u*powerReturnPrice c) •
        OriginalKSourceResolventReconstruction.generatedK (barC c)+
      (2*fourierDebtPrice c) • physicalOutsideColumn c := by
  have returned := original_R_outside_physical_generatedK c (D c)
  change (P (R c (O (D c))) : BurnolL2)=_ at returned
  have outsidePrice : inner ℂ (hPowerPhysicalCorrection c) (O (D c))=
      (-2*u)*powerReturnPrice c := by
    rw [outside_debt_source,inner_smul_right]
    rfl
  rw [outsidePrice] at returned
  have leaked := original_R_physical_outside_source c (projectedDebt c)
  change O (R c (projectedDebt c : BurnolL2))=
    (-2*fourierDebtPrice c) • physicalOutsideColumn c at leaked
  have input : D c=(projectedDebt c : BurnolL2)+O (D c) := by
    rw [outside_debt_source,projected_debt_source]
    module
  have acted := congrArg (fun value : BurnolL2 => (P (R c value) : BurnolL2)) input
  simp only [map_add,Submodule.coe_add] at acted
  have split : O (R c (projectedDebt c : BurnolL2))=
    R c (projectedDebt c : BurnolL2)-
      (P (R c (projectedDebt c : BurnolL2)) : BurnolL2) :=
    Submodule.starProjection_orthogonal_val (R c (projectedDebt c : BurnolL2))
  rw [leaked] at split
  change (P (R c (O (D c))) : BurnolL2)=
    (-2*((-2*u)*powerReturnPrice c)) •
      OriginalKSourceResolventReconstruction.generatedK (barC c) at returned
  linear_combination (norm := module) acted+returned+split

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

/-- The source field is generated before its actual R target is identified. -/
theorem original_source_action :
    R c (projectedDebt c : BurnolL2)=sourceField c := by
  have square := whole_debt_projection_R_square c
  have whole := OriginalUpperWaveRGapSource.whole_debt_R_source c
  have projection := congrArg (fun value : BurnolL2 => (P value : BurnolL2)) whole
  simp only [map_add,map_sub,map_smul,Submodule.coe_add,Submodule.coe_sub,
    Submodule.coe_smul] at projection
  have wave : (P (R c (upperSourceWave c h)) : BurnolL2)=R c (upperSourceWave c h) := by
    let admitted : BurnolPaAmbientCarrier :=
      ⟨R c (upperSourceWave c h),
        OriginalUpperWaveRGapSource.original_upper_R_physical observation nontrivial half h
          junctionShift_pos.le ((le_abs_self h).trans OriginalRieszFiniteColumns.fixedShift_small)⟩
    have fixed : P (admitted : BurnolL2)=admitted :=
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
    exact congrArg (fun value : BurnolPaAmbientCarrier => (value : BurnolL2)) fixed
  rw [wave] at projection
  unfold sourceField kernelRBoundary
  simp only [map_sub,map_smul,Submodule.coe_sub,Submodule.coe_smul]
  linear_combination (norm := module) projection-square

private theorem ambient_physical_read (read : BurnolCompletedMellinCoordinate)
    (value : BurnolPaAmbientCarrier) :
    burnolAmbientCompletedMellinEvaluator read (value : BurnolL2)=
      inner ℂ (K read : BurnolL2) (value : BurnolL2) := by
  have restricted := congrArg (fun f : BurnolPaAmbientCarrier →L[ℂ] ℂ => f value)
    (burnolAmbientCompletedMellinEvaluator_restrict read)
  change burnolAmbientCompletedMellinEvaluator read (value : BurnolL2)=
    burnolCompletedMellinEvaluator read value at restricted
  exact restricted.trans (burnolCompletedMellinRieszVector_readback read value).symm

private theorem coordinate_eq {left right : BurnolCompletedMellinCoordinate}
    (same : left.value=right.value) : left=right := by
  cases left
  cases right
  cases same
  rfl

/-- The same priced debt, including meanDebt, is consumed after the complete source action. -/
theorem original_finite_price_source_action :
    burnolAmbientCompletedMellinEvaluator c (sourceField c)=
      (-(1/((c).value-(1/2 : ℂ))))*u*
        star (BandFiniteSourcePrice.finiteSourcePrice c h) := by
  have right : 1/4<((c).value/2).re := by
    rw [Complex.div_re];norm_num;linarith [(c).rightHalf]
  have below : ((c).value/2).re<1/2 := by
    rw [Complex.div_re];norm_num;linarith [(c).belowOne]
  have coordinate : burnolDivisionCompletedMellinCoordinate ((c).value/2) right below=c := by
    apply coordinate_eq
    change 2*((c).value/2)=(c).value
    ring
  have action := CombSource.Pricing.ambient_R_scalar_action ((c).value/2) right
    (projectedDebt c : BurnolL2) (projectedDebt c).property.1.1
    ((c).value/2) right below
  rw [coordinate,ambient_physical_read] at action
  have priced := BandFullStockEuler.actual_projected_debt_value c observation.mathlibZero
  change inner ℂ (K c : BurnolL2) (projectedDebt c : BurnolL2)=
    u*star (BandFiniteSourcePrice.finiteSourcePrice c h) at priced
  rw [priced] at action
  rw [← original_source_action observation nontrivial half]
  have denominator : (c).value/2+(c).value/2-(1/2 : ℂ)=(c).value-(1/2 : ℂ) := by ring
  rw [denominator] at action
  change burnolAmbientCompletedMellinEvaluator c
    (burnolDirectRightResolvent ((c).value/2) (projectedDebt c : BurnolL2))=_
  simpa only [mul_assoc] using action

end OriginalWholeDebtRProjectionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
