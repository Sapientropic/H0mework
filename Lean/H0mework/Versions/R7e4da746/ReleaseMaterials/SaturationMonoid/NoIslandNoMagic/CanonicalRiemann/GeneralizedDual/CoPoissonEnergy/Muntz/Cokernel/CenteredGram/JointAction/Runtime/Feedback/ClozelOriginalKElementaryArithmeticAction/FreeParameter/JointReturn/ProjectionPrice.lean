import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Cotest
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.LowerPrice
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.MeanCancellation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.JointReturn.FullJet
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.ProjectionPrice
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.FreeParameter.Riesz OriginalKElementaryArithmeticAction.FreeParameter.UnitSplice OriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer
open OriginalKElementaryArithmeticAction.FreeParameter.RadiusConsumer OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.CrossContact OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.CrossJet
open OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.LowerPrice OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.ConstantContact
open OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Consumer
open OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.FullJet OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.UnitJet
open OriginalUnitMellinSource.Band OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Cotest
open scoped Topology InnerProductSpace BigOperators
open private original_inverse_pair even_part_fixed two_clock_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Cotest
open private coordinate_eq from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.OriginalOrder
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "K" => burnolCompletedMellinRieszVector
local notation "D" => burnolMultiplicativeDilation
local notation "F" => fourierL2
local notation "Rq" => burnolQuarterRestriction
local notation "Eq" => burnolQuarterZeroExtension
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "b" => burnolRieszSingleFourierSource
local notation "P0" => Constructor.zeroMean
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "phase" s => fullMellinTranslationCharacter s (Real.log 16)

/-- The two block contacts are the actual source correction of the original elementary kernel. -/
theorem actual_B_projection_price (c d : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) :
    inner ℂ (twoClockCorrection c h)
        (burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula d))=
      inner ℂ (twoClockSource c h) (gapState d-(K d:BurnolL2)) := by
  have position : P0 (Rq (twoClockSource c h))=P0 (Rq (movedTest c h)) := by
    have source:=actual_two_clock_position c h nonnegative
    rw [burnolAmbientMeanZeroPosition,even_part_fixed _ (two_clock_even c h)] at source
    exact source
  have fourier : P0 (Rq (F (twoClockSource c h)))=P0 (Rq (fourierTest c h)) := by
    have source:=actual_two_clock_fourier c h nonnegative
    rw [burnolAmbientMeanZeroFourier,even_part_fixed _ (two_clock_even c h)] at source
    exact source
  have even : reflectL2 (Eq (b d:Hq))=Eq (b d:Hq) := by
    change reflectL2 (burnolRadiusZeroExtension q (b d:Hq))=_
    rw [burnolRadiusZeroExtension_reflect,burnolRieszSingleFourierSource_reflection_fixed]
    rfl
  have unitary:=fourierL2.inner_map_map (twoClockSource c h) (F (Eq (b d:Hq)))
  rw [fourierL2_fourierL2,even] at unitary
  have innerProject (x : Hq) (y : M) : inner ℂ x (y:Hq)=inner ℂ (P0 x) y :=
    (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right y x).symm
  rw [gapState_eq_kernel_add_correction]
  have difference : (K d:BurnolL2)+sourceCorrection d-(K d:BurnolL2)=sourceCorrection d := by module
  rw [difference,sourceCorrection,inner_sub_right,←unitary,
    show Eq=burnolQuarterRestriction.adjoint from rfl,
    ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right,
    innerProject,innerProject,position,fourier]
  rw [←original_inverse_pair,actual_two_clock_correction_source c h nonnegative,
    jointCotest,inner_sub_left,
    meanZero_fourier_pairing_of_reflection _ _ (burnolRieszSingleFourierSource_reflection_fixed d)]

private theorem lower_zero_price (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (bound : q*Real.exp h<2*q) :
    inner ℂ (radiusTest c h) (burnolUnitTailResponse (barC c) 4)=
      bandMean (barC c) 0*fullMass c h+fullLogBand c h 0 := by
  let observation:=burnolPaZeroObservation c zero
  let nontrivial:=burnolPaZeroObservation_nontrivial c zero
  let half : OriginalKCombCalculation.Half observation := ⟨c.rightHalf⟩
  have positive:=generatedRiemannXiZeroOrder_pos observation nontrivial
  have source:=actual_original_lower_price observation nontrivial half 0 positive h nonnegative bound
  have same : burnolDivisionZeroCompletedMellinCoordinate observation half.down=c := by
    apply coordinate_eq
    rfl
  rw [same] at source
  simpa only [pow_zero,one_apply_eq_self,bandCoefficient,Nat.factorial_zero,Nat.cast_one,
    div_one,one_mul] using source

/-- The original zero's order is positive; its zeroth Unit read keeps the complete finite band. -/
theorem actual_zero_unit_price (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (bound : q*Real.exp h<2*q) :
    -inner ℂ (movedTest c h) (freeUnit (star c.value) ConstantDual.value)=
      -(1/4:ℂ)*constantCoefficient (star c.value)*inverseBandPrice c h+
        (1/2:ℂ)*(phase (star c.value))⁻¹*fullLogBand c h 0 := by
  have unit:=actual_free_unit_jet c (barC c) h 0
  simp only [iteratedDeriv_zero,Nat.zero_add,Finset.range_one,Finset.sum_singleton,
    Nat.choose_self,Nat.cast_one,Nat.sub_self,pow_zero,one_mul,Nat.factorial_zero,div_one,
    unitJet,one_apply_eq_self] at unit
  change inner ℂ (movedTest c h) (freeUnit (star c.value) ConstantDual.value)=
    constantCoefficient (star c.value)*inner ℂ (movedTest c h) ConstantDual.value-
    (1/2:ℂ)*(phase (star c.value))⁻¹*inner ℂ (radiusTest c h) (burnolUnitTailResponse (barC c) 4) at unit
  rw [lower_zero_price c zero h nonnegative bound,
    actual_original_constant_contact c h nonnegative bound] at unit
  have mean:=actual_phase_mean_zero (barC c)
  change (1/2:ℂ)*(phase (star c.value))⁻¹*bandMean (barC c) 0= -constantCoefficient (star c.value) at mean
  have paid:=congrArg (fun z:ℂ=>z*fullMass c h) mean
  linear_combination -unit+paid

def completeProjectionPrice (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  -(1/4:ℂ)*constantCoefficient (star c.value)*inverseBandPrice c h+
    (1/2:ℂ)*(phase (star c.value))⁻¹*fullLogBand c h 0+
    inner ℂ (twoClockSource c h) (gapState c-(K c:BurnolL2))

theorem actual_complete_projection_price (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) (bound : q*Real.exp h<2*q) :
    completeJointModel c h (star c.value)=completeProjectionPrice c h := by
  have logBound : h≤Real.log 2 := by
    have exponential : Real.exp h<2 := by nlinarith
    exact (Real.exp_lt_exp.mp (by simpa only [Real.exp_log (by norm_num:(0:ℝ)<2)] using exponential)).le
  rw [actual_complete_joint_source_price c c h nonnegative logBound,
    actual_zero_unit_price c zero h nonnegative bound,actual_B_projection_price c c h nonnegative]
  rfl

theorem actual_original_fixed_projection_price (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    BurnolPaBoundaryCancellationAt c zero↔
      (pairedMellinTranslationCharacter c.value (Real.log stageZeroSonineQ)-
        pairedMellinTranslationCharacter (star c.value) (Real.log stageZeroSonineQ))*kernelSelfSource c+
      (1/2:ℂ)*completeProjectionPrice c (Real.log stageZeroSonineQ)=0 := by
  have nn : 0≤Real.log stageZeroSonineQ := Real.log_nonneg (by
    change 1≤Real.sqrt 3
    exact Real.le_sqrt_of_sq_le (by norm_num))
  have bound : q*Real.exp (Real.log stageZeroSonineQ)<2*q := by
    rw [Real.exp_log stageZeroSonineQ_pos]
    have strict : stageZeroSonineQ<2 := by
      change Real.sqrt 3<2
      exact Real.sqrt_lt' (by norm_num) |>.mpr (by norm_num)
    nlinarith
  rw [actual_original_fixed_joint c zero,actual_complete_projection_price c zero _ nn bound]

end OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.ProjectionPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
