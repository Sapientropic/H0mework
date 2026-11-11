import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.JointReturn.FirstCell
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Cotest
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.FreeParameter.CountGeometry OriginalKElementaryArithmeticAction.FreeParameter.CountReturn
open OriginalKElementaryArithmeticAction.FreeParameter.Riesz OriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer
open OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Consumer
open OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.CrossContact OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.CrossJet
open OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.FirstCell
open scoped Topology InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "K" => burnolCompletedMellinRieszVector
local notation "D" => burnolMultiplicativeDilation
local notation "F" => fourierL2
local notation "Rq" => burnolQuarterRestriction
local notation "Eq" => burnolQuarterZeroExtension
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "L" => burnolMeanZeroOneMinusSquare
local notation "b" => burnolRieszSingleFourierSource
local notation "P0" => Constructor.zeroMean

/-- The cotest keeps the two genuine source clocks before solving the block. -/
def twoClockSource (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  D h (K c:BurnolL2)+D (-h) (K c:BurnolL2)

def jointCotest (c : BurnolCompletedMellinCoordinate) (h : ℝ) : M :=
  P0 (Rq (fourierTest c h))-S (P0 (Rq (movedTest c h)))

def twoClockCorrection (c : BurnolCompletedMellinCoordinate) (h : ℝ) : M :=
  burnolAmbientMeanZeroSecondCorrection (twoClockSource c h)

theorem actual_return_first_cell_pair (c d : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    inner ℂ (movedTest c h) (countReader (b d:Hq))=
      inner ℂ (P0 (Rq (movedTest c h))) (S (b d)) := by
  have half : q/2≤q*Real.exp (-h) := by
    have bound : (1/2:ℝ)≤Real.exp (-h) := by
      calc
        (1/2:ℝ)=Real.exp (-Real.log 2) := by rw [Real.exp_neg,Real.exp_log (by norm_num)];norm_num
        _≤Real.exp (-h) := Real.exp_le_exp.mpr (neg_le_neg bounded)
    nlinarith
  have source : inner ℂ (movedTest c h) (countReader (b d:Hq))=
      inner ℂ (movedTest c h) (Eq (S (b d):Hq)) := by
    rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [countReader_read (b d:Hq),burnolZeroExtensionMeanZeroFourier_ae_raw (b d),
      actual_moved_gap c h nonnegative] with x counted returned gap
    rw [counted,returned]
    by_cases inside : |x|≤q
    · have member : x∈symmetricInterval q := abs_le.mp inside
      rw [indicator_of_mem member]
      by_cases after : q*Real.exp (-h)< |x|
      · rw [actual_count_first_cell (b d:Hq) x (half.trans_lt after) inside,actual_centeredRaw]
        rfl
      · rw [gap (le_of_not_gt after)]
        simp
    · have outside : x∉symmetricInterval q := fun member=>inside (abs_le.mpr member)
      rw [indicator_of_notMem outside,countRaw_outside _ _ (lt_of_not_ge inside)]
  rw [source]
  change inner ℂ (movedTest c h) (burnolQuarterRestriction.adjoint (S (b d):Hq))=_
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (S (b d)) _).symm

theorem actual_joint_cotest_read (c d : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    jointBRead c h (bModel (star d.value):Hq)=inner ℂ (jointCotest c h) (b d) := by
  rw [←actual_original_B_model]
  change inner ℂ (Rq (fourierTest c h)) (b d:Hq)-inner ℂ (movedTest c h) (countReader (b d:Hq))=_
  rw [actual_return_first_cell_pair c d h nonnegative bounded,jointCotest,inner_sub_left,
    OriginalRieszSourceGreen.meanZero_fourier_pairing_of_reflection _ _
      (burnolRieszSingleFourierSource_reflection_fixed d)]
  congr 1
  exact (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (b d) _).symm

private theorem even_part_fixed (value : BurnolL2) (even : reflectL2 value=value) :
    burnolAmbientEvenPart value=value := by
  rw [burnolAmbientEvenPart,even]
  module

private theorem kernel_even (c : BurnolCompletedMellinCoordinate) :
    reflectL2 (K c:BurnolL2)=(K c:BurnolL2) :=
  mem_evenL2ClosedFace_iff.mp (K c).property.2

private theorem two_clock_even (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    reflectL2 (twoClockSource c h)=twoClockSource c h := by
  rw [twoClockSource,map_add,reflectL2_burnolMultiplicativeDilation,
    reflectL2_burnolMultiplicativeDilation,kernel_even]

private theorem contracted_gap (value : BurnolPaAmbientCarrier) (h : ℝ) (nonpositive : h≤0) :
    Rq (D h (value:BurnolL2))=
      ((Real.exp (h/2):ℂ)*burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value) • intervalConstant q := by
  have gap := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (burnolAmbientGap_ae value)
  have scale : Measure.QuasiMeasurePreserving (fun x : ℝ=>Real.exp h*x) volume volume := by
    simpa only [smul_eq_mul] using Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ)) (Real.exp_ne_zero h)
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (D h (value:BurnolL2)),
    ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn h (value:BurnolL2)),
    ae_restrict_of_ae (scale.ae gap),ae_restrict_mem (measurableSet_symmetricInterval q),
    Lp.coeFn_smul ((Real.exp (h/2):ℂ)*burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value) (intervalConstant q),
    intervalConstant_coeFn q] with x restriction dilation source inside scalar constant
  have stays : Real.exp h*x∈symmetricInterval q := by
    apply abs_le.mp
    rw [abs_mul,abs_of_pos (Real.exp_pos h)]
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr nonpositive) (abs_nonneg x)).trans
      (by simpa only [one_mul] using abs_le.mpr inside)
  change Rq (D h (value:BurnolL2)) x=_ at restriction
  rw [restriction,dilation,scalar,Pi.smul_apply,smul_eq_mul,constant,mul_one]
  change (Real.exp (h/2):ℂ)*(value:BurnolL2) (Real.exp h*x)=_
  rw [source stays]

private theorem projected_constant (z : ℂ) : P0 (z • intervalConstant q)=0 := by
  apply Subtype.ext
  change burnolQuarterMeanZeroProjection (z • intervalConstant q)=0
  exact (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr
    (Submodule.smul_mem _ z (Submodule.mem_span_singleton_self _))

private theorem contracted_mean_zero (value : BurnolPaAmbientCarrier) (h : ℝ) (nonpositive : h≤0) :
    P0 (Rq (D h (value:BurnolL2)))=0 := by
  rw [contracted_gap value h nonpositive,projected_constant]

theorem actual_two_clock_position (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0≤h) :
    burnolAmbientMeanZeroPosition (twoClockSource c h)=P0 (Rq (movedTest c h)) := by
  rw [burnolAmbientMeanZeroPosition,even_part_fixed _ (two_clock_even c h)]
  change P0 (Rq (twoClockSource c h))=_
  rw [twoClockSource,map_add,map_add,contracted_mean_zero (K c) (-h) (neg_nonpos.mpr nonnegative),add_zero]
  rw [movedTest,map_sub,map_smul,map_sub,map_smul]
  have original : P0 (Rq (K c:BurnolL2))=0 := by
    simpa only [burnolMultiplicativeDilation_zero] using contracted_mean_zero (K c) 0 le_rfl
  rw [original,smul_zero,sub_zero]

theorem actual_two_clock_fourier (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0≤h) :
    burnolAmbientMeanZeroFourier (twoClockSource c h)=P0 (Rq (fourierTest c h)) := by
  rw [burnolAmbientMeanZeroFourier,even_part_fixed _ (two_clock_even c h)]
  change P0 (Rq (F (twoClockSource c h)))=_
  rw [twoClockSource,map_add,fourierL2_burnolMultiplicativeDilation,
    fourierL2_burnolMultiplicativeDilation,neg_neg,map_add,map_add]
  let dual : BurnolPaAmbientCarrier := ⟨F (K c:BurnolL2),fourierL2_mem_evenBurnolClosedFace (K c).property⟩
  have negative : P0 (Rq (D (-h) (F (K c:BurnolL2))))=0 :=
    contracted_mean_zero dual (-h) (neg_nonpos.mpr nonnegative)
  have original : P0 (Rq (F (K c:BurnolL2)))=0 := by
    simpa only [burnolMultiplicativeDilation_zero] using
      contracted_mean_zero dual 0 le_rfl
  rw [negative,zero_add,fourierTest,map_sub,map_smul,map_sub,map_smul,original,smul_zero,sub_zero]

private theorem second_correction_equation (value : BurnolL2) :
    L (burnolAmbientMeanZeroSecondCorrection value)=
      burnolAmbientMeanZeroFourier value-S (burnolAmbientMeanZeroPosition value) := by
  have first := burnolMeanZeroBlock_first_equation (burnolAmbientMeanZeroBlockRhs value)
  have second := burnolMeanZeroBlock_second_equation (burnolAmbientMeanZeroBlockRhs value)
  change burnolAmbientMeanZeroFirstCorrection value+S (burnolAmbientMeanZeroSecondCorrection value)=
    burnolAmbientMeanZeroPosition value at first
  change S (burnolAmbientMeanZeroFirstCorrection value)+burnolAmbientMeanZeroSecondCorrection value=
    burnolAmbientMeanZeroFourier value at second
  change burnolAmbientMeanZeroSecondCorrection value-S (S (burnolAmbientMeanZeroSecondCorrection value))=_
  rw [←first,←second,map_add]
  module

/-- The actual sum of both shifts, not a single shifted K, generates the complete Schur cotest. -/
theorem actual_two_clock_correction_source (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) :
    L (twoClockCorrection c h)=jointCotest c h := by
  rw [twoClockCorrection,second_correction_equation,
    actual_two_clock_position c h nonnegative,actual_two_clock_fourier c h nonnegative]
  rfl

private theorem original_inverse_pair (test : M) (d : BurnolCompletedMellinCoordinate) :
    inner ℂ (L test) (b d)=
      inner ℂ test (burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula d)) := by
  change inner ℂ (test-S (S test)) (b d)=_
  rw [inner_sub_left,
    OriginalRieszSourceGreen.meanZero_fourier_pairing_of_reflection _ _
      (burnolRieszSingleFourierSource_reflection_fixed d),
    OriginalRieszSourceGreen.meanZero_fourier_pairing_of_reflection _ _
      (burnolRieszSingleFourierReturn_reflection_fixed d),←inner_sub_right]
  change inner ℂ test (L (b d))=_
  rw [burnolRieszSingleFourierSource_equation]

theorem actual_joint_B_source_price (c d : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    jointBRead c h (bModel (star d.value):Hq)=
      inner ℂ (twoClockCorrection c h)
        (burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula d)) := by
  rw [actual_joint_cotest_read c d h nonnegative bounded,
    ←actual_two_clock_correction_source c h nonnegative,original_inverse_pair]

theorem actual_complete_joint_source_price (c d : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    completeJointModel c h (star d.value)=
      -inner ℂ (movedTest c h) (freeUnit (star d.value) ConstantDual.value)+
        inner ℂ (twoClockCorrection c h)
          (burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula d)) := by
  rw [actual_complete_joint_source,actual_joint_B_source_price c d h nonnegative bounded]

theorem actual_original_fixed_cotest (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    BurnolPaBoundaryCancellationAt c zero↔
      (pairedMellinTranslationCharacter c.value (Real.log stageZeroSonineQ)-
        pairedMellinTranslationCharacter (star c.value) (Real.log stageZeroSonineQ))*kernelSelfSource c+
      (1/2:ℂ)*(-inner ℂ (movedTest c (Real.log stageZeroSonineQ))
        (freeUnit (star c.value) ConstantDual.value)+
        inner ℂ (twoClockCorrection c (Real.log stageZeroSonineQ))
          (burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula c)))=0 := by
  have nn : 0≤Real.log stageZeroSonineQ := Real.log_nonneg (by
    change 1≤Real.sqrt 3
    exact Real.le_sqrt_of_sq_le (by norm_num))
  have bound : Real.log stageZeroSonineQ≤Real.log 2 := Real.log_le_log stageZeroSonineQ_pos (by
    change Real.sqrt 3≤2
    exact Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
  rw [actual_original_fixed_joint c zero,actual_complete_joint_source_price c c _ nn bound]

end OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Cotest
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
