import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionHead
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Position
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.OriginalPrice
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Consumer OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ReciprocalMoment OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularForward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionHead OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Position
open scoped Topology InnerProductSpace
open private forward_bound forward_measurable pweight from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward
local notation "q"=>(1/4:ℝ)
local notation "μq"=>volume.restrict (symmetricInterval q)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "M"=>BurnolQuarterMeanZeroCarrier
local notation "K"=>burnolCompletedMellinRieszVector
local notation "F"=>fourierL2
local notation "Rq"=>burnolQuarterRestriction
local notation "Eq"=>burnolQuarterZeroExtension
local notation "S"=>burnolMeanZeroTruncatedFourier
local notation "P0"=>Constructor.zeroMean
local notation "BI"=>burnolMeanZeroBlockInverse
local instance finiteQuarter:IsFiniteMeasure μq where
  measure_univ_lt_top:=lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

private theorem forward_quarter_memLp (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    MemLp (burnolInnerGapForward (regularCompactRaw c)) 2 μq:=by
  obtain ⟨L,nonnegative,growth⟩:=actual_regular_global_growth c zero
  let mass:ℝ:=∑'n:ℕ,pweight n
  have positiveMass:0≤mass:=tsum_nonneg (fun n=>by unfold pweight;positivity)
  apply MemLp.of_bound
    (forward_measurable _ (actual_regular_measurable c)).aestronglyMeasurable.restrict (L*q*mass)
  filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with x inside
  exact (forward_bound _ L growth x).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (abs_le.mpr inside) nonnegative) positiveMass)

/-- The complete regular counting bank is built from its own source, independently of Whole's representation. -/
def forwardQuarter (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):Hq:=
  (forward_quarter_memLp c zero).toLp (burnolInnerGapForward (regularCompactRaw c))

theorem actual_forward_quarter_raw (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    (forwardQuarter c zero:ℝ→ℂ)=ᵐ[μq]burnolInnerGapForward (regularCompactRaw c):=
  (forward_quarter_memLp c zero).coeFn_toLp

/-- The actual Whole q field carries its regularized reciprocal Unit. -/
theorem actual_whole_quarter_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    Rq (wholeValue c zero h positive)=forwardQuarter c zero-
      wholeReciprocalFinitePart c • intervalConstant q:=by
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (wholeValue c zero h positive),
    actual_whole_head c zero h positive,actual_forward_quarter_raw c zero,
    Lp.coeFn_sub (forwardQuarter c zero) (wholeReciprocalFinitePart c • intervalConstant q),
    Lp.coeFn_smul (wholeReciprocalFinitePart c) (intervalConstant q),intervalConstant_coeFn q]
    with x restricted whole forward subtracted scalar constant
  change Rq (wholeValue c zero h positive) x=(wholeValue c zero h positive) x at restricted
  rw [restricted,whole,subtracted,Pi.sub_apply,scalar,Pi.smul_apply,smul_eq_mul,constant,mul_one,forward]
  rfl

def sourceInverse (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):M:=
  BI (P0 (forwardQuarter c zero))

theorem actual_position_inverse_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):positionInverse c zero h positive=sourceInverse c zero:=by
  rw [positionInverse,positionSource,actual_whole_quarter_source,map_sub,map_smul,
    Constructor.zeroMean_constant,smul_zero,sub_zero]
  rfl

private theorem mean_sub_constant (state:Hq) (z:ℂ):
    burnolQuarterMeanCoefficient (state-z • intervalConstant q)=burnolQuarterMeanCoefficient state-z:=by
  have oneMean:burnolQuarterMeanCoefficient (intervalConstant q)=1:=by
    rw [Constructor.mean_integral,integral_congr_ae (intervalConstant_coeFn q),integral_const,
      burnolRadiusInterval_measureReal_univ (by norm_num : (0:ℝ)<q),Complex.real_smul]
    norm_num
  simp only [burnolQuarterMeanCoefficient,inner_sub_right,inner_smul_right,sub_div,mul_div_assoc]
  change burnolQuarterMeanCoefficient state-z*burnolQuarterMeanCoefficient (intervalConstant q)=_
  rw [oneMean,mul_one]
  rfl

/-- Both original Unit slots are rewritten through the genuine regular source and its actual inverse. -/
theorem actual_position_unit (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    Rq (burnolEvenAmbientProjection (wholeValue c zero h positive):BurnolL2)=
      (burnolQuarterMeanCoefficient (forwardQuarter c zero)-wholeReciprocalFinitePart c+
        burnolQuarterMeanCoefficient (burnolTruncatedFourier (S (sourceInverse c zero):Hq))) • intervalConstant q:=by
  rw [actual_physical_position_unit,actual_position_inverse_source,actual_whole_quarter_source,mean_sub_constant]

theorem actual_fourier_unit (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    Rq (F (burnolEvenAmbientProjection (wholeValue c zero h positive):BurnolL2))=
      (-quarterMean c/4-burnolQuarterMeanCoefficient (burnolTruncatedFourier (sourceInverse c zero:Hq))) • intervalConstant q:=by
  rw [actual_physical_fourier_unit,actual_position_inverse_source]

/-- The actual original physical Mellin consumer now reads the source-computed inverse field. -/
theorem actual_original_source_price (c d:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    inner ℂ (K d:BurnolL2) (wholeValue c zero h positive)=
      mellin ((wholeValue c zero h positive-Eq (sourceInverse c zero:Hq)+
        F (Eq (S (sourceInverse c zero):Hq)):BurnolL2):ℝ→ℂ) (1-d.value):=by
  rw [actual_original_position_price,actual_position_inverse_source]

/-- The original Fourier B contact is already zero; the remaining position contact is this exact compact bank. -/
theorem actual_original_forward_price (c d:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    inner ℂ (K d:BurnolL2) (wholeValue c zero h positive)=
      inner ℂ (gapState d) (wholeValue c zero h positive)+
        inner ℂ (S (burnolRieszSingleFourierSource d):Hq) (forwardQuarter c zero):=by
  rw [OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.FourierContact.actual_original_K_price c d zero h positive,
    show Eq=burnolQuarterRestriction.adjoint from rfl,ContinuousLinearMap.adjoint_inner_left,
    actual_whole_quarter_source,inner_sub_right,inner_smul_right]
  have mean:inner ℂ (S (burnolRieszSingleFourierSource d):Hq) (intervalConstant q)=0:=by
    apply inner_eq_zero_symm.mp
    exact (Submodule.mem_orthogonal _ _).mp (S (burnolRieszSingleFourierSource d)).property _
      (Submodule.mem_span_singleton_self _)
  rw [mean,mul_zero,sub_zero]


theorem actual_compact_source_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h) (test:M):
    inner ℂ (Eq (test:Hq)) (wholeValue c zero h positive)=inner ℂ (test:Hq) (forwardQuarter c zero):=by
  rw [show Eq=burnolQuarterRestriction.adjoint from rfl,ContinuousLinearMap.adjoint_inner_left,
    actual_whole_quarter_source,inner_sub_right,inner_smul_right]
  have mean:inner ℂ (test:Hq) (intervalConstant q)=0:=by
    apply inner_eq_zero_symm.mp
    exact (Submodule.mem_orthogonal _ _).mp test.property _ (Submodule.mem_span_singleton_self _)
  rw [mean,mul_zero,sub_zero]

/-- The other original K leg uses the same source bank with its actual signed b contact. -/
theorem actual_original_fourier_source_price (c d:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    inner ℂ (F (K d:BurnolL2)) (wholeValue c zero h positive)=
      inner ℂ (F (gapState d)) (wholeValue c zero h positive)-
        inner ℂ (burnolRieszSingleFourierSource d:Hq) (forwardQuarter c zero):=by
  have even:reflectL2 (Eq (burnolRieszSingleFourierSource d:Hq))=Eq (burnolRieszSingleFourierSource d:Hq):=by
    rw [show Eq=burnolRadiusZeroExtension q from rfl,burnolRadiusZeroExtension_reflect,
      burnolRieszSingleFourierSource_reflection_fixed]
  have source:=congrArg (fun state:BurnolL2=>inner ℂ (F state) (wholeValue c zero h positive))
    (gapState_eq_kernel_add_correction d)
  rw [map_add,inner_add_left,sourceCorrection,map_sub,inner_sub_left,fourierL2_fourierL2,even,
    OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.OriginalPrice.actual_meanZero_fourier_contact c zero h positive
      (S (burnolRieszSingleFourierSource d)),sub_zero,actual_compact_source_price] at source
  linear_combination -source

/-- Both complete contacts of the original source combination are paid by the same regular quarter bank. -/
theorem actual_original_combo_source_price (c d:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    inner ℂ (OriginalKCrossParameterRAdjointSource.SharedOutsideSource.sourceKernelCombo d)
      (wholeValue c zero h positive)=
      star (OriginalKCrossParameterRAdjointSource.SharedOutsideSource.jQuarterAmplitude d)*
        inner ℂ (gapState d) (wholeValue c zero h positive)-
      star (OriginalKDirectRCofinalOutsideVolterraSource.hQuarterAmplitude d)*
        inner ℂ (F (gapState d)) (wholeValue c zero h positive)+
      star (OriginalKCrossParameterRAdjointSource.SharedOutsideSource.jQuarterAmplitude d)*
        inner ℂ (S (burnolRieszSingleFourierSource d):Hq) (forwardQuarter c zero)+
      star (OriginalKDirectRCofinalOutsideVolterraSource.hQuarterAmplitude d)*
        inner ℂ (burnolRieszSingleFourierSource d:Hq) (forwardQuarter c zero):=by
  rw [OriginalKCrossParameterRAdjointSource.SharedOutsideSource.sourceKernelCombo_actual,
    inner_sub_left,inner_smul_left,inner_smul_left,starRingEnd_apply,starRingEnd_apply,
    actual_original_forward_price,actual_original_fourier_source_price]
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
