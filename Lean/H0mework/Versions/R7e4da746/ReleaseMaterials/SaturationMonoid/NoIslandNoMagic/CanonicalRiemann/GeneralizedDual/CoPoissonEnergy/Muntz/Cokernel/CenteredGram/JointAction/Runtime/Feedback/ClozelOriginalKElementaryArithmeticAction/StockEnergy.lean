import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.QuarterStock
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.Tate

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.StockEnergy
open Complex Filter MeasureTheory Set BurnolPhysicalState
open BurnolPhysicalState.OriginalRieszSource
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKFixedBoundarySourceFibre OriginalKExteriorCoPoissonAction
open OriginalKElementaryArithmeticAction.QuarterStock
open scoped Topology InnerProductSpace
open private energy reverse_even fourier_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingJointEnergy
open private mean_pair reverse_mean from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingEnergy
open private position_even fourier_even_input b_even r_even left_support right_support from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.QuarterStock
local notation "q"=>(1/4:ℝ)
local notation "M"=>BurnolQuarterMeanZeroCarrier
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "E"=>burnolQuarterZeroExtension
local notation "R"=>burnolQuarterRestriction
local notation "J"=>burnolTateReciprocalL2
local notation "S"=>burnolMeanZeroTruncatedFourier
local notation "L"=>burnolMeanZeroOneMinusSquare
local notation "B"=>CenteredCountingDual.reverse
local notation "C"=>CenteredCountingDual.forward
local notation "ell"=>CenteredCountingDual.logarithm
local notation "H"=>ConstantDual.value

/-- The original whole counted stock, including both unit and centering-mean fields. -/
def stock (c:BurnolCompletedMellinCoordinate) (h:ℝ) : BurnolL2 :=
  finiteBoundaryAction c h (Kernel.A c • H-Kernel.beta c • J H+J (CountingDual.value c)-ReturnCounting.value c)-
    (1/2:ℂ) • FullUnit.exteriorReverse c h 1+(1/2:ℂ) • fourierL2 (exteriorWave c h 0)-
    ((1/2:ℂ)*centeringMean c h 1) • H+((1/2:ℂ)*centeringMean c h 0) • J H

def unitStock (c:BurnolCompletedMellinCoordinate) (h:ℝ) : BurnolL2 :=
  finiteBoundaryAction c h (Kernel.A c • H-Kernel.beta c • J H)
def velocity (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) : BurnolL2 :=
  -CountedEulerDomain.positionVelocity c zero+J (CountedEulerDomain.fourierVelocity c)
def unitVelocity (c:BurnolCompletedMellinCoordinate) : BurnolL2 :=
  ((1/2:ℂ)*Kernel.A c) • H+((1/2:ℂ)*Kernel.beta c) • J H

theorem source_stock (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) (bounded:h≤Real.log 2) :
    stock c h=unitStock c h-positionValue c h-J (fourierValue c h) := by
  unfold stock unitStock positionValue fourierValue FullUnit.fullReverse
  rw [OriginalKExteriorCoPoissonAction.Tate.actual_fourier_reverse c h nn bounded 0]
  simp only [finiteBoundaryAction,map_add,map_sub,map_smul,map_neg,
    burnolTateReciprocalL2_dilation_inverse,neg_neg]
  module

theorem source_velocity (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    velocity c zero=leftVelocity c zero+J (rightVelocity c)+unitVelocity c := by
  unfold velocity leftVelocity rightVelocity unitVelocity
  simp only [CountedEulerDomain.positionVelocity,CountedEulerDomain.fourierVelocity,map_add,map_sub,map_smul]
  module

private theorem tate_inner (left right:BurnolL2) : inner ℂ (J left) (J right)=inner ℂ left right := by
  let actual : BurnolL2 →ₗᵢ[ℂ] BurnolL2 :=
    ⟨burnolTateReciprocalL2.toLinearMap,fun x=>burnolTateReciprocalValue_norm x⟩
  exact actual.inner_map_map left right

/-- Two mixed feet are paid by the actual supports; every remaining unit/mean contact remains explicit. -/
theorem complete_mixed_pair (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (bounded:h≤Real.log 2) :
    inner ℂ (velocity c zero) (stock c h)=
      -inner ℂ (leftVelocity c zero) (positionValue c h)-inner ℂ (rightVelocity c) (fourierValue c h)+
      inner ℂ (leftVelocity c zero+J (rightVelocity c)) (unitStock c h)+
      inner ℂ (unitVelocity c) (stock c h) := by
  have cross:=source_cross_feet c zero h nn
  conv_lhs => rw [source_velocity,inner_add_left]
  rw [source_stock c h nn bounded]
  simp only [inner_add_left,inner_sub_right]
  rw [cross.1,cross.2,tate_inner]
  ring

/-- The actual full unit tail, not a compact unit replacement, supplies the interior Tate value. -/
theorem tate_unit_interior : ∀ᵐx:ℝ ∂volume,|x|<4→J H x=-(q:ℂ) := by
  have pulled:=burnolTateReciprocalRaw_ae_congr (Lp.memLp H) ConstantDual.sawtooth_memLp ConstantDual.value_coeFn
  filter_upwards [burnolTateReciprocalL2_coeFn H,pulled,volume.ae_ne (0:ℝ)] with x read raw nonzero inside
  have positive : 0< |x| := abs_pos.mpr nonzero
  have outside : q< |x⁻¹| := by
    rw [abs_inv,inv_eq_one_div]
    apply (lt_div_iff₀ positive).mpr
    linarith
  rw [read,raw]
  unfold burnolTateReciprocalRaw
  rw [ConstantDual.sawtooth_tail _ outside,abs_inv,div_inv_eq_mul]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr positive.ne']

/-- Quarter restriction is performed after the original full dilation of JC. -/
theorem unit_dilation_quarter (time:ℝ) (bounded:time≤Real.log 2) :
    R (burnolMultiplicativeDilation time (J H))=
      (-(q:ℂ)*(Real.exp (time/2):ℂ)) • intervalConstant q := by
  have qmp:=Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ)) (r:=Real.exp time) (Real.exp_ne_zero time)
  have scale : Real.exp time≤2 := by
    simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using Real.exp_le_exp.mpr bounded
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (burnolMultiplicativeDilation time (J H)),
    ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn time (J H)),
    ae_restrict_of_ae (qmp.ae tate_unit_interior),ae_restrict_mem (measurableSet_symmetricInterval q),
    Lp.coeFn_smul (-(q:ℂ)*(Real.exp (time/2):ℂ)) (intervalConstant q),intervalConstant_coeFn q]
    with x restricted moved unit inside scalar constant
  change R (burnolMultiplicativeDilation time (J H)) x=burnolMultiplicativeDilation time (J H) x at restricted
  rw [restricted,moved,scalar]
  unfold burnolL2RawNormalizedDilation
  have small : |Real.exp time*x|<4 := by
    rw [abs_mul,abs_of_pos (Real.exp_pos time)]
    have bound:=abs_le.mpr inside
    nlinarith [Real.exp_pos time,abs_nonneg x]
  simp only [smul_eq_mul] at unit
  rw [unit small]
  change (Real.exp (time/2):ℂ)*(-(q:ℂ))=(-(q:ℂ)*(Real.exp (time/2):ℂ))*intervalConstant q x
  rw [constant]
  ring

def unitCoefficient (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
  -(q:ℂ)*(pairedMellinTranslationCharacter c.value h-
    (1/2:ℂ)*((Real.exp (h/2):ℂ)+(Real.exp (-h/2):ℂ)))

private theorem boundary_tate (c:BurnolCompletedMellinCoordinate) (h:ℝ) (value:BurnolL2) :
    J (finiteBoundaryAction c h value)=finiteBoundaryAction c h (J value) := by
  simp only [finiteBoundaryAction,map_sub,map_add,map_smul,burnolTateReciprocalL2_dilation_inverse,neg_neg]
  module

theorem unit_boundary_quarter (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) (bounded:h≤Real.log 2) :
    R (J (finiteBoundaryAction c h H))=unitCoefficient c h • intervalConstant q := by
  have negative : -h≤Real.log 2 := le_trans (neg_nonpos.mpr nn) (Real.log_nonneg (by norm_num))
  have fixed : R (J H)=-(q:ℂ) • intervalConstant q := by
    simpa only [zero_div,Real.exp_zero,Complex.ofReal_one,mul_one,burnolMultiplicativeDilation_zero] using
      unit_dilation_quarter 0 (Real.log_nonneg (by norm_num))
  rw [boundary_tate,finiteBoundaryAction]
  simp only [map_sub,map_smul,map_add]
  rw [unit_dilation_quarter h bounded,unit_dilation_quarter (-h) negative,fixed]
  unfold unitCoefficient
  module

private theorem quarter_pair_mean (left right:BurnolL2) (source:OriginalPaPhysicalGreen.originalPhysicalCutoff q left=left)
    (coefficient:ℂ) (read:R right=coefficient • intervalConstant q) :
    inner ℂ left right=coefficient*(1/2:ℂ)*star (burnolQuarterMeanCoefficient (R left)) := by
  have pairing : inner ℂ left right=inner ℂ (R left) (R right) := by
    calc
      _=inner ℂ (E (R left)) right := by rw [show E (R left)=left from source]
      _=_ := ContinuousLinearMap.adjoint_inner_left R right (R left)
  rw [pairing,read,inner_smul_right]
  have mean:=congrArg star (mean_pair (R left))
  simp only [star_mul,star_ofNat] at mean
  have symmetric : star (inner ℂ (intervalConstant q) (R left))=inner ℂ (R left) (intervalConstant q) := inner_conj_symm _ _
  rw [symmetric] at mean
  linear_combination -(coefficient/2)*mean

/-- The two boundary-unit cross prices are generated as original ordinary means. -/
theorem unit_cross_prices (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (bounded:h≤Real.log 2) :
    inner ℂ (leftVelocity c zero) (J (finiteBoundaryAction c h H))=
      unitCoefficient c h*(1/2:ℂ)*star (burnolQuarterMeanCoefficient (R (leftVelocity c zero))) ∧
    inner ℂ (J (rightVelocity c)) (finiteBoundaryAction c h H)=
      unitCoefficient c h*(1/2:ℂ)*star (burnolQuarterMeanCoefficient (R (rightVelocity c))) := by
  constructor
  · exact quarter_pair_mean _ _ (left_support c zero) _ (unit_boundary_quarter c h nn bounded)
  · have transpose:=tate_inner (rightVelocity c) (J (finiteBoundaryAction c h H))
    rw [burnolTateReciprocalL2_involutive] at transpose
    rw [transpose]
    exact quarter_pair_mean _ _ (right_support c) _ (unit_boundary_quarter c h nn bounded)

/-- The logarithmic price is read from the same finite reverse source, with its full ordinary mean. -/
private theorem mean_limit (state:M) (value:BurnolL2)
    (source:Tendsto (fun N:ℕ=>DualSource.source N (E (state:Hq))) atTop (𝓝 value)) :
    burnolQuarterMeanCoefficient (R value)=2*inner ℂ ell state := by
  have continuousMean : Continuous (fun x:BurnolL2=>burnolQuarterMeanCoefficient (R x)) := by
    unfold burnolQuarterMeanCoefficient
    fun_prop
  have actual:=(continuousMean.tendsto value).comp source
  have fixed:=actual.congr' (show _ =ᶠ[atTop] (fun _:ℕ=>2*inner ℂ ell state) from by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N positive
    exact reverse_mean N positive state)
  exact tendsto_nhds_unique fixed tendsto_const_nhds

theorem source_log_means (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) :
    burnolQuarterMeanCoefficient (R (positionValue c h))=2*inner ℂ ell (compactPosition c h) ∧
    burnolQuarterMeanCoefficient (R (fourierValue c h))=2*inner ℂ ell (compactFourier c h) :=
  ⟨mean_limit _ _ (position_tendsto c h nn),mean_limit _ _ (fourier_tendsto c h nn)⟩

/-- Both remaining reciprocal-unit/compact prices are exact original logarithmic means. -/
theorem compact_unit_cross_prices (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) :
    inner ℂ (J H) (positionValue c h)=-(q:ℂ)*inner ℂ ell (compactPosition c h) ∧
      inner ℂ H (J (fourierValue c h))=-(q:ℂ)*inner ℂ ell (compactFourier c h) := by
  have fixed : R (J H)=-(q:ℂ) • intervalConstant q := by
    simpa only [zero_div,Real.exp_zero,Complex.ofReal_one,mul_one,burnolMultiplicativeDilation_zero] using
      unit_dilation_quarter 0 (Real.log_nonneg (by norm_num))
  have pair (state:BurnolL2) (source:OriginalPaPhysicalGreen.originalPhysicalCutoff q state=state) :
      inner ℂ (J H) state=-(q:ℂ)*(1/2:ℂ)*burnolQuarterMeanCoefficient (R state) := by
    have direct:=quarter_pair_mean state (J H) source (-(q:ℂ)) fixed
    calc
      _=star (inner ℂ state (J H)) := (inner_conj_symm _ _).symm
      _=_ := by
        rw [direct]
        simp only [star_mul,star_star,star_neg]
        norm_num
        ring
  have means:=source_log_means c h nn
  constructor
  · rw [pair _ (position_support c h nn),means.1]
    ring
  · have same:=tate_inner H (J (fourierValue c h))
    rw [burnolTateReciprocalL2_involutive] at same
    rw [←same,pair _ (fourier_support c h nn),means.2]
    ring

/-- Actual cp/cq are cotests of the original same-N source action, never asserted to be an inverse pair. -/
theorem original_rank_two_stock (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h)
    (N:ℕ) (positive:0<N) :
    inner ℂ (C N (S (sourceB c))-S (B N (sourceB c))) (compactPosition c h)=
      2*(inner ℂ (sourceB c) ell*inner ℂ CenteredCountingDual.constantFourier (compactPosition c h)-
        inner ℂ (sourceB c) CenteredCountingDual.constantFourier*inner ℂ ell (compactPosition c h)) ∧
    inner ℂ (C N (S (sourceSB c))-S (B N (sourceSB c))) (compactFourier c h)=
      2*(inner ℂ (sourceSB c) ell*inner ℂ CenteredCountingDual.constantFourier (compactFourier c h)-
        inner ℂ (sourceSB c) CenteredCountingDual.constantFourier*inner ℂ ell (compactFourier c h)) := by
  constructor
  · exact CenteredCountingDual.commutator_pairing N positive _ _ (b_even c) (position_even c h nn)
  · exact CenteredCountingDual.commutator_pairing N positive _ _ (r_even c) (fourier_even_input c h nn)

end OriginalKElementaryArithmeticAction.StockEnergy
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
