import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKContactClosureSourceData
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.Action
import H0mework.Versions.R7e4da746.Arithmetic.RieszEuler.Extension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPairedBEulerJunctionSource.TwoPieceFourierAction
open Complex MeasureTheory Set Filter FourierTransform BurnolPhysicalState OriginalRieszSource
open scoped InnerProductSpace Topology ENNReal
attribute [local instance 1100] NormedSpace.complexToReal
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "S" => burnolMeanZeroTruncatedFourier
local instance quarterFinite : IsFiniteMeasure μq where
 measure_univ_lt_top:=lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

private theorem singlePieceIBP (a b : ℝ) (ordered : a ≤ b)
    (f df test dtest : ℝ → ℂ)
    (cf : ContinuousOn f (Icc a b)) (cdf : ContinuousOn df (Icc a b))
    (ct : ContinuousOn test (Icc a b)) (cdt : ContinuousOn dtest (Icc a b))
    (hf : ∀ x ∈ Ioo a b, HasDerivAt f (df x) x)
    (ht : ∀ x ∈ Ioo a b, HasDerivAt test (dtest x) x) :
    -(∫ x : ℝ in a..b, ((x : ℂ) * dtest x + (1/2 : ℂ) * test x) * f x) =
      (∫ x : ℝ in a..b, test x * ((x : ℂ) * df x + (1/2 : ℂ) * f x)) -
        ((b : ℂ) * test b * f b - (a : ℂ) * test a * f a) := by
  have castContinuous : ContinuousOn (fun x : ℝ => (x : ℂ)) (Icc a b) :=
    Complex.continuous_ofReal.continuousOn
  have leftContinuous := ((castContinuous.mul cdt).add (ct.const_mul (1/2 : ℂ))).mul cf
  have rightContinuous := ct.mul ((castContinuous.mul cdf).add (cf.const_mul (1/2 : ℂ)))
  have leftIntegrable : IntervalIntegrable
      (fun x : ℝ => ((x : ℂ) * dtest x + (1/2 : ℂ) * test x) * f x) volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le ordered, Pi.mul_apply, Pi.add_apply] using! leftContinuous
  have rightIntegrable : IntervalIntegrable
      (fun x : ℝ => test x * ((x : ℂ) * df x + (1/2 : ℂ) * f x)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le ordered, Pi.mul_apply, Pi.add_apply] using! rightContinuous
  have derivative (x : ℝ) (inside : x ∈ Ioo a b) :
      HasDerivAt (fun y : ℝ => (y : ℂ) * test y * f y)
        ((((x : ℂ) * dtest x + (1/2 : ℂ) * test x) * f x) +
          test x * ((x : ℂ) * df x + (1/2 : ℂ) * f x)) x := by
    have castDerivative : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
      simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using! (Complex.ofRealCLM.hasDerivAt (x := x))
    convert (castDerivative.mul (ht x inside)).mul (hf x inside) using 1 <;> first | rfl | (dsimp only [Pi.mul_apply, Pi.add_apply]; ring)
  have fundamental := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ordered
    ((castContinuous.mul ct).mul cf) derivative (leftIntegrable.add rightIntegrable)
  rw [intervalIntegral.integral_add leftIntegrable rightIntegrable] at fundamental
  dsimp only [Pi.mul_apply] at fundamental
  linear_combination -fundamental

private theorem twoPieceIBP (p r : ℝ) (positive : 0 < p) (inside : p < r)
    (f0 df0 f1 df1 test dtest : ℝ → ℂ)
    (cf0 : ContinuousOn f0 (Icc 0 p)) (cd0 : ContinuousOn df0 (Icc 0 p))
    (cf1 : ContinuousOn f1 (Icc p r)) (cd1 : ContinuousOn df1 (Icc p r))
    (ct0 : ContinuousOn test (Icc 0 p)) (cdt0 : ContinuousOn dtest (Icc 0 p))
    (ct1 : ContinuousOn test (Icc p r)) (cdt1 : ContinuousOn dtest (Icc p r))
    (hf0 : ∀ x ∈ Ioo 0 p, HasDerivAt f0 (df0 x) x)
    (hf1 : ∀ x ∈ Ioo p r, HasDerivAt f1 (df1 x) x)
    (ht0 : ∀ x ∈ Ioo 0 p, HasDerivAt test (dtest x) x)
    (ht1 : ∀ x ∈ Ioo p r, HasDerivAt test (dtest x) x) :
    -((∫ x : ℝ in 0..p, ((x : ℂ) * dtest x + (1/2 : ℂ) * test x) * f0 x) +
      (∫ x : ℝ in p..r, ((x : ℂ) * dtest x + (1/2 : ℂ) * test x) * f1 x)) =
      (∫ x : ℝ in 0..p, test x * ((x : ℂ) * df0 x + (1/2 : ℂ) * f0 x)) +
      (∫ x : ℝ in p..r, test x * ((x : ℂ) * df1 x + (1/2 : ℂ) * f1 x)) +
      (p : ℂ) * (f1 p - f0 p) * test p - (r : ℂ) * f1 r * test r := by
  have first := singlePieceIBP 0 p positive.le f0 df0 test dtest cf0 cd0 ct0 cdt0 hf0 ht0
  have second := singlePieceIBP p r inside.le f1 df1 test dtest cf1 cd1 ct1 cdt1 hf1 ht1
  simp only [Complex.ofReal_zero, zero_mul, sub_zero] at first
  linear_combination first + second


private theorem state_integrable (state:Hq) : Integrable state μq :=
 (Lp.memLp state).integrable (by norm_num)
private theorem state_moment (state:Hq) : Integrable (fun x:ℝ => ‖x‖*‖state x‖) μq := by
 have majorant:=(state_integrable state).norm.const_mul q
 apply majorant.mono' (by fun_prop)
 filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with x inside
 rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg x) (norm_nonneg _))]
 apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
 simpa only [symmetricInterval,mem_Icc,Real.norm_eq_abs,abs_le] using inside
private theorem state_clm_moment (state:Hq) :
 Integrable (VectorFourier.fourierSMulRight (innerSL ℝ) state) μq := by
 have majorant:=(state_moment state).const_mul (2*Real.pi*‖innerSL (E:=ℝ) ℝ‖)
 apply majorant.mono'
 · exact (Lp.memLp state).aestronglyMeasurable.fourierSMulRight
 · filter_upwards with x
   simpa only [mul_assoc] using VectorFourier.norm_fourierSMulRight_le (innerSL (E:=ℝ) ℝ) state x

theorem state_fourier_hasDerivAt (state:Hq) (x:ℝ) :
 HasDerivAt (Constructor.fourierRaw state) (Constructor.fourierDerivative state x) x := by
 have generated:=VectorFourier.hasFDerivAt_fourierIntegral (innerSL ℝ) (state_integrable state) (state_moment state) x
 unfold Constructor.fourierRaw Constructor.fourierDerivative
 have bilinear:(innerₗ ℝ)=(innerSL ℝ).toLinearMap₁₂ := by
  apply LinearMap.ext
  intro y
  apply LinearMap.ext
  intro z
  simp only [innerₗ_apply_apply,ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,innerSL_apply_apply]
 rw [bilinear]
 exact generated.hasDerivAt

theorem state_fourierSlope_continuous (state:Hq) : Continuous (Constructor.fourierDerivative state) := by
 unfold Constructor.fourierDerivative
 exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
  (by simpa only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,innerSL_apply_apply] using
   (continuous_inner:Continuous (fun p:ℝ×ℝ => inner ℝ p.1 p.2))) (state_clm_moment state)).clm_apply continuous_const

theorem meanZero_fourier_hasDerivAt (state:M) (x:ℝ) :
 HasDerivAt (burnolMeanZeroFourierRaw state) (Constructor.fourierDerivative (state:Hq) x) x :=
 (state_fourier_hasDerivAt (state:Hq) x).sub_const _

private theorem state_fourierDerivative_integral (state:Hq) (frequency:ℝ) :
 Constructor.fourierDerivative state frequency=
  ∫ x:ℝ in (-q)..q,Constructor.phase frequency x*(-2*(Real.pi:ℂ)*Complex.I*(x:ℂ)*state x) := by
 unfold Constructor.fourierDerivative
 erw [Real.fourierIntegral_continuousLinearMap_apply' (L:=innerSL ℝ) (a:=(1:ℝ)) (w:=frequency) (state_clm_moment state)]
 rw [intervalIntegral.integral_of_le (by norm_num:-q≤q),←integral_Icc_eq_integral_Ioc]
 unfold VectorFourier.fourierIntegral
 apply integral_congr_ae
 filter_upwards with x
 have innerOne:(innerSL ℝ) x 1=x:=by rw [innerSL_apply_apply,Real.inner_apply,mul_one]
 have innerFrequency:(innerSL ℝ) x frequency=x*frequency:=by rw [innerSL_apply_apply,Real.inner_apply]
 simp only [VectorFourier.fourierSMulRight_apply,ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
  innerOne,innerFrequency,Circle.smul_def,smul_eq_mul,Constructor.phase,real_smul]
 rw [mul_comm x frequency]
 ring

def pieceRaw (p:ℝ) (f0 f1:ℝ → ℂ) (x:ℝ) : ℂ := if |x|≤p then f0 |x| else f1 |x|
def bulkRaw (p:ℝ) (f0 df0 f1 df1:ℝ → ℂ) : ℝ → ℂ :=
 pieceRaw p (fun x => (x:ℂ)*df0 x+(1/2:ℂ)*f0 x) (fun x => (x:ℂ)*df1 x+(1/2:ℂ)*f1 x)

private theorem clipped_continuous (a b:ℝ) (ordered:a≤b) (f:ℝ → ℂ) (regular:ContinuousOn f (Icc a b)) :
 Continuous (fun x:ℝ => f (max a (min b |x|))) :=
 regular.comp_continuous (by fun_prop) (fun x => ⟨le_max_left _ _,max_le ordered (min_le_left _ _)⟩)

theorem piece_native (p:ℝ) (positive:0<p) (inside:p<q) (f0 f1:ℝ → ℂ)
 (cf0:ContinuousOn f0 (Icc 0 p)) (cf1:ContinuousOn f1 (Icc p q)) : MemLp (pieceRaw p f0 f1) 2 μq := by
 let lower:=fun x:ℝ => f0 (max 0 (min p |x|))
 let upper:=fun x:ℝ => f1 (max p (min q |x|))
 have lowerNative:=Constructor.continuous_memLp lower (clipped_continuous 0 p positive.le f0 cf0)
 have upperNative:=Constructor.continuous_memLp upper (clipped_continuous p q inside.le f1 cf1)
 have clamped:MemLp ({x:ℝ | |x|≤p}.piecewise lower upper) 2 μq :=
  MemLp.piecewise (measurableSet_le continuous_abs.measurable measurable_const) (lowerNative.restrict _) (upperNative.restrict _)
 apply (memLp_congr_ae ?_).mp clamped
 filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with x bounds
 have bound:|x|≤q:=abs_le.mpr bounds
 by_cases first:|x|≤p
 · simp only [Set.piecewise,mem_ofPred_eq,first,↓reduceIte,pieceRaw,lower,min_eq_right first,
    max_eq_right (abs_nonneg x)]
 · simp only [Set.piecewise,mem_ofPred_eq,first,↓reduceIte,pieceRaw,upper,min_eq_right bound,
    max_eq_right (le_of_lt (lt_of_not_ge first))]

def pieceBulk (p:ℝ) (positive:0<p) (inside:p<q) (f0 df0 f1 df1:ℝ → ℂ)
 (cf0:ContinuousOn f0 (Icc 0 p)) (cd0:ContinuousOn df0 (Icc 0 p))
 (cf1:ContinuousOn f1 (Icc p q)) (cd1:ContinuousOn df1 (Icc p q)) : Hq :=
 (piece_native p positive inside _ _
  ((Complex.continuous_ofReal.continuousOn.mul cd0).add (cf0.const_mul (1/2:ℂ)))
  ((Complex.continuous_ofReal.continuousOn.mul cd1).add (cf1.const_mul (1/2:ℂ)))).toLp (bulkRaw p f0 df0 f1 df1)

theorem pieceBulk_read (p:ℝ) (positive:0<p) (inside:p<q) (f0 df0 f1 df1:ℝ → ℂ)
 (cf0:ContinuousOn f0 (Icc 0 p)) (cd0:ContinuousOn df0 (Icc 0 p))
 (cf1:ContinuousOn f1 (Icc p q)) (cd1:ContinuousOn df1 (Icc p q)) :
 (pieceBulk p positive inside f0 df0 f1 df1 cf0 cd0 cf1 cd1:ℝ → ℂ)=ᵐ[μq]bulkRaw p f0 df0 f1 df1 :=
 MemLp.coeFn_toLp _

private theorem quarter_pairing_congr (state:Hq) (raw:ℝ → ℂ)
 (read:(state:ℝ → ℂ)=ᵐ[μq]raw) (test:ℝ → ℂ) :
 (∫x:ℝ in (-q)..q,test x*state x)=∫x:ℝ in (-q)..q,test x*raw x := by
 rw [intervalIntegral.integral_of_le (by norm_num:-q≤q),intervalIntegral.integral_of_le (by norm_num:-q≤q),
  ←integral_Icc_eq_integral_Ioc,←integral_Icc_eq_integral_Ioc]
 apply integral_congr_ae
 filter_upwards [read] with x actual
 rw [actual]

private theorem piece_pair_integrable (p:ℝ) (positive:0<p) (inside:p<q) (f0 f1:ℝ → ℂ)
 (cf0:ContinuousOn f0 (Icc 0 p)) (cf1:ContinuousOn f1 (Icc p q)) (test:ℝ → ℂ) (ct:Continuous test) :
 IntervalIntegrable (fun x:ℝ => test x*pieceRaw p f0 f1 x) volume (-q) q := by
 apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num:-q≤q)).mpr
 exact (Constructor.continuous_memLp test ct).integrable_mul (piece_native p positive inside f0 f1 cf0 cf1)

private theorem piece_pairing (p:ℝ) (positive:0<p) (inside:p<q) (f0 f1:ℝ → ℂ)
 (cf0:ContinuousOn f0 (Icc 0 p)) (cf1:ContinuousOn f1 (Icc p q)) (test:ℝ → ℂ) (ct:Continuous test) :
 (∫x:ℝ in (-q)..q,test x*pieceRaw p f0 f1 x)=
 (∫x:ℝ in 0..p,(test x+test (-x))*f0 x)+(∫x:ℝ in p..q,(test x+test (-x))*f1 x) := by
 have whole:=piece_pair_integrable p positive inside f0 f1 cf0 cf1 test ct
 have reflected:=piece_pair_integrable p positive inside f0 f1 cf0 cf1 (fun x => test (-x)) (ct.comp continuous_neg)
 have low:IntervalIntegrable (fun x:ℝ => test x*pieceRaw p f0 f1 x) volume (-q) 0 :=
  whole.mono_set (by simp only [uIcc_of_le (by norm_num:-q≤0),uIcc_of_le (by norm_num:-q≤q)];intro x hx;exact ⟨hx.1,hx.2.trans (by norm_num)⟩)
 have high:IntervalIntegrable (fun x:ℝ => test x*pieceRaw p f0 f1 x) volume 0 q :=
  whole.mono_set (by simp only [uIcc_of_le (by norm_num:0≤q),uIcc_of_le (by norm_num:-q≤q)];intro x hx;exact ⟨(by norm_num:-q≤0).trans hx.1,hx.2⟩)
 have reflectedHigh:IntervalIntegrable (fun x:ℝ => test (-x)*pieceRaw p f0 f1 x) volume 0 q :=
  reflected.mono_set (by simp only [uIcc_of_le (by norm_num:0≤q),uIcc_of_le (by norm_num:-q≤q)];intro x hx;exact ⟨(by norm_num:-q≤0).trans hx.1,hx.2⟩)
 have negative:(∫x:ℝ in (-q)..0,test x*pieceRaw p f0 f1 x)=
  ∫x:ℝ in 0..q,test (-x)*pieceRaw p f0 f1 x := by
  have substitution:=intervalIntegral.integral_comp_neg (f:=fun x:ℝ => test x*pieceRaw p f0 f1 x) (a:=(0:ℝ)) (b:=q)
  simp only [neg_zero] at substitution
  rw [←substitution]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [pieceRaw,abs_neg]
 have folded:(∫x:ℝ in (-q)..q,test x*pieceRaw p f0 f1 x)=
   ∫x:ℝ in 0..q,(test x+test (-x))*pieceRaw p f0 f1 x := by
  rw [←intervalIntegral.integral_add_adjacent_intervals low high,negative,
   ←intervalIntegral.integral_add reflectedHigh high]
  apply intervalIntegral.integral_congr
  intro x _
  ring
 have foldedInt:IntervalIntegrable (fun x:ℝ => (test x+test (-x))*pieceRaw p f0 f1 x) volume 0 q := by
  convert reflectedHigh.add high using 1
  funext x
  ring
 rw [folded,←intervalIntegral.integral_add_adjacent_intervals
  (foldedInt.mono_set (by rw [uIcc_of_le positive.le,uIcc_of_le (by norm_num:0≤q)];exact Icc_subset_Icc le_rfl inside.le))
  (foldedInt.mono_set (by rw [uIcc_of_le inside.le,uIcc_of_le (by norm_num:0≤q)];exact Icc_subset_Icc positive.le le_rfl))]
 congr 1
 · apply intervalIntegral.integral_congr
   intro x hx
   rw [uIcc_of_le positive.le] at hx
   simp only [pieceRaw,abs_of_nonneg hx.1,if_pos hx.2]
 · apply intervalIntegral.integral_congr_Ioo_of_le inside.le
   intro x hx
   simp only [pieceRaw,abs_of_pos (positive.trans hx.1),if_neg (not_le_of_gt hx.1)]


private theorem quarterPieceIBP (p:ℝ) (positive:0<p) (inside:p<q) (f0 df0 f1 df1:ℝ → ℂ)
 (cf0:ContinuousOn f0 (Icc 0 p)) (cd0:ContinuousOn df0 (Icc 0 p))
 (cf1:ContinuousOn f1 (Icc p q)) (cd1:ContinuousOn df1 (Icc p q))
 (hf0:∀x∈Ioo 0 p,HasDerivAt f0 (df0 x) x) (hf1:∀x∈Ioo p q,HasDerivAt f1 (df1 x) x)
 (test dtest:ℝ → ℂ) (ct:Continuous test) (cdt:Continuous dtest)
 (ht:∀x:ℝ,HasDerivAt test (dtest x) x) :
 -(∫x:ℝ in (-q)..q,((x:ℂ)*dtest x+(1/2:ℂ)*test x)*pieceRaw p f0 f1 x)=
 (∫x:ℝ in (-q)..q,test x*bulkRaw p f0 df0 f1 df1 x)+
 (p:ℂ)*(f1 p-f0 p)*(test p+test (-p))-(q:ℂ)*f1 q*(test q+test (-q)) := by
 have testPairContinuous:Continuous (fun x:ℝ => test x+test (-x)):=ct.add (ct.comp continuous_neg)
 have derivativePairContinuous:Continuous (fun x:ℝ => dtest x-dtest (-x)):=cdt.sub (cdt.comp continuous_neg)
 have derivativePair (x:ℝ):HasDerivAt (fun y:ℝ => test y+test (-y)) (dtest x-dtest (-x)) x := by
  have reflected:HasDerivAt (fun y:ℝ => test (-y)) (-dtest (-x)) x := by
   simpa only [neg_one_smul,Function.comp_def] using (ht (-x)).scomp x ((hasDerivAt_id x).neg)
  convert (ht x).add reflected using 1 <;> rfl
 have generated:=twoPieceIBP p q positive inside f0 df0 f1 df1
  (fun x => test x+test (-x)) (fun x => dtest x-dtest (-x)) cf0 cd0 cf1 cd1
  testPairContinuous.continuousOn derivativePairContinuous.continuousOn
  testPairContinuous.continuousOn derivativePairContinuous.continuousOn hf0 hf1
  (fun x _ => derivativePair x) (fun x _ => derivativePair x)
 have bulk0:ContinuousOn (fun x:ℝ => (x:ℂ)*df0 x+(1/2:ℂ)*f0 x) (Icc 0 p):=
  (Complex.continuous_ofReal.continuousOn.mul cd0).add (cf0.const_mul (1/2:ℂ))
 have bulk1:ContinuousOn (fun x:ℝ => (x:ℂ)*df1 x+(1/2:ℂ)*f1 x) (Icc p q):=
  (Complex.continuous_ofReal.continuousOn.mul cd1).add (cf1.const_mul (1/2:ℂ))
 unfold bulkRaw
 rw [piece_pairing p positive inside f0 f1 cf0 cf1
   (fun x:ℝ => (x:ℂ)*dtest x+(1/2:ℂ)*test x) (by fun_prop),
  piece_pairing p positive inside _ _ bulk0 bulk1 test ct]
 have kernel (x:ℝ):((x:ℂ)*dtest x+(1/2:ℂ)*test x)+
   (((-x:ℝ):ℂ)*dtest (-x)+(1/2:ℂ)*test (-x))=
   (x:ℂ)*(dtest x-dtest (-x))+(1/2:ℂ)*(test x+test (-x)) := by
  push_cast
  ring
 simp_rw [kernel]
 exact generated


def smoothFourierBulk (state:M) : Hq :=
 Constructor.compact
  (fun x:ℝ => (x:ℂ)*Constructor.fourierDerivative (state:Hq) x+(1/2:ℂ)*burnolMeanZeroFourierRaw state x)
  (by have slope:=state_fourierSlope_continuous (state:Hq)
      have value:=OriginalCommonInverseForcing.InverseEuler.meanZeroRaw_continuous state
      fun_prop)

theorem smoothFourierBulk_read (state:M) :
 (smoothFourierBulk state:ℝ → ℂ)=ᵐ[μq]
  (fun x:ℝ => (x:ℂ)*Constructor.fourierDerivative (state:Hq) x+(1/2:ℂ)*burnolMeanZeroFourierRaw state x) :=
 Constructor.compact_read _ _


section ActualPieces
variable (p:ℝ) (positive:0<p) (inside:p<q) (f0 df0 f1 df1:ℝ → ℂ)
variable (cf0:ContinuousOn f0 (Icc 0 p)) (cd0:ContinuousOn df0 (Icc 0 p))
variable (cf1:ContinuousOn f1 (Icc p q)) (cd1:ContinuousOn df1 (Icc p q))
variable (hf0:∀x∈Ioo 0 p,HasDerivAt f0 (df0 x) x) (hf1:∀x∈Ioo p q,HasDerivAt f1 (df1 x) x)
include hf0 hf1
local notation "bulk" => pieceBulk p positive inside f0 df0 f1 df1 cf0 cd0 cf1 cd1

/-- Interior jumps and outer traces are generated on the same actual quarter extension. -/
theorem weak_two_piece_euler (state:Hq) (read:(state:ℝ → ℂ)=ᵐ[μq]pieceRaw p f0 f1) :
 GapEuler.euler (burnolQuarterZeroExtension state:TemperedDistribution ℝ ℂ)=
 (burnolQuarterZeroExtension bulk:TemperedDistribution ℝ ℂ)+
 ((p:ℂ)*(f1 p-f0 p)) • (TemperedDistribution.delta p+TemperedDistribution.delta (-p))-
 ((q:ℂ)*f1 q) • (TemperedDistribution.delta q+TemperedDistribution.delta (-q)) := by
 ext test
 have derivativeContinuous:Continuous (deriv test):=(SchwartzMap.derivCLM ℂ ℂ test).continuous
 have action:=quarterPieceIBP p positive inside f0 df0 f1 df1 cf0 cd0 cf1 cd1 hf0 hf1
  test (deriv test) test.continuous derivativeContinuous test.hasDerivAt
 have derivativeInt:=piece_pair_integrable p positive inside f0 f1 cf0 cf1
  (fun x:ℝ => (x:ℂ)*deriv test x) (by fun_prop)
 have valueInt:=piece_pair_integrable p positive inside f0 f1 cf0 cf1 test test.continuous
 have kernel:(fun x:ℝ => ((x:ℂ)*deriv test x+(1/2:ℂ)*test x)*pieceRaw p f0 f1 x)=
   (fun x:ℝ => ((x:ℂ)*deriv test x)*pieceRaw p f0 f1 x)+
   (fun x:ℝ => (1/2:ℂ)*(test x*pieceRaw p f0 f1 x)) := by
  funext x
  dsimp only [Pi.add_apply]
  ring
 rw [kernel] at action
 erw [intervalIntegral.integral_add derivativeInt (valueInt.const_mul _),intervalIntegral.integral_const_mul] at action
 rw [Translator.ForcingCutoff.euler_zeroExtension_pairing state _ read test]
 simp only [sub_apply,add_apply,smul_apply,TemperedDistribution.delta_apply,smul_eq_mul]
 rw [Translator.ForcingCutoff.zeroExtension_pairing bulk _ (pieceBulk_read p positive inside f0 df0 f1 df1 cf0 cd0 cf1 cd1) test]
 rw [←intervalIntegral.integral_of_le (by norm_num:-q≤q),
  ←intervalIntegral.integral_of_le (by norm_num:-q≤q),←intervalIntegral.integral_of_le (by norm_num:-q≤q)]
 have derivativeOrder:(∫x:ℝ in (-q)..q,((x:ℂ)*pieceRaw p f0 f1 x)*deriv test x)=
  ∫x:ℝ in (-q)..q,((x:ℂ)*deriv test x)*pieceRaw p f0 f1 x := by
  apply intervalIntegral.integral_congr
  intro x _
  ring
 have valueOrder:(∫x:ℝ in (-q)..q,pieceRaw p f0 f1 x*test x)=
  ∫x:ℝ in (-q)..q,test x*pieceRaw p f0 f1 x := by
  apply intervalIntegral.integral_congr
  intro x _
  exact mul_comm _ _
 have bulkOrder:(∫x:ℝ in (-q)..q,bulkRaw p f0 df0 f1 df1 x*test x)=
  ∫x:ℝ in (-q)..q,test x*bulkRaw p f0 df0 f1 df1 x := by
  apply intervalIntegral.integral_congr
  intro x _
  exact mul_comm _ _
 rw [derivativeOrder,valueOrder,bulkOrder]
 linear_combination action

/-- The bulk mean is generated independently of the Fourier-return mean. -/
theorem pieceBulk_mean (state:Hq) (read:(state:ℝ → ℂ)=ᵐ[μq]pieceRaw p f0 f1) :
 burnolQuarterMeanCoefficient bulk=
 f1 q-((p/q:ℝ):ℂ)*(f1 p-f0 p)-(1/2:ℂ)*burnolQuarterMeanCoefficient state := by
 have action:=quarterPieceIBP p positive inside f0 df0 f1 df1 cf0 cd0 cf1 cd1 hf0 hf1
  (fun _:ℝ => (1:ℂ)) (fun _:ℝ => (0:ℂ)) continuous_const continuous_const (fun x => hasDerivAt_const x (1:ℂ))
 simp only [mul_zero,mul_one,zero_add,one_mul,intervalIntegral.integral_const_mul] at action
 have meanRead (value:Hq) (raw:ℝ → ℂ) (actual:(value:ℝ → ℂ)=ᵐ[μq]raw) :
  burnolQuarterMeanCoefficient value=(2:ℂ)*(∫x:ℝ in (-q)..q,raw x) := by
  rw [Constructor.mean_integral]
  congr 1
  rw [intervalIntegral.integral_of_le (by norm_num:-q≤q),←integral_Icc_eq_integral_Ioc]
  exact integral_congr_ae actual
 rw [meanRead bulk _ (pieceBulk_read p positive inside f0 df0 f1 df1 cf0 cd0 cf1 cd1),meanRead state _ read]
 push_cast
 norm_num at action ⊢
 linear_combination -2*action


/-- The native phase kernel generates both outer traces and the interior jump with their actual signs. -/
theorem two_piece_fourier_action (state:Hq) (read:(state:ℝ → ℂ)=ᵐ[μq]pieceRaw p f0 f1) (frequency:ℝ) :
 (frequency:ℂ)*Constructor.fourierDerivative state frequency+(1/2:ℂ)*Constructor.fourierRaw state frequency+
 Constructor.fourierRaw bulk frequency=
 (q:ℂ)*f1 q*(Constructor.phase frequency q+Constructor.phase frequency (-q))-
 (p:ℂ)*(f1 p-f0 p)*(Constructor.phase frequency p+Constructor.phase frequency (-p)) := by
 let phase:=Constructor.phase frequency
 let dphase:=fun x:ℝ => -2*(Real.pi:ℂ)*Complex.I*(frequency:ℂ)*phase x
 have phaseContinuous:Continuous phase:=Constructor.phaseContinuous frequency
 have dphaseContinuous:Continuous dphase:=by dsimp only [dphase];fun_prop
 have action:=quarterPieceIBP p positive inside f0 df0 f1 df1 cf0 cd0 cf1 cd1 hf0 hf1 phase dphase
  phaseContinuous dphaseContinuous (Constructor.phase_derivative frequency)
 let moment:=fun x:ℝ => phase x*(-2*(Real.pi:ℂ)*Complex.I*(x:ℂ))
 have momentContinuous:Continuous moment:=by dsimp only [moment];fun_prop
 have valueRepresentative:Constructor.fourierRaw state frequency=
   ∫x:ℝ in (-q)..q,phase x*pieceRaw p f0 f1 x := by
  rw [Constructor.fourierRaw_integral]
  exact quarter_pairing_congr state _ read phase
 have derivativeRepresentative:Constructor.fourierDerivative state frequency=
   ∫x:ℝ in (-q)..q,moment x*pieceRaw p f0 f1 x := by
  rw [state_fourierDerivative_integral]
  have order:(fun x:ℝ => Constructor.phase frequency x*(-2*(Real.pi:ℂ)*Complex.I*(x:ℂ)*state x))=
    fun x:ℝ => moment x*state x := by funext x;dsimp only [moment,phase];ring
  rw [order]
  exact quarter_pairing_congr state _ read moment
 have bulkRepresentative:Constructor.fourierRaw bulk frequency=
   ∫x:ℝ in (-q)..q,phase x*bulkRaw p f0 df0 f1 df1 x := by
  rw [Constructor.fourierRaw_integral]
  exact quarter_pairing_congr bulk _ (pieceBulk_read p positive inside f0 df0 f1 df1 cf0 cd0 cf1 cd1) phase
 have momentInt:=piece_pair_integrable p positive inside f0 f1 cf0 cf1 moment momentContinuous
 have valueInt:=piece_pair_integrable p positive inside f0 f1 cf0 cf1 phase phaseContinuous
 have kernel:(fun x:ℝ => ((x:ℂ)*dphase x+(1/2:ℂ)*phase x)*pieceRaw p f0 f1 x)=
  (fun x:ℝ => (frequency:ℂ)*(moment x*pieceRaw p f0 f1 x))+
  (fun x:ℝ => (1/2:ℂ)*(phase x*pieceRaw p f0 f1 x)) := by
  funext x
  dsimp only [Pi.add_apply,dphase,moment]
  ring
 rw [kernel] at action
 erw [intervalIntegral.integral_add (momentInt.const_mul _) (valueInt.const_mul _),
  intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
  ←derivativeRepresentative,←valueRepresentative,←bulkRepresentative] at action
 change _=(q:ℂ)*f1 q*(phase q+phase (-q))-(p:ℂ)*(f1 p-f0 p)*(phase p+phase (-p))
 linear_combination -action


/-- The actual Fourier-return mean is retained before mean-zero projection. -/
theorem two_piece_fourier_ambient (state:M) (read:((state:Hq):ℝ → ℂ)=ᵐ[μq]pieceRaw p f0 f1) :
 smoothFourierBulk state+burnolTruncatedFourier bulk=
 ((q:ℂ)*f1 q) • (Constructor.compact (Constructor.phase q) (Constructor.phaseContinuous q)+
   Constructor.compact (Constructor.phase (-q)) (Constructor.phaseContinuous (-q)))-
 ((p:ℂ)*(f1 p-f0 p)) • (Constructor.compact (Constructor.phase p) (Constructor.phaseContinuous p)+
   Constructor.compact (Constructor.phase (-p)) (Constructor.phaseContinuous (-p)))-
 (burnolQuarterMeanCoefficient (burnolTruncatedFourier (state:Hq))/2) • intervalConstant q := by
 let mean:=burnolQuarterMeanCoefficient (burnolTruncatedFourier (state:Hq))
 let A:ℂ:=(q:ℂ)*f1 q
 let B:ℂ:=(p:ℂ)*(f1 p-f0 p)
 let rawEuler:=fun x:ℝ => (x:ℂ)*Constructor.fourierDerivative (state:Hq) x+(1/2:ℂ)*burnolMeanZeroFourierRaw state x
 let rawFourier:=Constructor.fourierRaw bulk
 let rhs:ℝ → ℂ:=A • (Constructor.phase q+Constructor.phase (-q))-
  B • (Constructor.phase p+Constructor.phase (-p))-(mean/2) • (fun _:ℝ => (1:ℂ))
 have rawEulerContinuous:Continuous rawEuler:=by
  have slope:=state_fourierSlope_continuous (state:Hq)
  have value:=OriginalCommonInverseForcing.InverseEuler.meanZeroRaw_continuous state
  dsimp only [rawEuler]
  fun_prop
 have rawFourierContinuous:Continuous rawFourier:=burnolRadiusTruncatedFourierRaw_continuous bulk
 have cq:=Constructor.phaseContinuous q
 have cnq:=Constructor.phaseContinuous (-q)
 have cp:=Constructor.phaseContinuous p
 have cnp:=Constructor.phaseContinuous (-p)
 have rhsContinuous:Continuous rhs:=by dsimp only [rhs];fun_prop
 have equation:rawEuler+rawFourier=rhs := by
  funext x
  have generated:=two_piece_fourier_action p positive inside f0 df0 f1 df1 cf0 cd0 cf1 cd1 hf0 hf1 (state:Hq) read x
  change (x:ℂ)*Constructor.fourierDerivative (state:Hq) x+
   (1/2:ℂ)*(Constructor.fourierRaw (state:Hq) x-mean)+Constructor.fourierRaw bulk x=rhs x
  dsimp only [rhs,A,B,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_one]
  rw [Constructor.phase_symm q x,Constructor.phase_symm (-q) x,Constructor.phase_symm p x,Constructor.phase_symm (-p) x]
  linear_combination generated
 have stateEquation:Constructor.compact (rawEuler+rawFourier) (rawEulerContinuous.add rawFourierContinuous)=
  Constructor.compact rhs rhsContinuous := by
  apply Lp.ext
  filter_upwards [Constructor.compact_read (rawEuler+rawFourier) (rawEulerContinuous.add rawFourierContinuous),
   Constructor.compact_read rhs rhsContinuous] with x left right
  rw [left,right,equation]
 rw [Constructor.compact_add] at stateEquation
 change smoothFourierBulk state+Constructor.compact rawFourier rawFourierContinuous=Constructor.compact rhs rhsContinuous at stateEquation
 have actualFourier:Constructor.compact rawFourier rawFourierContinuous=burnolTruncatedFourier bulk:=
  Edge.compact_truncatedFourier bulk
 rw [actualFourier] at stateEquation
 refine stateEquation.trans ?_
 change Constructor.compact (A • (Constructor.phase q+Constructor.phase (-q))-
  B • (Constructor.phase p+Constructor.phase (-p))-(mean/2) • (fun _:ℝ => (1:ℂ))) rhsContinuous=_
 rw [Constructor.compact_sub _ _ (by fun_prop) (by fun_prop),
  Constructor.compact_sub _ _ (by fun_prop) (by fun_prop),
  Constructor.compact_smul _ _ (by fun_prop),Constructor.compact_smul _ _ (by fun_prop),
  Constructor.compact_smul _ _ continuous_const,
  Constructor.compact_add _ _ cq cnq,Constructor.compact_add _ _ cp cnp,Constructor.compact_one]

/-- The original quarter endpoint columns normalize the interior contact at p by p/q. -/
theorem centered_two_piece_fourier_action (state:M)
 (read:((state:Hq):ℝ → ℂ)=ᵐ[μq]pieceRaw p f0 f1) :
 Constructor.zeroMean (smoothFourierBulk state)+S (Constructor.zeroMean bulk)=
 f1 q • eta q-(((p/q:ℝ):ℂ)*(f1 p-f0 p)) • eta p := by
 have ambient:=two_piece_fourier_ambient p positive inside f0 df0 f1 df1 cf0 cd0 cf1 cd1 hf0 hf1 state read
 have full:=congrArg Constructor.zeroMean ambient
 simp only [map_add,map_sub,map_smul,Constructor.zeroMean_constant,smul_zero,sub_zero] at full
 have mean:=pieceBulk_mean p positive inside f0 df0 f1 df1 cf0 cd0 cf1 cd1 hf0 hf1 (state:Hq) read
 rw [Constructor.mean_zero state,mul_zero,sub_zero] at mean
 have returned:S (Constructor.zeroMean bulk)=Constructor.zeroMean (burnolTruncatedFourier bulk)-
   burnolQuarterMeanCoefficient bulk • Constructor.zeroMean (burnolTruncatedFourier (intervalConstant q)) := by
  change Constructor.zeroMean (burnolTruncatedFourier (Constructor.zeroMean bulk:Hq))=_
  rw [Constructor.zeroMean_read,map_sub,map_smul,map_sub,map_smul]
 rw [returned,mean]
 unfold eta Constructor.endpointColumn
 simp only [map_sub,map_smul]
 push_cast at full ⊢
 norm_num at full ⊢
 linear_combination (norm := module) full

end ActualPieces

end OriginalKPairedBEulerJunctionSource.TwoPieceFourierAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
