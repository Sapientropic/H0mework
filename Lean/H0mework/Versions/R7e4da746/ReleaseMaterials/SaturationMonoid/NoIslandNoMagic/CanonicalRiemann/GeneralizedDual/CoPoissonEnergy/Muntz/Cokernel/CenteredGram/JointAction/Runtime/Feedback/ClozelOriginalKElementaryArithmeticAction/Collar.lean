import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitResolvent
import H0mework.Versions.R7e4da746.Arithmetic.MellinProjection.FiniteWindow

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction
open Complex Filter MeasureTheory Set BurnolPhysicalState
open BurnolPhysicalState.OriginalRieszSource BurnolPhysicalState.OriginalRieszSourceGreen
open BurnolPhysicalState.OriginalRieszFinitePairing
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKFixedBoundarySourceFibre
open OriginalKExteriorCoPoissonAction OriginalKSourceResolventReconstruction
open OriginalPaPhysicalGreen OriginalRieszFiniteColumns
open scoped InnerProductSpace Topology
local notation "q" => (1/4 : ℝ)
local notation "C" => ConstantDual.seed
local notation "cut" => originalPhysicalCutoff

/-- The zero-owned output is not a constructor input: only C and its generated resolvent source occur. -/
def collarSource (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  GapEuler.gapMean q c •
    (burnolMultiplicativeDilation (-h) C - (Real.exp (-h/2) : ℂ) • C) -
  Complex.exp (sourceRate c * (h : ℂ)) •
    (cut (q*Real.exp h) (unitResolventSource c C) - GapEuler.gapMean q c • C)

def collarRaw (c : BurnolCompletedMellinCoordinate) (h x : ℝ) : ℂ :=
  if q < |x| ∧ |x| ≤ q*Real.exp h then
    (Real.exp (-h/2) : ℂ)*GapEuler.gapMean q c -
      Complex.exp (sourceRate c*(h : ℂ))*(1/2 : ℂ)*((|x| : ℝ) : ℂ)^(-star c.value)
  else 0

private theorem gap_raw_absolute (c : BurnolCompletedMellinCoordinate) (x : ℝ) :
    burnolEvenRaw (burnolAmbientMellinKernelRaw c) x =
      burnolEvenRaw (burnolAmbientMellinKernelRaw c) |x| := by
  rcases le_total 0 x with pos | neg
  · rw [abs_of_nonneg pos]
  · rw [abs_of_nonpos neg]
    unfold burnolEvenRaw
    simp only [neg_neg]
    ring

private theorem power_scaling (c : BurnolCompletedMellinCoordinate) (h x : ℝ) (pos : 0 < x) :
    (Real.exp (-h/2) : ℂ) * ((Real.exp (-h)*x : ℝ) : ℂ)^(-star c.value) =
      Complex.exp (sourceRate c*(h : ℂ))*(x : ℂ)^(-star c.value) := by
  have power : (Real.exp (-h) : ℂ)^(-star c.value) =
      Complex.exp ((-h : ℂ)*(-star c.value)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
      ←Complex.ofReal_log (Real.exp_pos (-h)).le, Real.log_exp]
    simp only [Complex.ofReal_neg]
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Real.exp_pos (-h)).le pos.le,
    power, Complex.ofReal_exp, ←mul_assoc, ←Complex.exp_add]
  congr 2
  unfold sourceRate
  push_cast
  ring

/-- The complete original count has exactly one channel on this collar. -/
theorem elementary_reverse_collar (c : BurnolCompletedMellinCoordinate) {x : ℝ}
    (lower : q/2 < |x|) (upper : |x| ≤ q) :
    elementaryReverseRaw c x = GapEuler.gapMean q c - (1/2 : ℂ)*((|x| : ℝ) : ℂ)^(-star c.value) := by
  have pos : 0 < |x| := (by norm_num : (0:ℝ) < q/2).trans lower
  have index : ⌊q/|x|⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ q/|x|)]
    constructor
    · norm_num
      exact (le_div_iff₀ pos).mpr (by simpa using upper)
    · norm_num
      exact (div_lt_iff₀ pos).mpr (by linarith)
  rw [elementaryReverseRaw, DualSourceRaw.channels, index, Finset.Icc_self, Finset.sum_singleton]
  simp only [Nat.cast_one, one_mul]
  ring

private theorem collar_source_raw (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nn : 0 ≤ h) :
    (collarSource c h : ℝ → ℂ) =ᵐ[volume] collarRaw c h := by
  have elementary := gapState_read c
  change (elementarySource c : ℝ → ℂ) =ᵐ[volume] _ at elementary
  rw [collarSource, elementary_unit_resolvent]
  filter_upwards [Lp.coeFn_sub (GapEuler.gapMean q c •
      (burnolMultiplicativeDilation (-h) C - (Real.exp (-h/2):ℂ) • C))
      (Complex.exp (sourceRate c*(h:ℂ)) • (cut (q*Real.exp h) (elementarySource c) - GapEuler.gapMean q c • C)),
    Lp.coeFn_smul (GapEuler.gapMean q c) (burnolMultiplicativeDilation (-h) C - (Real.exp (-h/2):ℂ) • C),
    Lp.coeFn_sub (burnolMultiplicativeDilation (-h) C) ((Real.exp (-h/2):ℂ) • C),
    Lp.coeFn_smul (Real.exp (-h/2):ℂ) C,
    Lp.coeFn_smul (Complex.exp (sourceRate c*(h:ℂ))) (cut (q*Real.exp h) (elementarySource c) - GapEuler.gapMean q c • C),
    Lp.coeFn_sub (cut (q*Real.exp h) (elementarySource c)) (GapEuler.gapMean q c • C),
    Lp.coeFn_smul (GapEuler.gapMean q c) C,
    originalPhysicalCutoff_coeFn (q*Real.exp h) (elementarySource c), elementary,
    ConstantDual.seed_coeFn, burnolMultiplicativeDilation_coeFn (-h) C,
    (Measure.quasiMeasurePreserving_smul (μ := (volume:Measure ℝ)) (Real.exp_ne_zero (-h))).ae ConstantDual.seed_coeFn]
    with x subAt gAt shellAt scalarAt expAt regularAt gcAt cutAt elemAt cAt dilAt movedAt
  change C (Real.exp (-h)*x)=ConstantDual.seedRaw (Real.exp (-h)*x) at movedAt
  simp only [subAt, gAt, shellAt, scalarAt, expAt, regularAt, gcAt, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, dilAt, burnolL2RawNormalizedDilation, movedAt, cAt, cutAt, ConstantDual.seedRaw]
  have landing : |Real.exp (-h)*x| ≤ q ↔ |x| ≤ q*Real.exp h := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _), Real.exp_neg, ←div_eq_inv_mul,
      div_le_iff₀ (Real.exp_pos _)]
  have rge : q ≤ q*Real.exp h := le_mul_of_one_le_right (by norm_num) (Real.one_le_exp_iff.mpr nn)
  by_cases inside : |x| ≤ q
  · have outer : |x| ≤ q*Real.exp h := inside.trans rge
    rw [if_pos inside, if_pos (landing.mpr outer),
      indicator_of_mem (show x∈symmetricInterval (q*Real.exp h) from abs_le.mp outer), elemAt, gapState_raw_gap c (abs_le.mp inside),
      collarRaw, if_neg (fun active => (not_lt_of_ge inside) active.1)]
    ring
  · have outside : q < |x| := lt_of_not_ge inside
    rw [if_neg inside]
    by_cases outer : |x| ≤ q*Real.exp h
    · rw [indicator_of_mem (show x∈symmetricInterval (q*Real.exp h) from abs_le.mp outer), if_pos (landing.mpr outer),
        elemAt, gap_raw_absolute c x, gapState_raw_tail c outside, collarRaw, if_pos ⟨outside,outer⟩]
      ring
    · rw [indicator_of_notMem (show x∉symmetricInterval (q*Real.exp h) from fun member => outer (abs_le.mpr member)),
        if_neg (fun member => outer (landing.mp member)), collarRaw,
        if_neg (fun active => outer active.2)]
      ring

/-- Exact n=1 incidence generates the whole outward vector, including its unit and power feet. -/
theorem elementary_reverse_exterior (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (h : ℝ) (nn : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    burnolMultiplicativeDilation (-h) (elementaryReverseSource c zero) -
      cut q (burnolMultiplicativeDilation (-h) (elementaryReverseSource c zero)) = collarSource c h := by
  let Z := elementaryReverseSource c zero
  let moved := burnolMultiplicativeDilation (-h) Z
  have source := (Measure.quasiMeasurePreserving_smul (μ := (volume:Measure ℝ))
    (Real.exp_ne_zero (-h))).ae (elementary_reverse_raw c zero)
  have half : (1/2:ℝ) ≤ Real.exp (-h) := by
    have order := Real.exp_le_exp.mpr (neg_le_neg bounded)
    simpa only [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<2), one_div] using order
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub moved (cut q moved), originalPhysicalCutoff_coeFn q moved,
    burnolMultiplicativeDilation_coeFn (-h) Z, source, collar_source_raw c h nn]
    with x difference cutoff dilation raw actual
  change (moved-cut q moved:BurnolL2) x = _
  rw [difference, Pi.sub_apply, cutoff, actual]
  by_cases inside : |x| ≤ q
  · rw [indicator_of_mem (show x∈symmetricInterval q from abs_le.mp inside), sub_self, collarRaw,
      if_neg (fun active => (not_lt_of_ge inside) active.1)]
  · have outside : q < |x| := lt_of_not_ge inside
    have absolute : |Real.exp (-h)*x| = Real.exp (-h)*|x| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have lower : q/2 < |Real.exp (-h)*x| := by
      rw [absolute]
      nlinarith [Real.exp_pos (-h)]
    have landing : |Real.exp (-h)*x| ≤ q ↔ |x| ≤ q*Real.exp h := by
      rw [absolute, Real.exp_neg, ←div_eq_inv_mul, div_le_iff₀ (Real.exp_pos _)]
    rw [indicator_of_notMem (show x∉symmetricInterval q from fun member => inside (abs_le.mpr member)), sub_zero, dilation]
    change (Real.exp (-h/2):ℂ)*Z (Real.exp (-h)*x) = _
    change Z (Real.exp (-h)*x) = elementaryReverseRaw c (Real.exp (-h)*x) at raw
    rw [raw]
    by_cases outer : |x| ≤ q*Real.exp h
    · rw [elementary_reverse_collar c lower (landing.mpr outer), absolute, collarRaw, if_pos ⟨outside,outer⟩,
        mul_sub]
      linear_combination -(1/2:ℂ)*(power_scaling c h |x| ((by norm_num : (0:ℝ)<q).trans outside))
    · have empty : DualSourceRaw.channels (Real.exp (-h)*x) = ∅ := by
        have index : ⌊q/|Real.exp (-h)*x|⌋₊ = 0 :=
          Nat.floor_eq_zero.mpr ((div_lt_one ((by norm_num : (0:ℝ)<q/2).trans lower)).mpr
            (lt_of_not_ge (fun covered => outer (landing.mp covered))))
        rw [DualSourceRaw.channels,index]
        norm_num
      rw [elementaryReverseRaw, empty, Finset.sum_empty, neg_zero, mul_zero, collarRaw,
        if_neg (fun active => outer active.2)]

private theorem cutoff_integrable (radius : ℝ) (value : BurnolL2) :
    Integrable (cut radius value : ℝ → ℂ) := by
  have : IsFiniteMeasure (volume.restrict (symmetricInterval radius)) :=
    ⟨by simpa only [Measure.restrict_apply_univ, symmetricInterval] using
      (measure_Icc_lt_top (a := -radius) (b := radius))⟩
  have localValue : Integrable (value:ℝ→ℂ) (volume.restrict (symmetricInterval radius)) :=
    ((Lp.memLp value).mono_measure Measure.restrict_le_self).integrable (by norm_num : (1:ENNReal)≤2)
  exact ((integrable_indicator_iff (measurableSet_symmetricInterval radius)).mpr localValue).congr
    (originalPhysicalCutoff_coeFn radius value).symm

private theorem dilation_integrable (value : BurnolL2) (hi : Integrable (value:ℝ→ℂ)) (h : ℝ) :
    Integrable (burnolMultiplicativeDilation h value : ℝ→ℂ) :=
  (((integrable_comp_mul_left_iff (value:ℝ→ℂ) (Real.exp_ne_zero h)).mpr hi).const_mul
    (Real.exp (h/2):ℂ)).congr (burnolMultiplicativeDilation_coeFn h value).symm

private theorem dilation_mass (value : BurnolL2) (h : ℝ) :
    (∫ x:ℝ, burnolMultiplicativeDilation h value x) =
      (Real.exp (-h/2):ℂ)*(∫ x:ℝ, value x) := by
  rw [integral_congr_ae (burnolMultiplicativeDilation_coeFn h value)]
  unfold burnolL2RawNormalizedDilation
  rw [integral_const_mul, Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr (Real.exp_pos h)),
    Complex.real_smul, Complex.ofReal_inv, ←mul_assoc]
  congr 1
  rw [←Complex.ofReal_inv, ←Complex.ofReal_mul, ←Real.exp_neg, ←Real.exp_add]
  congr 2
  ring

private theorem collar_integrable (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (h : ℝ) (nn : 0≤h) (bounded : h≤Real.log 2) : Integrable (collarSource c h : ℝ→ℂ) := by
  rw [←elementary_reverse_exterior c zero h nn bounded]
  have hi : Integrable (elementaryReverseSource c zero : ℝ→ℂ) := by
    rw [←elementary_reverse_support c zero]
    exact cutoff_integrable q _
  exact ((dilation_integrable _ hi (-h)).sub (cutoff_integrable q _)).congr (Lp.coeFn_sub _ _).symm

private theorem even_half_mass (radius : ℝ) (pos : 0<radius) (f:ℝ→ℂ)
    (hi : IntegrableOn f (symmetricInterval radius)) (even : ∀x, f (-x)=f x) :
    (∫ x in symmetricInterval radius, f x) = 2*∫x in Ioc 0 radius, f x := by
  have first := hi.mono_set (show Ioc (-radius) 0 ⊆ symmetricInterval radius by
    rintro x ⟨lo,up⟩; exact ⟨lo.le,up.trans pos.le⟩)
  have second := hi.mono_set (show Ioc 0 radius ⊆ symmetricInterval radius by
    rintro x ⟨lo,up⟩; exact ⟨by linarith,up⟩)
  have split := setIntegral_union (Ioc_disjoint_Ioc_of_le (a := -radius) (b := (0:ℝ)) (c := 0) (d := radius) le_rfl)
    measurableSet_Ioc first second
  rw [Ioc_union_Ioc_eq_Ioc (by linarith : -radius≤(0:ℝ)) pos.le] at split
  have reflected : (∫x in Ioc (-radius) 0, f x) = ∫x in Ioc 0 radius, f x := by
    rw [←intervalIntegral.integral_of_le (by linarith : -radius≤(0:ℝ)), ←intervalIntegral.integral_of_le pos.le]
    have result := intervalIntegral.integral_comp_neg (f:=f) (a:=(0:ℝ)) (b:=radius)
    rw [show (fun x=>f (-x))=f from funext even,neg_zero] at result
    exact result.symm
  change (∫x in Icc (-radius) radius, f x)=_
  rw [integral_Icc_eq_integral_Ioc, split,reflected]
  ring

private theorem gap_moment (c : BurnolCompletedMellinCoordinate) :
    burnolRadiusMellinGapMoment q (star c.value) = (2*q:ℝ)*GapEuler.gapMean q c := by
  have ne : 1-star c.value ≠ 0 := by
    intro hz
    have r := congrArg Complex.re (sub_eq_zero.mp hz)
    simp only [one_re,star_def,conj_re] at r
    linarith [c.belowOne]
  have source := GapEuler.gapMean_primitive q (by norm_num) c
  have power : (q:ℂ)^(1-star c.value)=(q:ℂ)^(-star c.value)*(q:ℂ) := by
    rw [show (1:ℂ)-star c.value = -star c.value+1 by ring,
      Complex.cpow_add _ _ (by norm_num : (q:ℂ)≠0),Complex.cpow_one]
  unfold burnolRadiusMellinGapMoment
  rw [power,div_eq_iff ne]
  norm_num at source ⊢
  linear_combination -(1/2:ℂ)*source

/-- The whole exterior mass includes the actual constant and power terms; neither is discarded. -/
theorem collar_source_mass (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (bounded:h≤Real.log 2) :
    (∫ x:ℝ, collarSource c h x) = (2*q:ℝ)*GapEuler.gapMean q c *
      (Complex.exp (sourceRate c*(h:ℂ))-(Real.exp (-h/2):ℂ)) := by
  let R:=q*Real.exp h
  have rp : 0<R := by dsimp [R]; positivity
  have ordered : q≤R := le_mul_of_one_le_right (by norm_num) (Real.one_le_exp_iff.mpr nn)
  have hi := (collar_integrable c zero h nn bounded).congr (collar_source_raw c h nn)
  have supported : (symmetricInterval R).indicator (collarRaw c h) = collarRaw c h := by
    funext x
    by_cases hx:x∈symmetricInterval R
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx,collarRaw,if_neg (fun active=>hx (abs_le.mp active.2))]
  have whole : (∫x:ℝ,collarRaw c h x) = ∫x in symmetricInterval R,collarRaw c h x := by
    rw [←integral_indicator (measurableSet_symmetricInterval R),supported]
  have half : (∫x in Ioc 0 R,collarRaw c h x) =
      ∫x in Ioc q R, (Real.exp (-h/2):ℂ)*GapEuler.gapMean q c -
        Complex.exp (sourceRate c*(h:ℂ))*(1/2:ℂ)*(x:ℂ)^(-star c.value) := by
    rw [setIntegral_congr_fun measurableSet_Ioc (show EqOn (collarRaw c h)
      ((Ioc q R).indicator (fun x:ℝ=>(Real.exp (-h/2):ℂ)*GapEuler.gapMean q c-
        Complex.exp (sourceRate c*(h:ℂ))*(1/2:ℂ)*(x:ℂ)^(-star c.value))) (Ioc 0 R) from by
          intro x hx
          have up : x≤q*Real.exp h := hx.2
          by_cases lo : q<x
          · rw [collarRaw,abs_of_pos hx.1,if_pos ⟨lo,up⟩,indicator_of_mem (show x∈Ioc q R from ⟨lo,hx.2⟩)]
          · rw [collarRaw,abs_of_pos hx.1,if_neg (fun active=>lo active.1),indicator_of_notMem (show x∉Ioc q R from fun member=>lo member.1)]),
      integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr (Ioc_subset_Ioc (by norm_num : (0:ℝ)≤q) le_rfl)]
  have exponent : -1<(-star c.value).re := by simp only [neg_re,star_def,conj_re]; linarith [c.belowOne]
  have powers := (intervalIntegrable_iff_integrableOn_Ioc_of_le ordered).mp
    (intervalIntegral.intervalIntegrable_cpow' exponent (a:=q) (b:=R))
  have integralPower : (∫x in Ioc q R,(x:ℂ)^(-star c.value)) =
      burnolRadiusMellinGapMoment R (star c.value)-burnolRadiusMellinGapMoment q (star c.value) := by
    rw [←intervalIntegral.integral_of_le ordered,integral_cpow (Or.inl exponent)]
    unfold burnolRadiusMellinGapMoment
    rw [show -star c.value+1=1-star c.value by ring]
    ring
  have scaled := burnolMellinGapMoment_scaled (by norm_num : (0:ℝ)<q) (star c.value) (-h)
  simp only [neg_neg,Complex.ofReal_neg] at scaled
  have exponential : Complex.exp (sourceRate c*(h:ℂ))*Complex.exp ((h:ℂ)*(1-star c.value)) =
      (Real.exp (h/2):ℂ) := by
    rw [←Complex.exp_add,Complex.ofReal_exp]
    congr 1
    unfold sourceRate
    push_cast
    ring
  have constantInt : IntegrableOn (fun _:ℝ=>(Real.exp (-h/2):ℂ)*GapEuler.gapMean q c) (Ioc q R) volume :=
    integrableOn_const (by exact measure_Ioc_lt_top.ne)
  rw [integral_congr_ae (collar_source_raw c h nn),whole,
    even_half_mass R rp _ hi.integrableOn (by intro x; simp [collarRaw,abs_neg]),half,
    integral_sub (μ:=volume.restrict (Ioc q R)) constantInt
      (powers.const_mul _)]
  simp only [integral_const_mul]
  rw [integralPower,scaled,gap_moment]
  rw [setIntegral_const]
  have halfExp : (Real.exp h:ℂ)*(Real.exp (-h/2):ℂ)=(Real.exp (h/2):ℂ) := by
    rw [←Complex.ofReal_mul,←Real.exp_add]
    congr 2
    ring
  simp only [Measure.real, Real.volume_Ioc]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr ordered)]
  simp only [R,Complex.ofReal_mul]
  norm_num at exponential halfExp ⊢
  linear_combination -(1/2:ℂ)*GapEuler.gapMean q c*exponential + (1/2:ℂ)*GapEuler.gapMean q c*halfExp


private theorem K_gap (c : BurnolCompletedMellinCoordinate) :
    (sourceKernel c : ℝ→ℂ) =ᵐ[volume.restrict (symmetricInterval q)] fun _=>positionMean c := by
  rw [sourceKernel_original]
  filter_upwards [ae_restrict_of_ae (burnolRieszState_ae_raw c),ae_restrict_mem (measurableSet_symmetricInterval q)]
    with x read inside
  rw [read,position_raw,if_pos inside,add_zero]

private theorem gap_pair (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (supported : cut q value=value) :
    inner ℂ (sourceKernel c) value=star (positionMean c)*(∫x:ℝ,value x) := by
  have gap := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (K_gap c)
  have read := originalPhysicalCutoff_coeFn q value
  rw [supported] at read
  rw [L2.inner_def,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [gap,read] with x actual support
  by_cases inside:x∈symmetricInterval q
  · rw [actual inside,RCLike.inner_apply]
    simp only [starRingEnd_apply]
    ring
  · rw [support,indicator_of_notMem inside]
    simp

private theorem supported_mass (value : BurnolL2) (supported : cut q value=value) :
    (∫x:ℝ,value x) = (1/2:ℂ)*burnolQuarterMeanCoefficient (burnolQuarterRestriction value) := by
  have innerRead := ContinuousLinearMap.adjoint_inner_left burnolQuarterRestriction value (intervalConstant q)
  change inner ℂ C value = _ at innerRead
  have integralRead : (∫x:ℝ,value x) = ∫x in symmetricInterval q,burnolQuarterRestriction value x := by
    calc
      _ = ∫x:ℝ,burnolQuarterZeroExtension (burnolQuarterRestriction value) x := by
        change (∫x:ℝ,value x) = ∫x:ℝ,cut q value x
        rw [supported]
      _ = _ := by rw [integral_congr_ae (burnolQuarterZeroExtension_coe _),
        integral_indicator (measurableSet_symmetricInterval q)]
  rw [integralRead]
  have read : (∫x in symmetricInterval q,burnolQuarterRestriction value x) =
      inner ℂ (intervalConstant q) (burnolQuarterRestriction value) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [intervalConstant_coeFn q] with x constant
    rw [constant]
    simp [RCLike.inner_apply]
  rw [read]
  unfold burnolQuarterMeanCoefficient
  have normC : ((‖intervalConstant q‖^2:ℝ):ℂ)=(1/2:ℂ) := by
    rw [Complex.ofReal_pow,burnolIntervalConstant_norm_sq (by norm_num : (0:ℝ)<q)]
    norm_num
  rw [normC]
  ring

private theorem constant_mass : (∫x:ℝ,C x)=(1/2:ℂ) := by
  have read : (C:ℝ→ℂ)=ᵐ[volume] (symmetricInterval q).indicator (fun _:ℝ=>(1:ℂ)) := by
    filter_upwards [ConstantDual.seed_coeFn] with x source
    rw [source,ConstantDual.seedRaw]
    by_cases inside:x∈symmetricInterval q
    · rw [indicator_of_mem inside,if_pos (abs_le.mpr inside)]
    · rw [indicator_of_notMem inside,if_neg (fun hx=>inside (abs_le.mp hx))]
  rw [integral_congr_ae read,integral_indicator (measurableSet_symmetricInterval q),integral_const]
  norm_num [symmetricInterval,real_smul]

/-- The full count's mean is kept in the primitive gap contribution. -/
def reverseMean (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) : ℂ :=
  burnolQuarterMeanCoefficient (burnolQuarterRestriction (elementaryReverseSource c zero))

/-- This computes the K-cotest of the actual zero-owned column, rather than changing its name. -/
theorem elementary_reverse_boundary_price (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (bounded:h≤Real.log 2) :
    inner ℂ (sourceKernel c) (finiteBoundaryAction c h (elementaryReverseSource c zero)) =
      ((pairedMellinTranslationCharacter c.value h-
          ((Real.exp (h/2):ℂ)+(Real.exp (-h/2):ℂ))/2)*reverseMean c zero +
        (2*q:ℝ)*GapEuler.gapMean q c*(Complex.exp (sourceRate c*(h:ℂ))-(Real.exp (-h/2):ℂ))) *
        inner ℂ (sourceKernel c) C - (1/2:ℂ)*inner ℂ (sourceKernel c) (collarSource c h) := by
  let Z:=elementaryReverseSource c zero
  have zs : cut q Z=Z := elementary_reverse_support c zero
  have zi : Integrable (Z:ℝ→ℂ) := by rw [←zs];exact cutoff_integrable q Z
  have zm : (∫x:ℝ,Z x)=(1/2:ℂ)*reverseMean c zero := supported_mass Z zs
  have cs : cut q C=C := by
    change burnolQuarterZeroExtension (burnolQuarterRestriction (burnolQuarterZeroExtension (intervalConstant q))) = _
    rw [burnolQuarterRestriction_zeroExtension]
    rfl
  have kc : inner ℂ (sourceKernel c) C=star (positionMean c)*(1/2:ℂ) := by
    rw [gap_pair c C cs,constant_mass]
  have inwardSupport : cut q (burnolMultiplicativeDilation h Z)=burnolMultiplicativeDilation h Z := by
    have source : burnolQuarterZeroExtension (burnolQuarterRestriction Z)=Z := zs
    rw [←source]
    exact intervalDilation_cutoff_self _ h q
      (mul_le_of_le_one_right (by norm_num : (0:ℝ)≤q) (Real.exp_le_one_iff.mpr (by linarith)))
  have inward := gap_pair c (burnolMultiplicativeDilation h Z) inwardSupport
  rw [dilation_mass,zm] at inward
  have split := elementary_reverse_exterior c zero h nn bounded
  have cutSupport : cut q (cut q (burnolMultiplicativeDilation (-h) Z))=
      cut q (burnolMultiplicativeDilation (-h) Z) := by
    change burnolQuarterZeroExtension (burnolQuarterRestriction
      (burnolQuarterZeroExtension (burnolQuarterRestriction _))) = _
    rw [burnolQuarterRestriction_zeroExtension]
    rfl
  have cutPrice := gap_pair c (cut q (burnolMultiplicativeDilation (-h) Z)) cutSupport
  have massSplit : (∫x:ℝ,cut q (burnolMultiplicativeDilation (-h) Z) x) =
      (Real.exp (h/2):ℂ)*(1/2:ℂ)*reverseMean c zero-
        (2*q:ℝ)*GapEuler.gapMean q c*(Complex.exp (sourceRate c*(h:ℂ))-(Real.exp (-h/2):ℂ)) := by
    have integralEq:=congrArg (fun value:BurnolL2=>∫x:ℝ,value x) split
    rw [integral_congr_ae (Lp.coeFn_sub _ _)] at integralEq
    simp only [Pi.sub_apply] at integralEq
    rw [integral_sub (dilation_integrable Z zi (-h))
      (cutoff_integrable q _),dilation_mass,neg_neg,zm,collar_source_mass c zero h nn bounded] at integralEq
    linear_combination -integralEq
  rw [massSplit] at cutPrice
  have outward : inner ℂ (sourceKernel c) (burnolMultiplicativeDilation (-h) Z) =
      inner ℂ (sourceKernel c) (cut q (burnolMultiplicativeDilation (-h) Z)) +
        inner ℂ (sourceKernel c) (collarSource c h) := by
    have price:=congrArg (inner ℂ (sourceKernel c)) split
    rw [inner_sub_right] at price
    linear_combination price
  unfold finiteBoundaryAction
  rw [inner_sub_right,inner_smul_right,inner_smul_right,inner_add_right]
  rw [gap_pair c Z zs,zm,inward,outward,cutPrice,kc]
  ring

/-- The original Ward consumes the calculated n=1 collar price and retains both full B-loss outputs. -/
theorem original_core_collar_ward (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (bounded:h≤Real.log 2) :
    inner ℂ (KCountingGram.value c) (sourceCore c h) =
      ((pairedMellinTranslationCharacter c.value h-
          ((Real.exp (h/2):ℂ)+(Real.exp (-h/2):ℂ))/2)*reverseMean c zero +
        (2*q:ℝ)*GapEuler.gapMean q c*(Complex.exp (sourceRate c*(h:ℂ))-(Real.exp (-h/2):ℂ))) *
        inner ℂ (sourceKernel c) C - (1/2:ℂ)*inner ℂ (sourceKernel c) (collarSource c h) -
      (1/2:ℂ)*(inner ℂ (sourceKernel c) (FullUnit.fullReverse c h 1) -
        inner ℂ (sourceKernel c) (fourierL2 (FullUnit.fullForward c h 0))) := by
  rw [original_core_arithmetic_ward c zero h nn,coreReverseSource,
    inner_sub_right,inner_smul_right,inner_sub_right,elementary_reverse_boundary_price c zero h nn bounded]

end OriginalKElementaryArithmeticAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
