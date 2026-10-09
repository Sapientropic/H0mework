import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceRadiusClosedJointCost
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceCoreFormParseval
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceLowerStripRadiusPrice
open MeasureTheory Filter SourceJointResidualEnergy SourceFourPoleEnergyClosed SourceResolventBandLimit
open scoped Topology InnerProductSpace

section Finite
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Fintype ι]

private def freq (a : ι → ℝ) (u : ι → E) (μ w : ℝ) : E := ∑ i,pole μ (a i) w • u i
private def time (a : ι → ℝ) (u : ι → E) (μ t : ℝ) : E :=
  ∑ i,Complex.exp ((-(μ : ℂ)-Complex.I*(a i : ℂ))*(t : ℂ)) • u i
private def fgram (a : ι → ℝ) (u : ι → E) (μ w : ℝ) : ℂ :=
  ∑ i,∑ j,star (pole μ (a i) w)*pole μ (a j) w*inner ℂ (u i) (u j)
private def tgram (a : ι → ℝ) (u : ι → E) (μ t : ℝ) : ℂ :=
  ∑ i,∑ j,Complex.exp (-gap μ (a i) (a j)*(t : ℂ))*inner ℂ (u i) (u j)

omit [CompleteSpace E] in
private theorem pair_sum (u : ι → E) (c : ι → ℂ) :
    inner ℂ (∑ i,c i • u i) (∑ j,c j • u j)=
      ∑ i,∑ j,star (c i)*c j*inner ℂ (u i) (u j) := by
  simp only [sum_inner,inner_sum,inner_smul_left,inner_smul_right,starRingEnd_apply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [CompleteSpace E] in
private theorem frequency_value (a : ι → ℝ) (u : ι → E) (μ w : ℝ) :
    (fgram a u μ w).re=‖freq a u μ w‖^2 := by
  rw [←inner_self_eq_norm_sq (𝕜 := ℂ)]
  unfold freq fgram
  rw [pair_sum]
  rfl

omit [CompleteSpace E] in
private theorem time_value (a : ι → ℝ) (u : ι → E) (μ t : ℝ) :
    (tgram a u μ t).re=‖time a u μ t‖^2 := by
  rw [←inner_self_eq_norm_sq (𝕜 := ℂ)]
  unfold time tgram
  rw [pair_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.star_def,←Complex.exp_conj,←Complex.exp_add]
  congr 2
  simp only [gap,map_mul,map_sub,map_neg,Complex.conj_ofReal,Complex.conj_I]
  ring

private theorem exp_integrable (c : ℂ) (hc : c.re<0) :
    IntegrableOn (fun t : ℝ => Complex.exp (c*(t : ℂ))) (Set.Ioi 0) :=
  integrableOn_exp_mul_complex_Ioi hc 0

private theorem exp_integral (c : ℂ) (hc : c.re<0) :
    (∫ t : ℝ in Set.Ioi 0,Complex.exp (c*(t : ℂ)))= -c⁻¹ := by
  rw [integral_exp_mul_complex_Ioi hc 0]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_div,neg_div]

omit [CompleteSpace E] in
private theorem frequency_integrable (a : ι → ℝ) (u : ι → E) (μ : ℝ) (hμ : 0<μ) :
    Integrable (fun w : ℝ => ‖freq a u μ w‖^2) := by
  have h : Integrable (fgram a u μ) := integrable_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (two_pole_integrable μ (a i) (a j) hμ).mul_const _))
  have hr := h.re
  change Integrable (fun w => (fgram a u μ w).re) at hr
  simpa only [frequency_value] using hr

omit [CompleteSpace E] in
private theorem time_integrable (a : ι → ℝ) (u : ι → E) (μ : ℝ) (hμ : 0<μ) :
    IntegrableOn (fun t : ℝ => ‖time a u μ t‖^2) (Set.Ioi 0) := by
  have h : IntegrableOn (tgram a u μ) (Set.Ioi 0) := integrable_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => (exp_integrable (-gap μ (a i) (a j))
      (by simp [gap];linarith)).mul_const _))
  have hr := h.re
  change IntegrableOn (fun t => (tgram a u μ t).re) (Set.Ioi 0) at hr
  simpa only [time_value] using hr

omit [CompleteSpace E] in
private theorem parseval (a : ι → ℝ) (u : ι → E) (μ : ℝ) (hμ : 0<μ) :
    (∫ w : ℝ,‖freq a u μ w‖^2)=2*Real.pi*(∫ t : ℝ in Set.Ioi 0,‖time a u μ t‖^2) := by
  have he : (∫ w : ℝ,fgram a u μ w)=(2*Real.pi : ℂ)*(∫ t : ℝ in Set.Ioi 0,tgram a u μ t) := by
    unfold fgram tgram
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      (two_pole_integrable μ (a i) (a j) hμ).mul_const _)),
      integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      (exp_integrable (-gap μ (a i) (a j)) (by simp [gap];linarith)).mul_const _)),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => (two_pole_integrable μ (a i) (a j) hμ).mul_const _),
      integral_finsetSum _ (fun j _ => (exp_integrable (-gap μ (a i) (a j))
        (by simp [gap];linarith)).mul_const _),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_mul_const,integral_mul_const,exp_integral _ (by simp [gap];linarith)]
    change twoPole μ (a i) (a j)*_= _
    rw [two_pole_closed μ _ _ hμ,inv_neg,neg_neg]
    ring
  have hf : Integrable (fgram a u μ) := integrable_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (two_pole_integrable μ (a i) (a j) hμ).mul_const _))
  have ht : IntegrableOn (tgram a u μ) (Set.Ioi 0) := integrable_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => (exp_integrable (-gap μ (a i) (a j))
      (by simp [gap];linarith)).mul_const _))
  have h := congrArg Complex.re he
  have hr1 : (∫ w : ℝ,fgram a u μ w).re=∫ w : ℝ,(fgram a u μ w).re := (integral_re hf).symm
  have hr2 : (∫ t : ℝ in Set.Ioi 0,tgram a u μ t).re=∫ t : ℝ in Set.Ioi 0,(tgram a u μ t).re := (integral_re ht).symm
  rw [hr1,Complex.mul_re,show (2*Real.pi : ℂ).re=2*Real.pi by simp,
    show (2*Real.pi : ℂ).im=0 by simp,zero_mul,sub_zero,hr2] at h
  simpa only [frequency_value,time_value] using h

omit [CompleteSpace E] in
private theorem integral_cauchy (c : ℝ → ℂ) (y : ℝ → E) (M : Measure ℝ)
    (hc : AEStronglyMeasurable c M) (hy : AEStronglyMeasurable y M)
    (hc2 : Integrable (fun t => ‖c t‖^2) M) (hy2 : Integrable (fun t => ‖y t‖^2) M) :
    ‖∫ t,c t • y t ∂M‖^2  ≤  (∫ t,‖c t‖^2 ∂M)*(∫ t,‖y t‖^2 ∂M) := by
  have hcL := (memLp_two_iff_integrable_sq_norm hc).mpr hc2
  have hyL := (memLp_two_iff_integrable_sq_norm hy).mpr hy2
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall (fun t => norm_nonneg (c t))) (Eventually.of_forall (fun t => norm_nonneg (y t)))
    (by simpa using hcL.norm) (by simpa using hyL.norm)
  simp only [Real.rpow_two,←Real.sqrt_eq_rpow] at hh
  have hn : ‖∫ t,c t • y t ∂M‖  ≤  Real.sqrt (∫ t,‖c t‖^2 ∂M)*Real.sqrt (∫ t,‖y t‖^2 ∂M) := by
    have h := norm_integral_le_integral_norm (fun t => c t • y t) (μ := M)
    simp only [norm_smul] at h
    exact h.trans hh
  have h := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [mul_pow,Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _)),
    Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))] at h
  exact h

private theorem laplace (a : ι → ℝ) (u : ι → E) (ν μ w : ℝ) (hμ : 0<μ) :
    (∫ t : ℝ in Set.Ioi 0,Complex.exp ((-((μ-ν) : ℂ)+Complex.I*(w : ℂ))*(t : ℂ)) • time a u ν t)=
      (-Complex.I) • freq a u μ w := by
  have he (t : ℝ) : Complex.exp ((-((μ-ν) : ℂ)+Complex.I*(w : ℂ))*(t : ℂ)) • time a u ν t=
      ∑ i,Complex.exp ((-(μ : ℂ)+Complex.I*((w : ℂ)-(a i : ℂ)))*(t : ℂ)) • u i := by
    unfold time
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul,←Complex.exp_add]
    congr 2
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => (exp_integrable
    (-(μ : ℂ)+Complex.I*((w : ℂ)-(a i : ℂ))) (by simp;linarith)).smul_const (u i))]
  unfold freq
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_const,exp_integral _ (by simp;linarith),smul_smul]
  congr 1
  have he : -(μ : ℂ)+Complex.I*((w : ℂ)-(a i : ℂ))=(-Complex.I)*((a i : ℂ)-line μ w) := by
    unfold line
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [he,mul_inv,inv_neg,Complex.inv_I]
  simp only [neg_neg,pole,neg_mul]

private theorem finite_strip_point (a : ι → ℝ) (u : ι → E) (ν μ : ℝ)
    (hν : 0<ν) (hδ : ν<μ) (w : ℝ) :
    ‖freq a u μ w‖^2  ≤  1/(4*Real.pi*(μ-ν))*(∫ v : ℝ,‖freq a u ν v‖^2) := by
  have hμ : 0<μ := hν.trans hδ
  let c := fun t : ℝ => Complex.exp ((-((μ-ν) : ℂ)+Complex.I*(w : ℂ))*(t : ℂ))
  have hc2 (t : ℝ) : ‖c t‖^2=Real.exp (-2*(μ-ν)*t) := by
    simp only [c,Complex.norm_exp,Complex.mul_re,Complex.add_re,Complex.neg_re,Complex.ofReal_re,
      Complex.sub_re,Complex.I_re,Complex.I_im,Complex.ofReal_im,zero_mul,one_mul,add_zero,sub_zero]
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  have hcI : IntegrableOn (fun t : ℝ => ‖c t‖^2) (Set.Ioi 0) := by
    simp_rw [hc2]
    exact integrableOn_exp_mul_Ioi (by linarith : -2*(μ-ν)<0) 0
  have hcE : (∫ t : ℝ in Set.Ioi 0,‖c t‖^2)=1/(2*(μ-ν)) := by
    simp_rw [hc2]
    rw [integral_exp_mul_Ioi (by linarith : -2*(μ-ν)<0) 0]
    simp only [mul_zero,Real.exp_zero,neg_mul,div_neg]
    ring
  have hy : Continuous (time a u ν) := by unfold time;fun_prop
  have hh := integral_cauchy c (time a u ν) (volume.restrict (Set.Ioi 0))
    (by dsimp only [c];fun_prop) (hy.aestronglyMeasurable) hcI (time_integrable a u ν hν)
  rw [laplace a u ν μ w hμ,norm_smul,norm_neg,Complex.norm_I,one_mul,hcE] at hh
  have hp := parseval a u ν hν
  have hpi := Real.pi_pos
  have hd : 0<μ-ν := sub_pos.mpr hδ
  exact hh.trans_eq (by rw [hp];field_simp;ring)

omit [CompleteSpace E] in
private theorem finite_strip_integral (a : ι → ℝ) (u : ι → E) (ν μ : ℝ)
    (hν : 0<ν) (hδ : ν<μ) :
    (∫ w : ℝ,‖freq a u μ w‖^2)  ≤  ∫ w : ℝ,‖freq a u ν w‖^2 := by
  have hμ : 0<μ := hν.trans hδ
  have he (t : ℝ) : time a u μ t=
      Complex.exp (-((μ-ν) : ℂ)*(t : ℂ)) • time a u ν t := by
    unfold time
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul,←Complex.exp_add]
    congr 2
    ring
  have hb (t : ℝ) (ht : t∈Set.Ioi (0 : ℝ)) : ‖time a u μ t‖^2  ≤  ‖time a u ν t‖^2 := by
    have hc : ‖Complex.exp (-((μ-ν) : ℂ)*(t : ℂ))‖ ≤ 1 := by
      rw [Complex.norm_exp]
      have hx : (-((μ-ν) : ℂ)*(t : ℂ)).re= -(μ-ν)*t := by simp
      rw [hx]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) ht.le)
    rw [he,norm_smul]
    have hn := mul_le_mul_of_nonneg_right hc (norm_nonneg (time a u ν t))
    rw [one_mul] at hn
    exact pow_le_pow_left₀ (by positivity) hn 2
  rw [parseval a u μ hμ,parseval a u ν hν]
  exact mul_le_mul_of_nonneg_left
    (setIntegral_mono_on (time_integrable a u μ hμ) (time_integrable a u ν hν) measurableSet_Ioi hb)
    (by positivity)

end Finite

open GaussCoreHilbert GaussDiagonalHistory GaussUnitaryHistory
open FullYSourceResolventGraphSplice SourceInverseElectricMomentChannels
open SourceRadiusPairedScalarPrice SourceRadiusClosedJointCost SourceRelativePowerTail
abbrev Op := H →L[ℂ] H
attribute [local irreducible] radiusBand radiusMoment finiteResolvent

/-- The original two spectral half-planes are independent legs of one F. -/
def stripMoment (advanced : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (x : H) (w : ℝ) : ℝ :=
  radiusMoment m ell (finiteResolvent F (if advanced then star (line μ w) else line μ w) x)

def stripEnergy (advanced : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (x : H) : ℝ :=
  ∫ w : ℝ,stripMoment advanced m ell F μ x w

private theorem band_positive (m ell : ℕ) : 0 ≤ radiusBand m ell := by
  unfold radiusBand
  exact Finset.sum_nonneg (fun j _ => CStarAlgebra.pow_nonneg source_complement_nonnegative j)

private def sqrtOp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E) : E →L[ℂ] E := CFC.sqrt A

private theorem positive_root_square {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E) (hA : 0 ≤ A) (x : E) : (inner ℂ x (A x)).re=‖sqrtOp A x‖^2 := by
  have hS : 0 ≤ sqrtOp A := CFC.sqrt_nonneg _
  have hs : ∀ p q,inner ℂ (sqrtOp A p) q=inner ℂ p (sqrtOp A q) :=
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hS).isSymmetric
  have hss : sqrtOp A*sqrtOp A=A := CFC.sqrt_mul_sqrt_self _ hA
  conv_lhs => rw [←hss]
  change (inner ℂ x (sqrtOp A (sqrtOp A x))).re=_
  rw [←hs]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

private def bandRoot (m ell : ℕ) : Op := sqrtOp (radiusBand m ell)

private theorem moment_square (m ell : ℕ) (x : H) : radiusMoment m ell x=‖bandRoot m ell x‖^2 := by
  unfold radiusMoment
  exact positive_root_square _ (band_positive m ell) x

private theorem moment_nonnegative (advanced : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (x : H) (w : ℝ) :
    0 ≤ stripMoment advanced m ell F μ x w := by
  unfold stripMoment
  rw [moment_square]
  exact sq_nonneg _

private theorem source_norm (advanced : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (x : H) (w : ℝ) :
    stripMoment advanced m ell F μ x w=
      ‖freq (fun i : Channel F => if advanced then -channelValue F i else channelValue F i)
        (fun i => bandRoot m ell (channel F i x)) μ (if advanced then -w else w)‖^2 := by
  cases advanced
  · unfold stripMoment
    change radiusMoment m ell (finiteResolvent F (line μ w) x)=
      ‖freq (channelValue F) (fun i => bandRoot m ell (channel F i x)) μ w‖^2
    rw [moment_square,actual_resolvent_spectral F μ hμ w x]
    simp only [map_sum,map_smul,freq]
  · unfold stripMoment
    change radiusMoment m ell (finiteResolvent F (star (line μ w)) x)=
      ‖freq (fun i => -channelValue F i) (fun i => bandRoot m ell (channel F i x)) μ (-w)‖^2
    rw [moment_square,actual_channels F _
      (by simpa only [Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne') x]
    have hc (i : Channel F) : ((channelValue F i : ℂ)-star (line μ w))⁻¹=
        -pole μ (-channelValue F i) (-w) := by
      have he : (channelValue F i : ℂ)-star (line μ w)=
          -((-channelValue F i : ℝ) : ℂ)+line μ (-w) := by
        simp only [line,Complex.star_def,map_add,map_mul,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_neg]
        ring
      rw [he]
      unfold pole
      rw [←inv_neg]
      congr 1
      push_cast
      ring
    simp only [map_sum,hc,neg_smul,map_neg,map_smul,freq]
    rw [Finset.sum_neg_distrib,norm_neg]

private theorem moment_integrable (advanced : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (x : H) :
    Integrable (stripMoment advanced m ell F μ x) := by
  cases advanced
  · apply (frequency_integrable (channelValue F) (fun i => bandRoot m ell (channel F i x)) μ hμ).congr
    exact Eventually.of_forall (fun w => (source_norm false m ell F μ hμ x w).symm)
  · have h := (frequency_integrable (fun i => -channelValue F i)
      (fun i => bandRoot m ell (channel F i x)) μ hμ).comp_neg
    apply h.congr
    exact Eventually.of_forall (fun w => (source_norm true m ell F μ hμ x w).symm)

private theorem energy_spectral (advanced : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (x : H) :
    stripEnergy advanced m ell F μ x=
      ∫ w : ℝ,‖freq (fun i : Channel F => if advanced then -channelValue F i else channelValue F i)
        (fun i => bandRoot m ell (channel F i x)) μ w‖^2 := by
  unfold stripEnergy
  simp_rw [source_norm advanced m ell F μ hμ x]
  cases advanced
  · rfl
  · exact integral_neg_eq_self (fun w : ℝ => ‖freq (fun i => -channelValue F i)
      (fun i => bandRoot m ell (channel F i x)) μ w‖^2) volume

/-- Causal Laplace Cauchy with the sharp 1/(4πδ) strip constant, on each actual F. -/
theorem actual_lower_strip_point (advanced : Bool) (m ell : ℕ) (F : Index) (ν μ : ℝ)
    (hν : 0<ν) (hδ : ν<μ) (x : H) (w : ℝ) :
    stripMoment advanced m ell F μ x w  ≤
      (1/(4*Real.pi*(μ-ν)))*stripEnergy advanced m ell F ν x := by
  rw [source_norm advanced m ell F μ (hν.trans hδ) x,energy_spectral advanced m ell F ν hν x]
  exact finite_strip_point _ _ ν μ hν hδ _

/-- Integral strip monotonicity is generated from the same signed channel phases. -/
theorem actual_lower_strip_integral (advanced : Bool) (m ell : ℕ) (F : Index) (ν μ : ℝ)
    (hν : 0<ν) (hδ : ν<μ) (x : H) :
    stripEnergy advanced m ell F μ x  ≤  stripEnergy advanced m ell F ν x := by
  rw [energy_spectral advanced m ell F μ (hν.trans hδ) x,energy_spectral advanced m ell F ν hν x]
  exact finite_strip_integral _ _ ν μ hν hδ

/-- The same-F advanced/retarded pair consumes the two lower-strip integrals directly. -/
theorem actual_lower_strip_paired_price (m ell : ℕ) (F : Index) (ν μ : ℝ)
    (hν : 0<ν) (hδ : ν<μ) (g k : diagonal.domain) :
    pairedRadiusCost m ell F μ g k  ≤  ENNReal.ofReal
      ((1/(4*Real.pi*(μ-ν)))*stripEnergy true m ell F ν (k : H)*stripEnergy false m ell F ν (g : H)) := by
  have hd : 0<μ-ν := sub_pos.mpr hδ
  let C : ℝ := 1/(4*Real.pi*(μ-ν))*stripEnergy true m ell F ν (k : H)
  have hC : 0 ≤ C := mul_nonneg (by positivity) (integral_nonneg (moment_nonnegative true m ell F ν (k : H)))
  have hI : (∫⁻ w : ℝ,ENNReal.ofReal (stripMoment false m ell F μ (g : H) w))=
      ENNReal.ofReal (stripEnergy false m ell F μ (g : H)) := by
    rw [←ofReal_integral_eq_lintegral_ofReal (moment_integrable false m ell F μ (hν.trans hδ) (g : H))
      (Eventually.of_forall (moment_nonnegative false m ell F μ (g : H)))]
    rfl
  calc
    _  ≤  ∫⁻ w : ℝ,ENNReal.ofReal C*ENNReal.ofReal (stripMoment false m ell F μ (g : H) w) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right (actual_lower_strip_point true m ell F ν μ hν hδ (k : H) w)
        (moment_nonnegative false m ell F μ (g : H) w)
    _ = ENNReal.ofReal C*ENNReal.ofReal (stripEnergy false m ell F μ (g : H)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,hI]
    _  ≤  ENNReal.ofReal C*ENNReal.ofReal (stripEnergy false m ell F ν (g : H)) :=
      mul_le_mul_right (ENNReal.ofReal_le_ofReal (actual_lower_strip_integral false m ell F ν μ hν hδ (g : H))) _
    _ = _ := by rw [←ENNReal.ofReal_mul hC]

end LowEnergy.SourceLowerStripRadiusPrice
