import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiRenormalizedSecondGreen
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceActualResolventEnergy
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceResolventLorentzian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiRenormalizedSecondGreenBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussDiagonalHistory GaussUnitaryHistory SourceScalarPositiveBulkWard
open SourceClockPhiNativeJointPayment SourceClockPhiRenormalizedSecondGreen
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment
open FullYSourceResolventGraphSplice SourceResolventBandLimit SourceResolventLorentzian
open MeasureTheory Filter
open scoped InnerProductSpace Topology ENNReal
attribute [local irreducible] diagonalAction state finiteResolvent GaussAdjointHistory.coreStep

private theorem frequency_nonreal (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (w : ℝ) :
    (actualFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'
private theorem frequency_square (advanced : Bool) (μ w : ℝ) :
    ‖actualFrequency advanced μ w‖^2=w^2+μ^2 := by
  have h:Complex.normSq (line μ w)=w^2+μ^2 := by
    simp only [line,Complex.normSq_apply,Complex.add_re,Complex.add_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im]
    ring
  cases advanced
  · simpa only [actualFrequency,Bool.false_eq_true,ite_false,←Complex.normSq_eq_norm_sq] using h
  · simpa only [actualFrequency,ite_true,norm_star,←Complex.normSq_eq_norm_sq] using h
private theorem frequency_real (advanced : Bool) (μ w : ℝ) :
    (actualFrequency advanced μ w).re=w := by
  cases advanced <;> simp only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_re,line,Complex.add_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
private theorem frequency_im_square (advanced : Bool) (μ w : ℝ) :
    (actualFrequency advanced μ w).im^2=μ^2 := by
  cases advanced <;> simp only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_sq]
private theorem frequency_kernel (advanced : Bool) (μ w : ℝ) :
    (‖actualFrequency advanced μ w‖^2)⁻¹=kernel μ 0 w := by
  rw [frequency_square]
  simp only [kernel,zero_sub,neg_sq]
private theorem young (x y t : ℝ) (ht : 0<t) : x*y≤t*x^2+y^2/(4*t) := by
  have he:(4*t)*(y^2/(4*t))=y^2 := by field_simp
  nlinarith only [sq_nonneg (2*t*x-y),he,ht]
private theorem inverse_square_young (a b u μ η : ℝ) (hμ : 0<μ)
    (hμu : μ≤u) (hη : 0<η) :
    a*b/u^2≤η/u^2+a^2*b^2/(4*η*μ^2) := by
  have hy:=young 1 (a*b) η hη
  have h1:a*b/u^2≤(η+(a*b)^2/(4*η))/u^2 :=
    div_le_div_of_nonneg_right (by simpa only [one_mul,one_pow,mul_one] using hy) (sq_nonneg u)
  have hh:(a*b)^2/(4*η)/u^2≤(a*b)^2/(4*η)/μ^2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ hμ.le hμu 2
  calc
    _≤(η+(a*b)^2/(4*η))/u^2 := h1
    _=η/u^2+((a*b)^2/(4*η))/u^2 := by ring
    _≤η/u^2+((a*b)^2/(4*η))/μ^2 := add_le_add le_rfl hh
    _=_ := by ring
private theorem inverse_young (a b u η : ℝ) (hη : 0<η) :
    a*b/u≤η/u^2+a^2*b^2/(4*η) := by
  have h:=young (u⁻¹) (a*b) η hη
  convert h using 1 <;> ring
private theorem norm_pair (f g : QuantumTest) : ‖sourcePair f g‖≤‖embed f‖*‖embed g‖ :=
  norm_inner_le_norm _ _
private theorem complex_sum_bound (a b : Fin 2 → ℂ) (x y : ℂ) :
    |(x*(∑i,a i)-y*(∑i,b i)).re|≤‖x‖*(∑i,‖a i‖)+‖y‖*(∑i,‖b i‖) := by
  calc
    _≤‖x*(∑i,a i)-y*(∑i,b i)‖ := Complex.abs_re_le_norm _
    _≤‖x*(∑i,a i)‖+‖y*(∑i,b i)‖ := norm_sub_le _ _
    _=‖x‖*‖∑i,a i‖+‖y‖*‖∑i,b i‖ := by rw [norm_mul,norm_mul]
    _≤_ := add_le_add (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _))

def fixedFrequencyPrice (m ell : ℕ) (μ η : ℝ) (g : diagonal.domain) : ℝ :=
  Real.pi/μ*(4*η+‖embed (fixedColumn m ell g)‖*‖embed (diagonalAction (fixedColumn m ell g))‖+
    μ*‖embed (fixedColumn m ell g)‖^2)+
  Real.pi/(4*η*μ^3)*(∑i : Fin 2,‖embed (fixedSecondTester m ell g i)‖^2*
    ‖(GaussAdjointHistory.coreStep (GaussAdjointHistory.coreStep (inputSeed g i)) : H)‖^2)+
  Real.pi/(4*η*μ)*(∑i : Fin 2,‖embed (fixedFirstTester m ell g i)‖^2*
    ‖(GaussAdjointHistory.coreStep (GaussAdjointHistory.coreStep (inputSeed g i)) : H)‖^2)

private theorem lorentz_point (w μ b : ℝ) (hμ : 0<μ) (hb : 0≤b) :
    |2*w*μ^2*b/(w^2+μ^2)^2|≤μ*b/(w^2+μ^2) := by
  have hd:0<w^2+μ^2 := by positivity
  have hw:2*|w| *μ≤w^2+μ^2 := by
    nlinarith only [sq_nonneg (|w|-μ),sq_abs w]
  simp only [abs_div,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ)≤2),abs_pow,abs_of_nonneg hμ.le,
    abs_of_nonneg hb,abs_of_nonneg hd.le]
  apply (div_le_iff₀ (pow_pos hd 2)).mpr
  have hh:=mul_le_mul_of_nonneg_right hw hb
  field_simp [ne_of_gt hd]
  nlinarith only [hh]

private theorem principal_point (z : ℂ) (X Y R : Fin 2 → QuantumTest) (μ η : ℝ)
    (hz : 0<‖z‖) (hμ : 0<μ) (hμz : μ≤‖z‖) (hη : 0<η) :
    |(((z^2)⁻¹)*(∑i,sourcePair (X i) (R i))-
      ((z.re : ℂ)*((z^2)⁻¹))*(∑i,sourcePair (Y i) (R i))).re|≤
        4*η/(‖z‖^2)+
        (1/(4*η*μ^2))*(∑i,‖embed (X i)‖^2*‖embed (R i)‖^2)+
        (1/(4*η))*(∑i,‖embed (Y i)‖^2*‖embed (R i)‖^2) := by
  have ha:‖(z^2)⁻¹‖=1/‖z‖^2 := by simp only [norm_inv,norm_pow,one_div]
  have hb:‖(z.re : ℂ)*((z^2)⁻¹)‖=|z.re|/‖z‖^2 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,ha]
    ring
  have hX:(∑i : Fin 2,‖sourcePair (X i) (R i)‖)≤∑i,‖embed (X i)‖*‖embed (R i)‖ :=
    Finset.sum_le_sum (fun i _=>norm_pair _ _)
  have hY:(∑i : Fin 2,‖sourcePair (Y i) (R i)‖)≤∑i,‖embed (Y i)‖*‖embed (R i)‖ :=
    Finset.sum_le_sum (fun i _=>norm_pair _ _)
  have hi(i : Fin 2):|z.re| *‖embed (Y i)‖*‖embed (R i)‖/‖z‖^2≤
      η/‖z‖^2+‖embed (Y i)‖^2*‖embed (R i)‖^2/(4*η) := by
    calc
      _≤‖z‖*‖embed (Y i)‖*‖embed (R i)‖/‖z‖^2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (norm_nonneg _)) (norm_nonneg _)
      _=‖embed (Y i)‖*‖embed (R i)‖/‖z‖ := by field_simp [ne_of_gt hz]
      _≤_ := inverse_young _ _ _ _ hη
  calc
    _≤‖(z^2)⁻¹‖*(∑i,‖sourcePair (X i) (R i)‖)+
        ‖(z.re : ℂ)*((z^2)⁻¹)‖*(∑i,‖sourcePair (Y i) (R i)‖) := complex_sum_bound _ _ _ _
    _≤‖(z^2)⁻¹‖*(∑i,‖embed (X i)‖*‖embed (R i)‖)+
        ‖(z.re : ℂ)*((z^2)⁻¹)‖*(∑i,‖embed (Y i)‖*‖embed (R i)‖) :=
      add_le_add (mul_le_mul_of_nonneg_left hX (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hY (norm_nonneg _))
    _=(∑i,‖embed (X i)‖*‖embed (R i)‖/‖z‖^2)+
        (∑i,|z.re| *‖embed (Y i)‖*‖embed (R i)‖/‖z‖^2) := by
      rw [ha,hb]
      simp only [Fin.sum_univ_two]
      ring
    _≤(∑i : Fin 2,(η/‖z‖^2+‖embed (X i)‖^2*‖embed (R i)‖^2/(4*η*μ^2)))+
        (∑i : Fin 2,(η/‖z‖^2+‖embed (Y i)‖^2*‖embed (R i)‖^2/(4*η))) :=
      add_le_add (Finset.sum_le_sum (fun i _=>inverse_square_young _ _ _ _ _ hμ hμz hη))
        (Finset.sum_le_sum (fun i _=>hi i))
    _=_ := by simp only [Fin.sum_univ_two];ring

def fixedPointPrice (m ell : ℕ) (F : Index) (advanced : Bool) (μ : ℝ) (hμ : 0<μ)
    (η : ℝ) (g : diagonal.domain) (w : ℝ) : ℝ :=
  (4*η+‖embed (fixedColumn m ell g)‖*‖embed (diagonalAction (fixedColumn m ell g))‖+
    μ*‖embed (fixedColumn m ell g)‖^2)*kernel μ 0 w+
  (1/(4*η*μ^2))*(∑i : Fin 2,‖embed (fixedSecondTester m ell g i)‖^2*
    ‖embed (fixedSecondResponse i F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g)‖^2)+
  (1/(4*η))*(∑i : Fin 2,‖embed (fixedFirstTester m ell g i)‖^2*
    ‖embed (fixedSecondResponse i F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g)‖^2)

/-- The mandatory pole subtraction produces an ordinary absolute envelope over the full frequency axis. -/
theorem actual_renormalized_point_budget (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) (η : ℝ) (hη : 0<η) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀m ell : ℕ,∀advanced : Bool,∀w : ℝ,
      |renormalizedEndpoint m ell F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g|≤
        fixedPointPrice m ell F advanced μ hμ η g w := by
  filter_upwards [actual_renormalized_fixed_source g] with F hF
  intro m ell advanced w
  let z:=actualFrequency advanced μ w
  let k:=fixedColumn m ell g
  let Hk:=diagonalAction k
  let X(i : Fin 2):=fixedSecondTester m ell g i
  let Y(i : Fin 2):=fixedFirstTester m ell g i
  let R(i : Fin 2):=fixedSecondResponse i F z (frequency_nonreal advanced μ hμ w) g
  have hz0:z≠0 := by
    intro he
    have hi:z.im≠0 := frequency_nonreal advanced μ hμ w
    exact hi (congrArg Complex.im he)
  have hz:0<‖z‖ := norm_pos_iff.mpr hz0
  have hsq:‖z‖^2=w^2+μ^2 := frequency_square advanced μ w
  have hμz:μ≤‖z‖ := by nlinarith only [hsq,sq_nonneg w,norm_nonneg z,hμ]
  have hmain:=principal_point z X Y R μ η hz hμ hμz hη
  have hc:|(sourcePair k Hk).re*((z^2)⁻¹).re|≤‖embed k‖*‖embed Hk‖/‖z‖^2 := by
    rw [abs_mul]
    have h1:|(sourcePair k Hk).re|≤‖embed k‖*‖embed Hk‖ :=
      (Complex.abs_re_le_norm _).trans (norm_pair _ _)
    have h2:|((z^2)⁻¹).re|≤1/‖z‖^2 := by
      calc
        _≤‖(z^2)⁻¹‖ := Complex.abs_re_le_norm _
        _=1/‖z‖^2 := by simp only [norm_inv,norm_pow,one_div]
    exact (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hp:|2*z.re*z.im^2*‖embed k‖^2/(z.re^2+z.im^2)^2|≤μ*‖embed k‖^2/‖z‖^2 := by
    have h:=lorentz_point w μ (‖embed k‖^2) hμ (sq_nonneg _)
    change |2*(actualFrequency advanced μ w).re*(actualFrequency advanced μ w).im^2*‖embed k‖^2/
      ((actualFrequency advanced μ w).re^2+(actualFrequency advanced μ w).im^2)^2|≤_
    rw [frequency_real,frequency_im_square,hsq]
    exact h
  have he:=hF m ell z (frequency_nonreal advanced μ hμ w)
  rw [he]
  have ha(x a b : ℝ):|x-a-b|≤|x|+|a|+|b| := by
    simpa only [sub_eq_add_neg,abs_neg] using
      (abs_add_le (x+ -a) (-b)).trans (add_le_add (abs_add_le x (-a)) le_rfl)
  calc
    _≤_ := by exact ha _ _ _
    _≤(4*η/‖z‖^2+(1/(4*η*μ^2))*(∑i,‖embed (X i)‖^2*‖embed (R i)‖^2)+
        (1/(4*η))*(∑i,‖embed (Y i)‖^2*‖embed (R i)‖^2))+
        ‖embed k‖*‖embed Hk‖/‖z‖^2+μ*‖embed k‖^2/‖z‖^2 :=
      add_le_add (add_le_add hmain hc) hp
    _=fixedPointPrice m ell F advanced μ hμ η g w := by
      unfold fixedPointPrice
      rw [←frequency_kernel advanced μ w]
      dsimp only [X,Y,R,k,Hk,z]
      ring

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g : H) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem causal_mass (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ) (x : H) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (actualFrequency advanced μ w) x‖^2))=
      ENNReal.ofReal (Real.pi/μ*‖x‖^2) := by
  have h:(∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line μ w) x‖^2))=
      ENNReal.ofReal (Real.pi/μ*‖x‖^2) := by
    simpa only [line,mul_comm (μ : ℂ) Complex.I] using
      SourceActualResolventEnergy.actual_square_lintegral F μ hμ x
  cases advanced
  · simpa only [actualFrequency,Bool.false_eq_true,ite_false] using h
  · have he(w : ℝ):‖finiteResolvent F (actualFrequency true μ w) x‖=
        ‖finiteResolvent F (line μ w) x‖ := by
      exact SourceInverseSourceLeg.actual_conjugate_leg_norm F _
        (by simpa only [line_im] using hμ.ne') x
    simp_rw [he]
    exact h
private theorem causal_measurable (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ) (x : H) :
    Measurable (fun w : ℝ=>ENNReal.ofReal (‖finiteResolvent F (actualFrequency advanced μ w) x‖^2)) := by
  have hR:Continuous (fun w : ℝ=>finiteResolvent F (line μ w) x) :=
    (SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F).clm_apply continuous_const
  have h:Measurable (fun w : ℝ=>ENNReal.ofReal (‖finiteResolvent F (line μ w) x‖^2)) := by
    simpa only [Pi.pow_apply] using (hR.norm.pow 2).measurable.ennreal_ofReal
  cases advanced
  · simpa only [actualFrequency,Bool.false_eq_true,ite_false] using h
  · have he(w : ℝ):‖finiteResolvent F (actualFrequency true μ w) x‖=
        ‖finiteResolvent F (line μ w) x‖ := by
      exact SourceInverseSourceLeg.actual_conjugate_leg_norm F _
        (by simpa only [line_im] using hμ.ne') x
    simp_rw [he]
    exact h
private def secondSeed (g : diagonal.domain) (i : Fin 2) : diagonal.domain :=
  GaussAdjointHistory.coreStep (GaussAdjointHistory.coreStep (inputSeed g i))
private def responseEnergy (i : Fin 2) (F : Index) (advanced : Bool) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) (w : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖embed (fixedSecondResponse i F (actualFrequency advanced μ w)
    (frequency_nonreal advanced μ hμ w) g)‖^2)
private theorem response_read (i : Fin 2) (F : Index) (advanced : Bool) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) (w : ℝ) : responseEnergy i F advanced μ hμ g w=
      ENNReal.ofReal (‖finiteResolvent F (actualFrequency advanced μ w) (secondSeed g i : H)‖^2) := by
  unfold responseEnergy fixedSecondResponse
  rw [state_embed]
  rfl
private theorem response_measurable (i : Fin 2) (F : Index) (advanced : Bool) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) : Measurable (responseEnergy i F advanced μ hμ g) := by
  change Measurable (fun w : ℝ=>responseEnergy i F advanced μ hμ g w)
  simp_rw [response_read]
  exact causal_measurable advanced F μ hμ _
private theorem response_mass (i : Fin 2) (F : Index) (advanced : Bool) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) : (∫⁻ w : ℝ,responseEnergy i F advanced μ hμ g w)=
      ENNReal.ofReal (Real.pi/μ*‖(secondSeed g i : H)‖^2) := by
  simp_rw [response_read]
  exact causal_mass advanced F μ hμ _
private theorem kernel_mass (μ : ℝ) (hμ : 0<μ) :
    (∫⁻ w : ℝ,ENNReal.ofReal (kernel μ 0 w))=ENNReal.ofReal (Real.pi/μ) := by
  rw [←ofReal_integral_eq_lintegral_ofReal (kernel_integrable μ 0 hμ)
    (Eventually.of_forall (fun w=>by unfold kernel;positivity)),kernel_integral μ 0 hμ]
private theorem point_price_integral (m ell : ℕ) (F : Index) (advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (η : ℝ) (hη : 0<η) (g : diagonal.domain) :
    (∫⁻ w : ℝ,ENNReal.ofReal (fixedPointPrice m ell F advanced μ hμ η g w))=
      ENNReal.ofReal (fixedFrequencyPrice m ell μ η g) := by
  let C:=4*η+‖embed (fixedColumn m ell g)‖*‖embed (diagonalAction (fixedColumn m ell g))‖+
    μ*‖embed (fixedColumn m ell g)‖^2
  let H(i : Fin 2):=‖embed (fixedSecondTester m ell g i)‖^2/(4*η*μ^2)
  let L(i : Fin 2):=‖embed (fixedFirstTester m ell g i)‖^2/(4*η)
  have hm(i : Fin 2):Measurable (responseEnergy i F advanced μ hμ g):=
    response_measurable i F advanced μ hμ g
  have hC:0≤C := by dsimp only [C];positivity
  have hH(i : Fin 2):0≤H i := by dsimp only [H];positivity
  have hL(i : Fin 2):0≤L i := by dsimp only [L];positivity
  let e(i : Fin 2)(w : ℝ):=‖embed (fixedSecondResponse i F (actualFrequency advanced μ w)
    (frequency_nonreal advanced μ hμ w) g)‖^2
  have he(i : Fin 2)(w : ℝ):0≤e i w := sq_nonneg _
  have hp0(w : ℝ):fixedPointPrice m ell F advanced μ hμ η g w=
      C*kernel μ 0 w+(H 0*e 0 w+H 1*e 1 w)+(L 0*e 0 w+L 1*e 1 w) := by
    unfold fixedPointPrice
    simp only [Fin.sum_univ_two]
    dsimp only [C,H,L,e]
    ring
  have hp(w : ℝ):ENNReal.ofReal (fixedPointPrice m ell F advanced μ hμ η g w)=
      ENNReal.ofReal C*ENNReal.ofReal (kernel μ 0 w)+
      (∑i : Fin 2,ENNReal.ofReal (H i)*responseEnergy i F advanced μ hμ g w)+
      (∑i : Fin 2,ENNReal.ofReal (L i)*responseEnergy i F advanced μ hμ g w) := by
    have hk:0≤kernel μ 0 w := by unfold kernel;positivity
    have hHs:0≤H 0*e 0 w+H 1*e 1 w:=add_nonneg (mul_nonneg (hH 0) (he 0 w)) (mul_nonneg (hH 1) (he 1 w))
    have hLs:0≤L 0*e 0 w+L 1*e 1 w:=add_nonneg (mul_nonneg (hL 0) (he 0 w)) (mul_nonneg (hL 1) (he 1 w))
    rw [hp0,ENNReal.ofReal_add (add_nonneg (mul_nonneg hC hk) hHs) hLs,
      ENNReal.ofReal_add (mul_nonneg hC hk) hHs,
      ENNReal.ofReal_add (mul_nonneg (hH 0) (he 0 w)) (mul_nonneg (hH 1) (he 1 w)),
      ENNReal.ofReal_add (mul_nonneg (hL 0) (he 0 w)) (mul_nonneg (hL 1) (he 1 w)),
      ENNReal.ofReal_mul hC,ENNReal.ofReal_mul (hH 0),ENNReal.ofReal_mul (hH 1),
      ENNReal.ofReal_mul (hL 0),ENNReal.ofReal_mul (hL 1)]
    simp only [Fin.sum_univ_two]
    rfl
  have mH:Measurable (fun w : ℝ=>ENNReal.ofReal (H 0)*responseEnergy 0 F advanced μ hμ g w+
      ENNReal.ofReal (H 1)*responseEnergy 1 F advanced μ hμ g w) := by
    have h:=((hm 0).const_mul (ENNReal.ofReal (H 0))).add ((hm 1).const_mul (ENNReal.ofReal (H 1)))
    convert h using 1
    funext w
    rfl
  have mL:Measurable (fun w : ℝ=>ENNReal.ofReal (L 0)*responseEnergy 0 F advanced μ hμ g w+
      ENNReal.ofReal (L 1)*responseEnergy 1 F advanced μ hμ g w) := by
    have h:=((hm 0).const_mul (ENNReal.ofReal (L 0))).add ((hm 1).const_mul (ENNReal.ofReal (L 1)))
    convert h using 1
    funext w
    rfl
  simp_rw [hp]
  simp only [Fin.sum_univ_two]
  rw [lintegral_add_right _ mL,lintegral_add_right _ mH,
    lintegral_add_right _ ((hm 1).const_mul _),lintegral_add_right _ ((hm 1).const_mul _),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,kernel_mass μ hμ,
    response_mass 0 F advanced μ hμ g,response_mass 1 F advanced μ hμ g]
  dsimp only [C,H,L]
  rw [←ENNReal.ofReal_mul (by positivity),←ENNReal.ofReal_mul (by positivity),
    ←ENNReal.ofReal_mul (by positivity),←ENNReal.ofReal_mul (by positivity),
    ←ENNReal.ofReal_mul (by positivity),←ENNReal.ofReal_add (by positivity) (by positivity),
    ←ENNReal.ofReal_add (by positivity) (by positivity),
    ←ENNReal.ofReal_add (by positivity) (by positivity),
    ←ENNReal.ofReal_add (by positivity) (by positivity)]
  unfold fixedFrequencyPrice secondSeed
  simp only [Fin.sum_univ_two]
  congr 1
  ring

/-- The original full-H0 squared seeds pay the absolute whole-frequency endpoint at the same source event. -/
theorem actual_renormalized_fixed_frequency_budget (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain)
    (η : ℝ) (hη : 0<η) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀m ell : ℕ,∀advanced : Bool,
      (∫⁻ w : ℝ,ENNReal.ofReal (|renormalizedEndpoint m ell F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g|))≤ENNReal.ofReal (fixedFrequencyPrice m ell μ η g) := by
  filter_upwards [actual_renormalized_point_budget μ hμ g η hη] with F hF
  intro m ell advanced
  calc
    _≤∫⁻ w : ℝ,ENNReal.ofReal (fixedPointPrice m ell F advanced μ hμ η g w) :=
      lintegral_mono (fun w=>ENNReal.ofReal_le_ofReal (hF m ell advanced w))
    _=_ := point_price_integral m ell F advanced μ hμ η hη g

end LowEnergy.SourceClockPhiRenormalizedSecondGreenBudget
