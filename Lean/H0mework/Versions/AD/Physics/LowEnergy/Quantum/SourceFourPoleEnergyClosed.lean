import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceJointResidualEnergy
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecificLimits.RCLike

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceFourPoleEnergyClosed
open MeasureTheory Filter SourceJointResidualEnergy SourceResolventLorentzian
open SourceResolventBandLimit (line line_im)
open scoped Topology InnerProductSpace

private def den (μ a t : ℝ) : ℂ := (a : ℂ)-line μ t

private theorem den_ne (μ a t : ℝ) (hμ : 0<μ) : den μ a t≠0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [den,Complex.sub_im,Complex.ofReal_im,line_im,Complex.zero_im,
    zero_sub,neg_eq_zero] at hi
  exact hμ.ne' hi

private theorem pole_top (μ a : ℝ) : Tendsto (pole μ a) atTop (𝓝 0) := by
  have h := tendsto_inv₀_cobounded.comp
    ((tendsto_const_sub_cobounded ((a : ℂ)-(μ : ℂ)*Complex.I)).comp
      (RCLike.tendsto_ofReal_atTop_cobounded ℂ))
  convert h using 1
  funext t
  unfold pole line
  congr 1
  change (a : ℂ)-((t : ℂ)+(μ : ℂ)*Complex.I)=
    (a : ℂ)-(μ : ℂ)*Complex.I-(t : ℂ)
  ring

private theorem pole_bot (μ a : ℝ) : Tendsto (pole μ a) atBot (𝓝 0) := by
  have h := tendsto_inv₀_cobounded.comp
    ((tendsto_const_sub_cobounded ((a : ℂ)-(μ : ℂ)*Complex.I)).comp
      (RCLike.tendsto_ofReal_atBot_cobounded ℂ))
  convert h using 1
  funext t
  unfold pole line
  congr 1
  change (a : ℂ)-((t : ℂ)+(μ : ℂ)*Complex.I)=
    (a : ℂ)-(μ : ℂ)*Complex.I-(t : ℂ)
  ring

private def ratio (μ a b t : ℝ) : ℂ := den μ a t/den μ b t

private theorem ratio_slit (μ a b t : ℝ) (hμ : 0<μ) :
    ratio μ a b t∈Complex.slitPlane := by
  by_cases hab : a=b
  · simp [ratio,hab,div_self (den_ne μ b t hμ)]
  · apply Complex.mem_slitPlane_iff.mpr
    right
    have hi : (ratio μ a b t).im=μ*(a-b)/((b-t)^2+μ^2) := by
      simp [ratio,den,line,Complex.div_im,Complex.normSq_apply]
      ring
    rw [hi]
    exact div_ne_zero (mul_ne_zero hμ.ne' (sub_ne_zero.mpr hab)) (by positivity)

private theorem den_deriv (μ a t : ℝ) : HasDerivAt (den μ a) (-1) t := by
  simpa only [den,line,Complex.ofReal_one,id_eq] using!
    (((hasDerivAt_id t).ofReal_comp).add_const ((μ : ℂ)*Complex.I)).const_sub (a : ℂ)

private theorem log_ratio_deriv (μ a b t : ℝ) (hμ : 0<μ) :
    HasDerivAt (fun t => Complex.log (ratio μ a b t)) (pole μ b t-pole μ a t) t := by
  have h := ((den_deriv μ a t).div (den_deriv μ b t) (den_ne μ b t hμ)).clog_real
    (ratio_slit μ a b t hμ)
  convert h using 1
  · rfl
  · unfold pole
    change (den μ b t)⁻¹-(den μ a t)⁻¹=
      ((-1*den μ b t-den μ a t*(-1))/(den μ b t)^2)/(den μ a t/den μ b t)
    field_simp [den_ne μ a t hμ,den_ne μ b t hμ]
    ring

private theorem ratio_eq (μ a b t : ℝ) (hμ : 0<μ) :
    ratio μ a b t=1+((a : ℂ)-(b : ℂ))*pole μ b t := by
  unfold ratio pole
  change den μ a t/den μ b t=1+((a : ℂ)-(b : ℂ))*(den μ b t)⁻¹
  field_simp [den_ne μ b t hμ]
  unfold den
  ring

private theorem log_ratio_top (μ a b : ℝ) (hμ : 0<μ) :
    Tendsto (fun t => Complex.log (ratio μ a b t)) atTop (𝓝 0) := by
  have h : Tendsto (ratio μ a b) atTop (𝓝 1) := by
    change Tendsto (fun t => ratio μ a b t) atTop (𝓝 1)
    simp_rw [ratio_eq μ a b _ hμ]
    simpa using tendsto_const_nhds.add ((pole_top μ b).const_mul ((a : ℂ)-(b : ℂ)))
  simpa using h.clog Complex.one_mem_slitPlane

private theorem log_ratio_bot (μ a b : ℝ) (hμ : 0<μ) :
    Tendsto (fun t => Complex.log (ratio μ a b t)) atBot (𝓝 0) := by
  have h : Tendsto (ratio μ a b) atBot (𝓝 1) := by
    change Tendsto (fun t => ratio μ a b t) atBot (𝓝 1)
    simp_rw [ratio_eq μ a b _ hμ]
    simpa using tendsto_const_nhds.add ((pole_bot μ b).const_mul ((a : ℂ)-(b : ℂ)))
  simpa using h.clog Complex.one_mem_slitPlane

theorem same_half_integrable (μ a b : ℝ) (hμ : 0<μ) : Integrable (polePair μ a b) := by
  apply memLp_one_iff_integrable.mp
  exact (pole_memLp μ b hμ).mul' (pole_memLp μ a hμ)

private theorem pole_difference (μ a b t : ℝ) (hμ : 0<μ) :
    pole μ a t-pole μ b t=((b : ℂ)-(a : ℂ))*polePair μ a b t := by
  unfold polePair pole
  change (den μ a t)⁻¹-(den μ b t)⁻¹=
    ((b : ℂ)-(a : ℂ))*((den μ a t)⁻¹*(den μ b t)⁻¹)
  field_simp [den_ne μ a t hμ,den_ne μ b t hμ]
  unfold den
  ring

theorem pole_difference_integral (μ a b : ℝ) (hμ : 0<μ) :
    (∫ t : ℝ, pole μ a t-pole μ b t)=0 := by
  have hi : Integrable (fun t : ℝ => pole μ a t-pole μ b t) := by
    simp_rw [pole_difference μ a b _ hμ]
    exact (same_half_integrable μ a b hμ).const_mul _
  simpa using integral_of_hasDerivAt_of_tendsto (fun t => log_ratio_deriv μ b a t hμ) hi
    (log_ratio_bot μ b a hμ) (log_ratio_top μ b a hμ)

private theorem pole_deriv (μ a t : ℝ) (hμ : 0<μ) :
    HasDerivAt (pole μ a) (polePair μ a a t) t := by
  have h := (den_deriv μ a t).inv (den_ne μ a t hμ)
  convert h using 1 <;> first | rfl | simp [polePair,pole,den,div_eq_mul_inv,pow_two]

theorem same_half_integral (μ a b : ℝ) (hμ : 0<μ) :
    (∫ t : ℝ, polePair μ a b t)=0 := by
  by_cases hab : a=b
  · subst b
    simpa using integral_of_hasDerivAt_of_tendsto (fun t => pole_deriv μ a t hμ)
      (same_half_integrable μ a a hμ) (pole_bot μ a) (pole_top μ a)
  · have h := pole_difference_integral μ a b hμ
    simp_rw [pole_difference μ a b _ hμ] at h
    rw [integral_const_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (by exact_mod_cast Ne.symm hab))

def gap (μ a c : ℝ) : ℂ := 2*(μ : ℂ)+Complex.I*((c : ℂ)-(a : ℂ))

theorem gap_ne (μ a c : ℝ) (hμ : 0<μ) : gap μ a c≠0 := by
  intro h
  have hr := congrArg Complex.re h
  simp [gap] at hr
  linarith

private theorem gap_den (μ a c t : ℝ) :
    gap μ a c=Complex.I*(den μ c t-star (den μ a t)) := by
  apply Complex.ext <;> simp [gap,den,line]
  ring

theorem two_pole_integrable (μ a c : ℝ) (hμ : 0<μ) :
    Integrable (fun t : ℝ => star (pole μ a t)*pole μ c t) := by
  apply memLp_one_iff_integrable.mp
  exact (pole_memLp μ c hμ).mul' (pole_memLp μ a hμ).star

private theorem gap_two_pole (μ a c t : ℝ) (hμ : 0<μ) :
    gap μ a c*(star (pole μ a t)*pole μ c t)=
      Complex.I*(star (pole μ a t)-pole μ c t) := by
  rw [gap_den μ a c t]
  unfold pole
  change (Complex.I*(den μ c t-star (den μ a t)))*
    (star ((den μ a t)⁻¹)*(den μ c t)⁻¹)=
      Complex.I*(star ((den μ a t)⁻¹)-(den μ c t)⁻¹)
  rw [star_inv₀]
  field_simp [den_ne μ a t hμ,den_ne μ c t hμ,
    star_ne_zero.mpr (den_ne μ a t hμ)]

private theorem pole_star_difference (μ a t : ℝ) (hμ : 0<μ) :
    star (pole μ a t)-pole μ a t=(-2*Complex.I*(μ : ℂ))*(kernel μ a t : ℂ) := by
  have hn : star (pole μ a t)*pole μ a t=(kernel μ a t : ℂ) := by
    change (starRingEnd ℂ) (pole μ a t)*pole μ a t=_
    rw [←Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
    congr 1
    simpa only [pole,line,mul_comm] using inverse_norm_square μ a t
  calc
    _ = (den μ a t-star (den μ a t))*(star (pole μ a t)*pole μ a t) := by
      unfold pole
      change star ((den μ a t)⁻¹)-(den μ a t)⁻¹=
        (den μ a t-star (den μ a t))*(star ((den μ a t)⁻¹)*(den μ a t)⁻¹)
      rw [star_inv₀]
      field_simp [den_ne μ a t hμ,star_ne_zero.mpr (den_ne μ a t hμ)]
    _ = _ := by
      rw [hn]
      congr 1
      apply Complex.ext <;> simp [den,line]
      ring

def twoPole (μ a c : ℝ) : ℂ := ∫ t : ℝ, star (pole μ a t)*pole μ c t

theorem two_pole_closed (μ a c : ℝ) (hμ : 0<μ) :
    twoPole μ a c=2*(Real.pi : ℂ)/gap μ a c := by
  have hid (t : ℝ) : gap μ a c*(star (pole μ a t)*pole μ c t)=
      Complex.I*((-2*Complex.I*(μ : ℂ))*(kernel μ a t : ℂ)+
        (pole μ a t-pole μ c t)) := by
    rw [gap_two_pole μ a c t hμ,←pole_star_difference μ a t hμ]
    congr 1
    abel
  have hi : Integrable (fun t : ℝ => pole μ a t-pole μ c t) := by
    simp_rw [pole_difference μ a c _ hμ]
    exact (same_half_integrable μ a c hμ).const_mul _
  have hk : Integrable (fun t : ℝ => (-2*Complex.I*(μ : ℂ))*(kernel μ a t : ℂ)) :=
    ((kernel_integrable μ a hμ).ofReal).const_mul _
  have he : gap μ a c*twoPole μ a c=2*(Real.pi : ℂ) := by
    unfold twoPole
    rw [←integral_const_mul]
    simp_rw [hid]
    rw [integral_const_mul,integral_add hk hi,integral_const_mul,
      integral_complex_ofReal,kernel_integral μ a hμ,pole_difference_integral μ a c hμ]
    push_cast
    field_simp [hμ.ne']
    ring_nf
    norm_num
  exact (eq_div_iff (gap_ne μ a c hμ)).mpr (by simpa only [mul_comm] using he)

private theorem four_pole_gap (μ a b c d t : ℝ) (hμ : 0<μ) :
    (gap μ a c*gap μ b d)*(star (polePair μ a b t)*polePair μ c d t)=
      star (pole μ a t)*pole μ d t+star (pole μ b t)*pole μ c t-
        star (polePair μ a b t)-polePair μ c d t := by
  calc
    _ = (gap μ a c*(star (pole μ a t)*pole μ c t))*
        (gap μ b d*(star (pole μ b t)*pole μ d t)) := by
      simp only [polePair,star_mul]
      ring
    _ = (Complex.I*(star (pole μ a t)-pole μ c t))*
        (Complex.I*(star (pole μ b t)-pole μ d t)) := by
      rw [gap_two_pole μ a c t hμ,gap_two_pole μ b d t hμ]
    _ = (Complex.I*Complex.I)*((star (pole μ a t)-pole μ c t)*
        (star (pole μ b t)-pole μ d t)) := by ring
    _ = _ := by
      rw [Complex.I_mul_I]
      simp only [polePair,star_mul]
      ring

def closedKernel (μ a b c d : ℝ) : ℂ :=
  (2*(Real.pi : ℂ)*(4*(μ : ℂ)+Complex.I*((c : ℂ)+(d : ℂ)-(a : ℂ)-(b : ℂ))))/
    (gap μ a c*gap μ a d*gap μ b c*gap μ b d)

/-- One scalar formula covers all spectral collisions; only cross-half-plane gaps are divided. -/
theorem four_pole_closed (μ a b c d : ℝ) (hμ : 0<μ) :
    fourPole μ a b c d=closedKernel μ a b c d := by
  have hab : Integrable (fun t : ℝ => star (polePair μ a b t)) := by
    apply memLp_one_iff_integrable.mp
    exact (memLp_one_iff_integrable.mpr (same_half_integrable μ a b hμ)).star
  have hcd := same_half_integrable μ c d hμ
  have had := two_pole_integrable μ a d hμ
  have hbc := two_pole_integrable μ b c hμ
  have hs : (∫ t : ℝ, star (polePair μ a b t))=0 := by
    change (∫ t : ℝ, (starRingEnd ℂ) (polePair μ a b t))=0
    rw [integral_conj,same_half_integral μ a b hμ,map_zero]
  have hsum : Integrable (fun t : ℝ =>
      star (pole μ a t)*pole μ d t+star (pole μ b t)*pole μ c t) := had.add hbc
  have hsub : Integrable (fun t : ℝ =>
      star (pole μ a t)*pole μ d t+star (pole μ b t)*pole μ c t-
        star (polePair μ a b t)) := hsum.sub hab
  have he : (gap μ a c*gap μ b d)*fourPole μ a b c d=twoPole μ a d+twoPole μ b c := by
    unfold fourPole twoPole
    rw [←integral_const_mul]
    simp_rw [four_pole_gap μ a b c d _ hμ]
    rw [integral_sub hsub hcd,
      integral_sub hsum hab,integral_add had hbc,hs,
      same_half_integral μ c d hμ,sub_zero,sub_zero]
  apply mul_left_cancel₀ (mul_ne_zero (gap_ne μ a c hμ) (gap_ne μ b d hμ))
  rw [he,two_pole_closed μ a d hμ,two_pole_closed μ b c hμ]
  unfold closedKernel
  field_simp [gap_ne μ a c hμ,gap_ne μ a d hμ,gap_ne μ b c hμ,gap_ne μ b d hμ]
  unfold gap
  ring

theorem four_pole_repeated (μ a : ℝ) (hμ : 0<μ) :
    fourPole μ a a a a=(Real.pi : ℂ)/(2*(μ : ℂ)^3) := by
  rw [four_pole_closed μ a a a a hμ]
  simp only [closedKernel,gap,sub_self,mul_zero,add_zero]
  have hm : (μ : ℂ)≠0 := by exact_mod_cast hμ.ne'
  field_simp [hm]
  ring

open GaussCoreHilbert GaussDiagonalHistory GaussUnitaryHistory

def closedJointCost (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (g k : H) : ℝ :=
  (∑ ij : Channel F × Channel F, ∑ kl : Channel F × Channel F,
    closedKernel μ (channelValue F ij.1) (channelValue F ij.2)
      (channelValue F kl.1) (channelValue F kl.2)*
      inner ℂ (inner ℂ k (spectralLeg F (jointInsertion sharp m ell F) g ij))
        (inner ℂ k (spectralLeg F (jointInsertion sharp m ell F) g kl))).re

theorem actual_joint_gram_closed (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ)
    (hμ : 0<μ) (g k : H) :
    actualJointGram sharp m ell F μ g k=closedJointCost sharp m ell F μ g k := by
  unfold actualJointGram closedJointCost
  simp_rw [four_pole_closed μ _ _ _ _ hμ]

/-- The actual native/sharp joint cost has no remaining frequency integral in its finite Gram. -/
theorem actual_joint_closed_energy (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ)
    (hμ : 0<μ) (g k : diagonal.domain) :
    (∫ t : ℝ, ‖jointResidual sharp m ell F (line μ t)
      (by simpa only [line_im] using hμ.ne') g k‖^2)=
      closedJointCost sharp m ell F μ (g : H) (k : H) := by
  rw [actual_joint_energy sharp m ell F μ hμ g k,
    actual_joint_gram_closed sharp m ell F μ hμ (g : H) (k : H)]

theorem actual_joint_closed_lintegral (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ)
    (hμ : 0<μ) (g k : diagonal.domain) :
    (∫⁻ t, ENNReal.ofReal (‖jointResidual sharp m ell F (line μ t)
      (by simpa only [line_im] using hμ.ne') g k‖^2))=
      ENNReal.ofReal (closedJointCost sharp m ell F μ (g : H) (k : H)) := by
  rw [actual_joint_lintegral sharp m ell F μ hμ g k,
    actual_joint_gram_closed sharp m ell F μ hμ (g : H) (k : H)]

end LowEnergy.SourceFourPoleEnergyClosed
