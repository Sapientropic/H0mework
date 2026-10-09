import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYPairedRetardedParseval
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceFourPoleEnergyClosed
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FullYDynamicResponse
open MeasureTheory Filter SourceJointResidualEnergy SourceFourPoleEnergyClosed SourceResolventBandLimit
open scoped Topology FourierTransform

private def den(μ a t:ℝ):ℂ:=(a:ℂ)-line μ t
private theorem den_ne(μ a t:ℝ)(hμ:0<μ):den μ a t≠0:=by
  intro h
  have hi:=congrArg Complex.im h
  simp only [den,Complex.sub_im,Complex.ofReal_im,line_im,Complex.zero_im,zero_sub,neg_eq_zero] at hi
  exact hμ.ne' hi
private theorem den_im(μ a t:ℝ):(den μ a t).im= -μ:=by
  simp only [den,Complex.sub_im,Complex.ofReal_im,line_im,zero_sub]
private def ratio(μ ν a b t:ℝ):ℂ:=den μ a t/den ν b t
private theorem ratio_slit(μ ν a b t:ℝ)(hμ:0<μ)(hν:0<ν):ratio μ ν a b t∈Complex.slitPlane:=by
  apply Complex.mem_slitPlane_iff.mpr
  by_cases hi:(ratio μ ν a b t).im≠0
  · exact Or.inr hi
  · apply Or.inl
    have hi0:(ratio μ ν a b t).im=0:=not_ne_iff.mp hi
    have hm:ratio μ ν a b t*den ν b t=den μ a t:=div_mul_cancel₀ _ (den_ne ν b t hν)
    have him:=congrArg Complex.im hm
    simp only [Complex.mul_im,den_im,hi0,zero_mul,add_zero] at him
    nlinarith
private theorem den_deriv(μ a t:ℝ):HasDerivAt (den μ a) (-1) t:=by
  simpa only [den,line,Complex.ofReal_one,id_eq] using!
    (((hasDerivAt_id t).ofReal_comp).add_const ((μ:ℂ)*Complex.I)).const_sub (a:ℂ)
private theorem log_deriv(μ ν a b t:ℝ)(hμ:0<μ)(hν:0<ν):
    HasDerivAt (fun t:ℝ=>Complex.log (ratio μ ν a b t)) (pole ν b t-pole μ a t) t:=by
  have h:=((den_deriv μ a t).div (den_deriv ν b t) (den_ne ν b t hν)).clog_real
    (ratio_slit μ ν a b t hμ hν)
  convert h using 1
  · rfl
  · unfold pole
    change (den ν b t)⁻¹-(den μ a t)⁻¹=
      ((-1*den ν b t-den μ a t*(-1))/(den ν b t)^2)/(den μ a t/den ν b t)
    field_simp [den_ne μ a t hμ,den_ne ν b t hν]
    ring
private theorem pole_top(μ a:ℝ):Tendsto (pole μ a) atTop (𝓝 0):=by
  have h:=tendsto_inv₀_cobounded.comp
    ((tendsto_const_sub_cobounded ((a:ℂ)-(μ:ℂ)*Complex.I)).comp
      (RCLike.tendsto_ofReal_atTop_cobounded ℂ))
  convert h using 1
  funext t
  unfold pole line
  congr 1
  change (a:ℂ)-((t:ℂ)+(μ:ℂ)*Complex.I)=(a:ℂ)-(μ:ℂ)*Complex.I-(t:ℂ)
  ring
private theorem pole_bot(μ a:ℝ):Tendsto (pole μ a) atBot (𝓝 0):=by
  have h:=tendsto_inv₀_cobounded.comp
    ((tendsto_const_sub_cobounded ((a:ℂ)-(μ:ℂ)*Complex.I)).comp
      (RCLike.tendsto_ofReal_atBot_cobounded ℂ))
  convert h using 1
  funext t
  unfold pole line
  congr 1
  change (a:ℂ)-((t:ℂ)+(μ:ℂ)*Complex.I)=(a:ℂ)-(μ:ℂ)*Complex.I-(t:ℂ)
  ring
private def difference(μ ν a b:ℝ):ℂ:=((b:ℂ)-(ν:ℂ)*Complex.I)-((a:ℂ)-(μ:ℂ)*Complex.I)
private theorem ratio_eq(μ ν a b t:ℝ)(hν:0<ν):
    ratio μ ν a b t=1-difference μ ν a b*pole ν b t:=by
  unfold ratio pole difference
  change den μ a t/den ν b t=1-
    (((b:ℂ)-(ν:ℂ)*Complex.I)-((a:ℂ)-(μ:ℂ)*Complex.I))*(den ν b t)⁻¹
  field_simp [den_ne ν b t hν]
  unfold den line
  ring
private theorem pole_difference(μ ν a b t:ℝ)(hμ:0<μ)(hν:0<ν):
    pole μ a t-pole ν b t=difference μ ν a b*(pole μ a t*pole ν b t):=by
  unfold pole
  change (den μ a t)⁻¹-(den ν b t)⁻¹=difference μ ν a b*((den μ a t)⁻¹*(den ν b t)⁻¹)
  field_simp [den_ne μ a t hμ,den_ne ν b t hν]
  unfold den line difference
  ring

theorem mixed_same_half_integrable(μ ν a b:ℝ)(hμ:0<μ)(hν:0<ν):
    Integrable (fun t:ℝ=>pole μ a t*pole ν b t):=
  memLp_one_iff_integrable.mp ((pole_memLp ν b hν).mul' (pole_memLp μ a hμ))

/-- Distinct positive damping parameters share the same original causal half-plane cancellation. -/
theorem mixed_same_half_integral(μ ν a b:ℝ)(hμ:0<μ)(hν:0<ν):
    (∫t:ℝ,pole μ a t*pole ν b t)=0:=by
  by_cases he:μ=ν
  · subst ν
    exact same_half_integral μ a b hμ
  have hd:difference μ ν a b≠0:=by
    intro hz
    have h:=congrArg Complex.im hz
    simp only [difference,Complex.sub_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      Complex.I_im,Complex.I_re,mul_one,mul_zero,zero_sub,Complex.zero_im] at h
    exact he (by linarith)
  have hi:Integrable (fun t:ℝ=>pole μ a t-pole ν b t):=by
    simp_rw [pole_difference μ ν a b _ hμ hν]
    exact (mixed_same_half_integrable μ ν a b hμ hν).const_mul _
  have ht:Tendsto (fun t:ℝ=>Complex.log (ratio ν μ b a t)) atTop (𝓝 0):=by
    have h:Tendsto (ratio ν μ b a) atTop (𝓝 1):=by
      change Tendsto (fun t:ℝ=>ratio ν μ b a t) atTop (𝓝 1)
      simp_rw [ratio_eq ν μ b a _ hμ]
      simpa only [mul_zero,sub_zero] using tendsto_const_nhds.sub ((pole_top μ a).const_mul (difference ν μ b a))
    simpa only [Complex.log_one] using h.clog Complex.one_mem_slitPlane
  have hb:Tendsto (fun t:ℝ=>Complex.log (ratio ν μ b a t)) atBot (𝓝 0):=by
    have h:Tendsto (ratio ν μ b a) atBot (𝓝 1):=by
      change Tendsto (fun t:ℝ=>ratio ν μ b a t) atBot (𝓝 1)
      simp_rw [ratio_eq ν μ b a _ hμ]
      simpa only [mul_zero,sub_zero] using tendsto_const_nhds.sub ((pole_bot μ a).const_mul (difference ν μ b a))
    simpa only [Complex.log_one] using h.clog Complex.one_mem_slitPlane
  have hz:(∫t:ℝ,pole μ a t-pole ν b t)=0:=by
    simpa only [sub_self] using integral_of_hasDerivAt_of_tendsto
      (fun t=>log_deriv ν μ b a t hν hμ) hi hb ht
  simp_rw [pole_difference μ ν a b _ hμ hν] at hz
  rw [integral_const_mul] at hz
  exact (mul_eq_zero.mp hz).resolve_left hd

end LowEnergy.FullYDynamicResponse
