import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Reciprocal.Counting

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Reciprocal.Limit
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Reciprocal.Counting
open scoped Topology ENNReal InnerProductSpace
local notation "μplus" => volume.restrict (Ioi (0:ℝ))

private def radius (n:ℕ):ℝ:=(n+1:ℕ)

private theorem radius_positive (n:ℕ):0<radius n:=by unfold radius;positivity

private theorem radius_top:Tendsto radius atTop atTop:=by
  exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)

private theorem floor_ratio (u:ℝ) (positive:0<u):
    Tendsto (fun n:ℕ=>(⌊radius n/u⌋₊:ℝ)/radius n) atTop (𝓝 u⁻¹):=by
  have inverse:Tendsto (fun n:ℕ=>(radius n)⁻¹) atTop (𝓝 (0:ℝ)):=
    tendsto_inv_atTop_zero.comp radius_top
  have lower:Tendsto (fun n:ℕ=>u⁻¹-(radius n)⁻¹) atTop (𝓝 u⁻¹):=by
    simpa only [sub_zero] using tendsto_const_nhds.sub inverse
  apply lower.squeeze tendsto_const_nhds
  · intro n
    have rp:=radius_positive n
    have h:=Nat.lt_floor_add_one (radius n/u)
    have lowerBound:radius n/u-1≤(⌊radius n/u⌋₊:ℝ):=by linarith
    have scaled:=div_le_div_of_nonneg_right lowerBound rp.le
    have identity:(radius n/u-1)/radius n=u⁻¹-(radius n)⁻¹:=by field_simp
    rwa [identity] at scaled
  · intro n
    have rp:=radius_positive n
    have h:=Nat.floor_le (div_nonneg rp.le positive.le)
    have scaled:=div_le_div_of_nonneg_right h rp.le
    have identity:(radius n/u)/radius n=u⁻¹:=by field_simp
    rwa [identity] at scaled

/-- The original integer-grid adjoint floor kernel converges under its actual reciprocal L1 domain. -/
theorem actual_floor_kernel_limit (f:ℝ→ℂ) (measurable:Measurable f)
    (domain:Integrable (fun u:ℝ=>(u:ℂ)⁻¹*f u) μplus):
    Tendsto (fun n:ℕ=>∫u:ℝ in Ioi (0:ℝ),
      (((⌊radius n/u⌋₊:ℝ)/radius n:ℝ):ℂ)*f u) atTop
      (𝓝 (∫u:ℝ in Ioi (0:ℝ),(u:ℂ)⁻¹*f u)):=by
  apply tendsto_integral_of_dominated_convergence (fun u:ℝ=>‖(u:ℂ)⁻¹*f u‖)
  · intro n
    have coefficient:Measurable (fun u:ℝ=>(((⌊radius n/u⌋₊:ℝ)/radius n:ℝ):ℂ)):=by fun_prop
    exact (coefficient.mul measurable).aestronglyMeasurable
  · exact domain.norm
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u positive
    have rp:=radius_positive n
    have nonnegative:0≤(⌊radius n/u⌋₊:ℝ)/radius n:=div_nonneg (Nat.cast_nonneg _) rp.le
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg nonnegative,
      norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have scaled:=div_le_div_of_nonneg_right (Nat.floor_le (div_nonneg rp.le positive.le)) rp.le
    have identity:(radius n/u)/radius n=u⁻¹:=by field_simp
    rwa [identity] at scaled
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u positive
    have coefficient: Tendsto (fun n:ℕ=>(((⌊radius n/u⌋₊:ℝ)/radius n:ℝ):ℂ)) atTop (𝓝 ((u⁻¹:ℝ):ℂ)):=
      Complex.continuous_ofReal.continuousAt.tendsto.comp (floor_ratio u positive)
    simpa only [Complex.ofReal_inv] using coefficient.mul_const (f u)

private theorem integral_L2_bound (value:BurnolL2) (T:ℝ) (positive:0<T):
    ‖∫y:ℝ in (0:ℝ)..T,value y‖≤Real.sqrt T*‖value‖:=by
  let test:BurnolL2:=indicatorConstLp 2 (measurableSet_Ioc (a:=(0:ℝ)) (b:=T))
    (by simp) (1:ℂ)
  have read:inner ℂ test value=∫y:ℝ in (0:ℝ)..T,value y:=by
    rw [L2.inner_indicatorConstLp_eq_inner_setIntegral ℂ]
    simp only [RCLike.inner_apply,map_one,mul_one]
    rw [intervalIntegral.integral_of_le positive.le]
  have testnorm:‖test‖=Real.sqrt T:=by
    dsimp only [test]
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp only [norm_one,one_mul,ENNReal.toReal_ofNat,measureReal_def,Real.volume_Ioc,
      sub_zero,ENNReal.toReal_ofReal positive.le]
    rw [Real.sqrt_eq_rpow]
  rw [←read]
  exact (norm_inner_le_norm test value).trans_eq (by rw [testnorm])

theorem actual_L2_average_zero (value:BurnolL2):
    Tendsto (fun n:ℕ=>(radius n:ℂ)⁻¹*(∫y:ℝ in (0:ℝ)..radius n,value y)) atTop (𝓝 (0:ℂ)):=by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have decay:Tendsto (fun n:ℕ=>(Real.sqrt (radius n))⁻¹*‖value‖) atTop (𝓝 (0:ℝ)):=by
    simpa only [Function.comp_def,zero_mul] using (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp radius_top)).mul_const ‖value‖
  apply squeeze_zero (fun _=>norm_nonneg _) _ decay
  intro n
  have rp:=radius_positive n
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos rp]
  calc
    _≤(radius n)⁻¹*(Real.sqrt (radius n)*‖value‖):=
      mul_le_mul_of_nonneg_left (integral_L2_bound value (radius n) rp) (inv_nonneg.mpr rp.le)
    _=_:=by
      have square:Real.sqrt (radius n)^2=radius n:=Real.sq_sqrt rp.le
      have positiveRoot:0<Real.sqrt (radius n):=Real.sqrt_pos.mpr rp
      field_simp [rp.ne',positiveRoot.ne']
      rw [square]

/-- A true complete L2 counted Fourier field fixes the full reciprocal mean of its source. -/
theorem actual_counted_reciprocal_mean (f:ℝ→ℂ) (continuous:Continuous f)
    (A:ℝ) (nonnegative:0≤A) (growth:∀u:ℝ,0<u→‖f u‖≤A*u)
    (domain:Integrable (fun u:ℝ=>(u:ℂ)⁻¹*f u) μplus)
    (value:BurnolL2) (mass:ℂ)
    (source:∀ᵐy:ℝ∂volume,HasSum (fun n:ℕ=>(((n+1:ℕ):ℂ)⁻¹)*f (y/((n+1:ℕ):ℝ))) (value y-mass)):
    (∫u:ℝ in Ioi (0:ℝ),(u:ℂ)⁻¹*f u)=-mass:=by
  have kernel:=actual_floor_kernel_limit f continuous.measurable domain
  have integrals (n:ℕ):
      (∫u:ℝ in Ioi (0:ℝ),(((⌊radius n/u⌋₊:ℝ)/radius n:ℝ):ℂ)*f u)=
      (radius n:ℂ)⁻¹*(∫y:ℝ in (0:ℝ)..radius n,value y)-mass:=by
    have rp:=radius_positive n
    have finite:=actual_finite_counting_integral f continuous A nonnegative growth (radius n) rp
    have counted:(∫y:ℝ in (0:ℝ)..radius n,∑'j:ℕ,(((j+1:ℕ):ℂ)⁻¹)*f (y/((j+1:ℕ):ℝ)))=
        ∫y:ℝ in (0:ℝ)..radius n,value y-mass:=by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [source] with y sum _
      exact sum.tsum_eq
    have valueDomain:IntervalIntegrable (value:ℝ→ℂ) volume 0 (radius n):=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le rp.le).mpr
        (integrableOn_Lp_of_measure_ne_top value (by norm_num) (by simp))
    rw [counted,intervalIntegral.integral_sub
      valueDomain (intervalIntegrable_const),
      intervalIntegral.integral_const,sub_zero,Complex.real_smul] at finite
    calc
      _=(radius n:ℂ)⁻¹*(∫u:ℝ in Ioi (0:ℝ),(⌊radius n/u⌋₊:ℂ)*f u):=by
        rw [←integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u _
        dsimp only
        push_cast
        ring
      _=_:=by
        rw [←finite]
        field_simp [Complex.ofReal_ne_zero.mpr rp.ne']
  simp_rw [integrals] at kernel
  have zero:=actual_L2_average_zero value
  have limit:Tendsto (fun n:ℕ=>(radius n:ℂ)⁻¹*(∫y:ℝ in (0:ℝ)..radius n,value y)-mass)
      atTop (𝓝 (-mass)):=by simpa only [zero_sub] using zero.sub_const mass
  exact tendsto_nhds_unique kernel limit

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Reciprocal.Limit
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
