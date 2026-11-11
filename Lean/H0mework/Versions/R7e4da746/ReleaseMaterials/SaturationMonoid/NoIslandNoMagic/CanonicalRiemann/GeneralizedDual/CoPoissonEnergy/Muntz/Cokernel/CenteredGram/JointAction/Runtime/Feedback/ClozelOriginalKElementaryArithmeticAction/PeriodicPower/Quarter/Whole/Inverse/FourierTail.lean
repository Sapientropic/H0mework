import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Derivative

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.FourierTail
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.PositionPrice OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Regularity OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.Derivative
open scoped Topology InnerProductSpace
open private inverse_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Position
open private phase_pair from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ReturnedArithmeticKernel
local notation "q"=>(1/4:ℝ)
local notation "μq"=>volume.restrict (symmetricInterval q)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "freq"=>(2*(Real.pi:ℂ))

theorem actual_inverse_reflection (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    reflectRestricted q (sourceInverse c zero:Hq)=(sourceInverse c zero:Hq):=by
  have source:=inverse_even c zero 1 (by norm_num)
  rw [actual_position_inverse_source c zero 1 (by norm_num)] at source
  exact source

theorem actual_inverse_raw_even (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (x:ℝ) (inside:x∈Icc (-q) q):inverseRaw c zero (-x)=inverseRaw c zero x:=by
  have evenRaw:(fun y:ℝ=>inverseRaw c zero (-y))=ᵐ[μq]inverseRaw c zero:=by
    filter_upwards [actual_inverse_raw c zero,
      (negMeasurePreserving_restrict q).quasiMeasurePreserving.ae (actual_inverse_raw c zero),
      Lp.coeFn_compMeasurePreserving (sourceInverse c zero:Hq) (negMeasurePreserving_restrict q)]
      with y raw negative reflected
    change reflectRestricted q (sourceInverse c zero:Hq) y=(sourceInverse c zero:Hq) (-y) at reflected
    rw [actual_inverse_reflection c zero] at reflected
    exact negative.symm.trans (reflected.symm.trans raw)
  exact MeasureTheory.Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (-q:ℝ)≠q) evenRaw
    ((actual_inverse_continuous c zero).comp continuous_neg).continuousOn
    (actual_inverse_continuous c zero).continuousOn inside

def inverseFourierRaw (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):ℝ→ℂ:=
  burnolRadiusTruncatedFourierRaw q (sourceInverse c zero:Hq)

theorem actual_inverse_fourier_cosine (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (x:ℝ):
    inverseFourierRaw c zero x=2*∫y:ℝ in (0:ℝ)..q,
      Complex.cos (freq*(x:ℂ)*(y:ℂ))*inverseRaw c zero y:=by
  have raw:=Constructor.fourierRaw_congr _ _ (actual_inverse_raw c zero)
  rw [inverseFourierRaw,←Constructor.fourierRaw_state,raw,Constructor.fourierRaw_integral]
  have positive:Continuous (fun y:ℝ=>Constructor.phase x y*inverseRaw c zero y):=
    (Constructor.phaseContinuous x).mul (actual_inverse_continuous c zero)
  have reflected:(∫y:ℝ in (-q)..(0:ℝ),Constructor.phase x y*inverseRaw c zero y)=
      ∫y:ℝ in (0:ℝ)..q,Constructor.phase x (-y)*inverseRaw c zero y:=by
    have moved:=intervalIntegral.integral_comp_neg
      (f:=fun y:ℝ=>Constructor.phase x y*inverseRaw c zero y) (a:=(0:ℝ)) (b:=q)
    rw [neg_zero] at moved
    rw [←moved]
    apply intervalIntegral.integral_congr
    intro y hy
    dsimp only
    rw [actual_inverse_raw_even c zero y (by
      rw [uIcc_of_le (by norm_num : (0:ℝ)≤q)] at hy
      exact ⟨by linarith [hy.1],hy.2⟩)]
  rw [←intervalIntegral.integral_add_adjacent_intervals (positive.intervalIntegrable (-q) 0)
    (positive.intervalIntegrable 0 q),reflected,←intervalIntegral.integral_add]
  · rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y _
    dsimp only
    rw [←add_mul,add_comm (Constructor.phase x (-y)),phase_pair]
    ring
  · exact (((Constructor.phaseContinuous x).comp continuous_neg).mul
      (actual_inverse_continuous c zero)).intervalIntegrable 0 q
  · exact positive.intervalIntegrable 0 q

/-- Both actual compact endpoints and the complete derivative integral pay the original inverse Fourier tail. -/
theorem actual_inverse_fourier_tail (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    ∃B:ℝ,0≤B∧∀x:ℝ,1≤x→‖inverseFourierRaw c zero x‖≤B/x:=by
  let f:=inverseRaw c zero
  let f':=inverseSlope c zero
  let D:ℝ:=‖f q‖+∫y:ℝ in (0:ℝ)..q,‖f' y‖
  have nonnegative:0≤D:=by
    dsimp only [D]
    exact add_nonneg (norm_nonneg _) (intervalIntegral.integral_nonneg (by norm_num) (fun _ _=>norm_nonneg _))
  refine ⟨D/Real.pi,div_nonneg nonnegative Real.pi_pos.le,fun x large=>?_⟩
  have positiveX:0<x:=lt_of_lt_of_le (by norm_num : (0:ℝ)<1) large
  let a:ℂ:=freq*(x:ℂ)
  have sinDerivative (y:ℝ):HasDerivAt (fun t:ℝ=>Complex.sin (a*(t:ℂ)))
      (a*Complex.cos (a*(y:ℂ))) y:=by
    have source:=(((Complex.hasDerivAt_sin (a*(y:ℂ))).comp (y:ℂ)
      ((hasDerivAt_id (y:ℂ)).const_mul a))).comp_ofReal
    have normalized:HasDerivAt (fun t:ℝ=>Complex.sin (a*(t:ℂ)))
        (Complex.cos (a*(y:ℂ))*a) y:=by
      simpa only [Function.comp_def,id_eq,mul_one] using source
    convert normalized using 1
    ring
  have cosineContinuous:Continuous (fun y:ℝ=>a*Complex.cos (a*(y:ℂ))):=by fun_prop
  have sineContinuous:Continuous (fun y:ℝ=>Complex.sin (a*(y:ℂ))):=by fun_prop
  have derivativeIntegral:IntervalIntegrable f' volume 0 q:=
    (actual_inverse_slope_continuous c zero).intervalIntegrable_of_Icc (by norm_num)
  have identity:=intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    sineContinuous.continuousOn (actual_inverse_continuous c zero).continuousOn
    (fun y _=>sinDerivative y)
    (fun y hy=>actual_inverse_derivative c zero y (by
      simpa only [min_eq_left (by norm_num : (0:ℝ)≤q),max_eq_right (by norm_num : (0:ℝ)≤q)] using hy))
    (cosineContinuous.intervalIntegrable 0 q) derivativeIntegral
  have firstIntegrable:IntervalIntegrable (fun y:ℝ=>Complex.cos (a*(y:ℂ))*f y) volume 0 q:=
    ((by fun_prop : Continuous (fun y:ℝ=>Complex.cos (a*(y:ℂ)))).mul
      (actual_inverse_continuous c zero)).intervalIntegrable 0 q
  have secondIntegrable:IntervalIntegrable (fun y:ℝ=>Complex.sin (a*(y:ℂ))*f' y) volume 0 q:=
    derivativeIntegral.continuousOn_mul sineContinuous.continuousOn
  simp only [Complex.ofReal_zero,mul_zero,Complex.sin_zero,zero_mul,sub_zero] at identity
  simp only [mul_assoc] at identity
  change (∫y:ℝ in (0:ℝ)..q,a*(Complex.cos (a*(y:ℂ))*f y)+Complex.sin (a*(y:ℂ))*f' y)=
    Complex.sin (a*(q:ℂ))*f q at identity
  rw [intervalIntegral.integral_add (firstIntegrable.const_mul a) secondIntegrable,
    intervalIntegral.integral_const_mul] at identity
  have fourier:a*inverseFourierRaw c zero x=2*(Complex.sin (a*(q:ℂ))*f q-
      ∫y:ℝ in (0:ℝ)..q,Complex.sin (a*(y:ℂ))*f' y):=by
    rw [actual_inverse_fourier_cosine]
    change a*(2*∫y:ℝ in (0:ℝ)..q,Complex.cos (a*(y:ℂ))*f y)=_
    linear_combination 2*identity
  have sineBound (y:ℝ):‖Complex.sin (a*(y:ℂ))‖≤1:=by
    have argument:a*(y:ℂ)=((2*Real.pi*x*y:ℝ):ℂ):=by dsimp only [a];push_cast;ring
    rw [argument,←Complex.ofReal_sin,Complex.norm_real,Real.norm_eq_abs]
    exact Real.abs_sin_le_one _
  have integralBound:‖∫y:ℝ in (0:ℝ)..q,Complex.sin (a*(y:ℂ))*f' y‖≤
      ∫y:ℝ in (0:ℝ)..q,‖f' y‖:=by
    apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans
    apply intervalIntegral.integral_mono_on (by norm_num) secondIntegrable.norm derivativeIntegral.norm
    intro y _
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (sineBound y) (norm_nonneg _)).trans_eq (one_mul _)
  have bound:‖a‖*‖inverseFourierRaw c zero x‖≤2*D:=by
    rw [←norm_mul,fourier,norm_mul,norm_ofNat]
    apply mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add
      (by rw [norm_mul];exact (mul_le_mul_of_nonneg_right (sineBound q) (norm_nonneg _)).trans_eq (one_mul _)) integralBound))
      (by norm_num : (0:ℝ)≤2)
  have normA:‖a‖=2*Real.pi*x:=by
    simp only [a,norm_mul,norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,abs_of_pos positiveX]
  rw [normA] at bound
  apply (le_div_iff₀ positiveX).mpr
  apply (le_div_iff₀ Real.pi_pos).mpr
  nlinarith

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.FourierTail
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
