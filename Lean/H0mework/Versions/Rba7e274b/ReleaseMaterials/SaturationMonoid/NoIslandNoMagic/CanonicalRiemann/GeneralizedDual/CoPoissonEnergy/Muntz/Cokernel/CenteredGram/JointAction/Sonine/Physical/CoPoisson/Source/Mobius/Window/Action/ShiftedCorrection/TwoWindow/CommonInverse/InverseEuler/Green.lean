import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.Source
import H0mework.Versions.V2.Arithmetic.RieszGreen.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing.InverseEuler
open Complex Filter FourierTransform MeasureTheory Set OriginalRieszSource
open scoped ENNReal InnerProductSpace Topology
open OriginalTwoWindowInverseForcing OriginalCommonInverseForcing
attribute [local instance 1100] NormedSpace.complexToReal
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "bState" => burnolRieszSingleFourierSource
local notation "bRaw" => burnolRieszSingleFourierSourceRaw

private theorem pair_integrable (left right : BurnolQuarterIntervalL2) (f g : ℝ→ℂ)
    (leftRead : (left:ℝ→ℂ)=ᵐ[μq] f) (rightRead : (right:ℝ→ℂ)=ᵐ[μq] g) :
    Integrable (fun x:ℝ=>star (f x)*g x) μq := by
  apply (L2.integrable_inner (𝕜:=ℂ) left right).congr
  filter_upwards [leftRead,rightRead] with x hl hr
  rw [hl,hr]
  simp only [RCLike.inner_apply,starRingEnd_apply,mul_comm]
private theorem interval_pair_read (left right : BurnolQuarterIntervalL2) (f g : ℝ→ℂ)
    (leftRead : (left:ℝ→ℂ)=ᵐ[μq] f) (rightRead : (right:ℝ→ℂ)=ᵐ[μq] g) :
    inner ℂ left right=∫ x:ℝ in (-q)..q,star (f x)*g x := by
  rw [L2.inner_def,intervalIntegral.integral_of_le (by norm_num : -q≤q),
    ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [leftRead,rightRead] with x hl hr
  rw [hl,hr]
  simp only [RCLike.inner_apply,starRingEnd_apply]
  ring

private theorem source_cotest_origin (coordinate : BurnolCompletedMellinCoordinate)
    (raw : ℝ→ℂ) (continuous : Continuous raw) :
    Tendsto (fun x:ℝ=>(x:ℂ)*star (bRaw coordinate x)*raw x) (𝓝 0) (𝓝 0) := by
  have source:=(OriginalRieszSourceGreen.source_halfWeight_origin coordinate).star.mul
    (OriginalRieszSourceGreen.halfWeight_origin.mul (continuous.tendsto (0:ℝ)))
  simp only [star_zero,zero_mul] at source
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have normLimit:=source.norm
  simp only [norm_zero] at normLimit
  apply normLimit.congr
  intro x
  calc
    ‖star ((Real.sqrt |x|:ℂ)*bRaw coordinate x)*((Real.sqrt |x|:ℂ)*raw x)‖=
        (Real.sqrt |x|)^2*‖bRaw coordinate x‖*‖raw x‖ := by
      simp only [norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg |x|)]
      ring
    _=_ := by
      rw [Real.sq_sqrt (abs_nonneg x)]
      simp only [norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs]

def sourceGreenDensity (coordinate : BurnolCompletedMellinCoordinate)
    (raw derivative : ℝ→ℂ) (x : ℝ) : ℂ :=
  star (OriginalRieszSourceGreen.weightedRaw coordinate x)*raw x+
    star (bRaw coordinate x)*eulerRaw raw derivative x

private theorem source_density_read (coordinate : BurnolCompletedMellinCoordinate)
    (state : BurnolQuarterMeanZeroCarrier) (raw derivative : ℝ→ℂ)
    (rawContinuous : Continuous raw) (derivativeContinuous : Continuous derivative)
    (read : (state:BurnolQuarterIntervalL2)=ᵐ[μq] raw) :
    inner ℂ (Euler.sourceEuler coordinate) state+
      inner ℂ (bState coordinate) (eulerState raw derivative rawContinuous derivativeContinuous)=
      ∫ x:ℝ in (-q)..q,sourceGreenDensity coordinate raw derivative x := by
  have leftProjection:=(burnolQuarterMeanZeroClosedFace.toSubmodule).inner_orthogonalProjectionOnto_eq_of_mem_right state (OriginalRieszSourceGreen.weightedState coordinate)
  have rightProjection:=(burnolQuarterMeanZeroClosedFace.toSubmodule).inner_orthogonalProjectionOnto_eq_of_mem_left (bState coordinate)
      (eulerAmbient raw derivative rawContinuous derivativeContinuous)
  change inner ℂ (Constructor.zeroMean (OriginalRieszSourceGreen.weightedState coordinate)) state=_
    at leftProjection
  change inner ℂ (bState coordinate) (eulerState raw derivative rawContinuous derivativeContinuous)=_
    at rightProjection
  rw [OriginalRieszSourceGreen.weightedState_centered] at leftProjection
  rw [leftProjection,rightProjection]
  unfold eulerAmbient
  rw [interval_pair_read _ _ _ _ (OriginalRieszSourceGreen.weightedState_read coordinate) read,
    interval_pair_read _ _ _ _ (burnolRieszSingleFourierSource_ae_raw coordinate)
      (Constructor.compact_read _ (eulerRaw_continuous _ _ rawContinuous derivativeContinuous))]
  have first:=pair_integrable _ _ _ _ (OriginalRieszSourceGreen.weightedState_read coordinate) read
  have second:=pair_integrable _ _ _ _ (burnolRieszSingleFourierSource_ae_raw coordinate)
    (Constructor.compact_read _ (eulerRaw_continuous _ _ rawContinuous derivativeContinuous))
  have firstIntegral : IntervalIntegrable
      (fun x=>star (OriginalRieszSourceGreen.weightedRaw coordinate x)*raw x) volume (-q) q := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : -q≤q)]
    exact first
  have secondIntegral : IntervalIntegrable
      (fun x=>star (bRaw coordinate x)*eulerRaw raw derivative x) volume (-q) q := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : -q≤q)]
    exact second
  rw [← intervalIntegral.integral_add (f:=fun x=>star (OriginalRieszSourceGreen.weightedRaw coordinate x)*raw x)
    (g:=fun x=>star (bRaw coordinate x)*eulerRaw raw derivative x)
    firstIntegral secondIntegral]
  rfl

theorem source_interval_cotest_green (coordinate : BurnolCompletedMellinCoordinate)
    (state : BurnolQuarterMeanZeroCarrier) (raw derivative : ℝ→ℂ)
    (rawContinuous : Continuous raw) (derivativeContinuous : Continuous derivative)
    (actualDerivative : ∀ x:ℝ,HasDerivAt raw (derivative x) x)
    (read : (state:BurnolQuarterIntervalL2)=ᵐ[μq] raw) :
    inner ℂ (Euler.sourceEuler coordinate) state+
      inner ℂ (bState coordinate) (eulerState raw derivative rawContinuous derivativeContinuous)=
      (q:ℂ)*star (Kernel.beta coordinate)*(raw q+raw (-q)) := by
  let flux:=fun x:ℝ=>(x:ℂ)*star (bRaw coordinate x)*raw x
  have generatedDerivative (x : ℝ) (nonzero : x≠0) :
      HasDerivAt flux (sourceGreenDensity coordinate raw derivative x) x := by
    have actual:=((Complex.ofRealCLM.hasDerivAt (x:=x)).mul
      (OriginalRieszSourceGreen.source_hasDerivAt coordinate x nonzero).star).mul (actualDerivative x)
    convert! actual using 1
    simp only [sourceGreenDensity,eulerRaw,Complex.ofRealCLM_apply,Complex.ofReal_one,
      star_sub,star_mul,star_div₀,star_one,star_ofNat,Complex.star_def,Complex.conj_ofReal,Pi.mul_apply]
    field_simp [Complex.ofReal_ne_zero.mpr nonzero]
    ring
  have first:=pair_integrable _ _ _ _ (OriginalRieszSourceGreen.weightedState_read coordinate) read
  have second:=pair_integrable _ _ _ _ (burnolRieszSingleFourierSource_ae_raw coordinate)
    (Constructor.compact_read _ (eulerRaw_continuous _ _ rawContinuous derivativeContinuous))
  have full : IntervalIntegrable (sourceGreenDensity coordinate raw derivative) volume (-q) q := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : -q≤q)]
    exact first.add second
  have origin:=source_cotest_origin coordinate raw rawContinuous
  have fluxContinuous (x : ℝ) (nonzero : x≠0) : ContinuousAt flux x :=
    (Complex.continuous_ofReal.continuousAt.mul
      (burnolRieszSingleFourierSourceRaw_continuousAt coordinate nonzero).star).mul rawContinuous.continuousAt
  have negativeIntegral : IntervalIntegrable (sourceGreenDensity coordinate raw derivative) volume (-q) 0 :=
    full.mono_set (by
      rw [uIcc_of_le (by norm_num : -q≤0),uIcc_of_le (by norm_num : -q≤q)]
      exact Icc_subset_Icc le_rfl (by norm_num))
  have positiveIntegral : IntervalIntegrable (sourceGreenDensity coordinate raw derivative) volume 0 q :=
    full.mono_set (by
      rw [uIcc_of_le (by norm_num : (0:ℝ)≤q),uIcc_of_le (by norm_num : -q≤q)]
      exact Icc_subset_Icc (by norm_num) le_rfl)
  have negativeFTC:=intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by norm_num : -q<(0:ℝ)) (fun x hx=>generatedDerivative x (by linarith [hx.2])) negativeIntegral
    ((fluxContinuous (-q) (by norm_num)).tendsto.mono_left nhdsWithin_le_nhds)
    (origin.mono_left nhdsWithin_le_nhds)
  have positiveFTC:=intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by norm_num : (0:ℝ)<q) (fun x hx=>generatedDerivative x (by linarith [hx.1])) positiveIntegral
    (origin.mono_left nhdsWithin_le_nhds)
    ((fluxContinuous q (by norm_num)).tendsto.mono_left nhdsWithin_le_nhds)
  rw [source_density_read coordinate state raw derivative rawContinuous derivativeContinuous read,
    ← intervalIntegral.integral_add_adjacent_intervals negativeIntegral positiveIntegral,
    negativeFTC,positiveFTC]
  dsimp only [flux]
  rw [burnolRieszSingleFourierSourceRaw_endpoints coordinate]
  unfold Kernel.beta
  push_cast
  ring

theorem return_interval_cotest_green (coordinate : BurnolCompletedMellinCoordinate)
    (state : BurnolQuarterMeanZeroCarrier) (raw derivative : ℝ→ℂ)
    (rawContinuous : Continuous raw) (derivativeContinuous : Continuous derivative)
    (actualDerivative : ∀ x:ℝ,HasDerivAt raw (derivative x) x)
    (read : (state:BurnolQuarterIntervalL2)=ᵐ[μq] raw) :
    inner ℂ (Constructor.returnEuler coordinate) state+
      inner ℂ (Constructor.returnState coordinate) (eulerState raw derivative rawContinuous derivativeContinuous)=
      (q:ℂ)*star (burnolRieszReturnRaw coordinate q)*(raw q+raw (-q)) := by
  let primitive:=fun x:ℝ=>(x:ℂ)*star (burnolRieszReturnRaw coordinate x)*raw x
  let density:=fun x:ℝ=>star (Constructor.returnEulerRaw coordinate x)*raw x+
    star (burnolRieszReturnRaw coordinate x)*eulerRaw raw derivative x
  have generatedDerivative (x : ℝ) : HasDerivAt primitive (density x) x := by
    have actual:=((Complex.ofRealCLM.hasDerivAt (x:=x)).mul
      (burnolRieszReturnRaw_hasDerivAt coordinate x).star).mul (actualDerivative x)
    convert! actual using 1
    simp only [density,Constructor.returnEulerRaw,eulerRaw,Complex.ofRealCLM_apply,Complex.ofReal_one,
      star_add,star_mul,star_div₀,star_one,star_ofNat,Complex.star_def,Complex.conj_ofReal,Pi.mul_apply]
    ring
  have firstContinuous : Continuous (fun x:ℝ=>star (Constructor.returnEulerRaw coordinate x)*raw x) :=
    (Constructor.returnEulerRaw_continuous coordinate).star.mul rawContinuous
  have secondContinuous : Continuous (fun x:ℝ=>star (burnolRieszReturnRaw coordinate x)*eulerRaw raw derivative x) :=
    (burnolRieszReturnRaw_continuous coordinate).star.mul
      (eulerRaw_continuous _ _ rawContinuous derivativeContinuous)
  have integrated:=intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _=>generatedDerivative x)
    ((firstContinuous.add secondContinuous).intervalIntegrable (-q) q)
  unfold Constructor.returnEuler eulerState Constructor.zeroMean
  simp only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  unfold Constructor.returnEulerAmbient eulerAmbient
  rw [interval_pair_read _ _ _ _ (Constructor.compact_read _ (Constructor.returnEulerRaw_continuous coordinate)) read,
    interval_pair_read _ _ _ _ (Constructor.returnState_read coordinate)
      (Constructor.compact_read _ (eulerRaw_continuous _ _ rawContinuous derivativeContinuous)),
    ← intervalIntegral.integral_add (firstContinuous.intervalIntegrable (-q) q) (secondContinuous.intervalIntegrable (-q) q)]
  change (∫ x:ℝ in (-q)..q,density x)=_
  rw [integrated]
  dsimp only [primitive]
  have endpoints : burnolRieszReturnRaw coordinate (-q)=burnolRieszReturnRaw coordinate q :=
    burnolRieszSingleFourierReturnRaw_endpoints coordinate
  rw [endpoints]
  push_cast
  ring

end OriginalCommonInverseForcing.InverseEuler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
