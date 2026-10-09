import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMCauchyInitialElectric
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationNativeGaugeLiteral

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMGaugeCurvature
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource
open SourcePropagationNativeActionHessian PreparationVacuumMixedFieldReturn
open PreparationVacuumLowerClassical CanonicalGradedSpatialSource
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationPhysicalNativePhotonFluxReturn ActualEMCauchyDynamic
open scoped Matrix BigOperators Topology

/-- The same complex Fourier field gives both real original first jets, in every native field slot. -/
def gaugeFourierJet (p : Fin 4→ℂ) (f : Fin 289→ℂ) (imaginary : Bool) : NativeFirstJet :=
  (fun j=>if imaginary then (f j).im else (f j).re,
   fun mu j=>if imaginary then (p mu*f j).im else (p mu*f j).re)

/-- Complete original 12-Lie curvature, including the background connection on both sides. -/
def fullGaugeRead (p : Fin 4→ℂ) (pair : Fin 6) (a : Fin 12) : (Fin 289→ℂ)→ₗ[ℂ]ℂ :=
  p (pairFirst pair) • LinearMap.proj (gaugeSlot (pairSecond pair) a)-
  p (pairSecond pair) • LinearMap.proj (gaugeSlot (pairFirst pair) a)+
  (∑ r : Fin 12, ∑ b : Fin 12,
    ((originalAd r a b:ℂ)*(gaugeBackgroundRaw (pairFirst pair) r:ℂ)) •
      LinearMap.proj (gaugeSlot (pairSecond pair) b))+
  (∑ r : Fin 12, ∑ b : Fin 12,
    ((originalAd r a b:ℂ)*(gaugeBackgroundRaw (pairSecond pair) b:ℂ)) •
      LinearMap.proj (gaugeSlot (pairFirst pair) r))

/-- This is all 72 original gauge-curvature components, not the previously restricted 36-reader. -/
def fullGaugeCurvature (p : Fin 4→ℂ) (f : Fin 289→ℂ) : Fin 6→Fin 12→ℂ :=
  fun pair a=>fullGaugeRead p pair a f

private theorem full_read_formula (p : Fin 4→ℂ) (f : Fin 289→ℂ) (pair : Fin 6) (a : Fin 12) :
    fullGaugeCurvature p f pair a=
      p (pairFirst pair)*f (gaugeSlot (pairSecond pair) a)-
      p (pairSecond pair)*f (gaugeSlot (pairFirst pair) a)+
      (∑r : Fin 12,∑b : Fin 12,(originalAd r a b:ℂ)*
        (gaugeBackgroundRaw (pairFirst pair) r:ℂ)*f (gaugeSlot (pairSecond pair) b))+
      (∑r : Fin 12,∑b : Fin 12,(originalAd r a b:ℂ)*
        f (gaugeSlot (pairFirst pair) r)*(gaugeBackgroundRaw (pairSecond pair) b:ℂ)) := by
  simp only [fullGaugeCurvature,fullGaugeRead,LinearMap.add_apply,LinearMap.sub_apply,
    LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.proj_apply,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Every raw original gauge curvature is evaluated on the actual real and imaginary Fourier jets. -/
theorem full_gauge_curvature_original (p : Fin 4→ℂ) (f : Fin 289→ℂ) (pair : Fin 6) (a : Fin 12) :
    fullGaugeCurvature p f pair a=
      (nativeGaugeLinearCurvature (gaugeFourierJet p f false) pair a:ℂ)+Complex.I*
        (nativeGaugeLinearCurvature (gaugeFourierJet p f true) pair a:ℂ) := by
  rw [full_read_formula,gaugeLinearRaw_source,gaugeLinearRaw_source]
  apply Complex.ext
  · simp [gaugeLinearRaw,gaugeFieldRaw,gaugeOriginalBracket,gaugeFourierJet,
      Complex.add_re,Complex.sub_re,Complex.mul_re]
  · simp [gaugeLinearRaw,gaugeFieldRaw,gaugeOriginalBracket,gaugeFourierJet,
      Complex.add_im,Complex.sub_im,Complex.mul_im]

/-- The complete curvature is the derivative of the actual nonlinear original curvature, including its original quadratic bracket. -/
theorem full_gauge_curvature_derivative (p : Fin 4→ℂ) (f : Fin 289→ℂ) (pair : Fin 6) (a : Fin 12) :
    HasDerivAt (fun r : ℝ=>(nativeGaugeRawCurvature (r • gaugeFourierJet p f false) pair a:ℂ)+
      Complex.I*(nativeGaugeRawCurvature (r • gaugeFourierJet p f true) pair a:ℂ))
      (fullGaugeCurvature p f pair a) 0 := by
  have realPart (imaginary : Bool) : HasDerivAt
      (fun r : ℝ=>nativeGaugeRawCurvature (r • gaugeFourierJet p f imaginary) pair a)
      (nativeGaugeLinearCurvature (gaugeFourierJet p f imaginary) pair a) 0 := by
    have paid:=hasDerivAt_pi.mp (coordinateQuadratic_derivative (sourceGaugeCurvature0 pair)
      (nativeGaugeLinearCurvature (gaugeFourierJet p f imaginary) pair)
      (nativeGaugeQuadraticCurvature (gaugeFourierJet p f imaginary) pair) 0) a
    simpa only [nativeGaugeRawCurvature_ray,mul_zero,zero_smul,add_zero] using paid
  rw [full_gauge_curvature_original]
  exact (realPart false).ofReal_comp.add ((realPart true).ofReal_comp.const_mul Complex.I)

/-- The actual holonomic configuration, not a separately assigned curvature tensor, realizes both quadratures. -/
theorem full_gauge_curvature_holonomic (p : Fin 4→ℂ) (f : Fin 289→ℂ) (pair : Fin 6) (a : Fin 12) :
    HasDerivAt (fun r : ℝ=>
      (PreparationCoordinates.rawCoordinates
        (StageNineHolonomicField.p286CoordinateEquiv
          (StageNineHolonomicField.holonomicGaugeCurvature
            (nativeConfiguration (affineSignal (r • gaugeFourierJet p f false))) 0 pair)) a:ℂ)+
      Complex.I*(PreparationCoordinates.rawCoordinates
        (StageNineHolonomicField.p286CoordinateEquiv
          (StageNineHolonomicField.holonomicGaugeCurvature
            (nativeConfiguration (affineSignal (r • gaugeFourierJet p f true))) 0 pair)) a:ℂ))
      (fullGaugeCurvature p f pair a) 0 := by
  simpa only [nativeGaugeCurvature_generated,nativeGaugeRawCurvature] using
    full_gauge_curvature_derivative p f pair a

/-- Joint momentum and complete-field continuity is generated by the original finite curvature polynomial. -/
theorem full_gauge_curvature_continuous (pair : Fin 6) (a : Fin 12) :
    Continuous (fun v : (Fin 4→ℂ)×(Fin 289→ℂ)=>fullGaugeCurvature v.1 v.2 pair a) := by
  simp only [fullGaugeCurvature,fullGaugeRead,LinearMap.add_apply,LinearMap.sub_apply,
    LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.proj_apply,smul_eq_mul]
  fun_prop

/-- The exact source Hessian retains the BF curvature leg, background quadratic curvature and both coframe-Hodge variation legs. -/
theorem full_gauge_bf_hessian (jet : NativeFirstJet) : nativeGaugeQuadratic jet=gaugeFlatQuadratic jet :=
  nativeGaugeQuadratic_flat jet

/-- Original boundary, maintained continuation and nine null data feed the same complete curvature. -/
theorem full_gauge_cauchy_event (spatial : Fin 3→ℂ) (z : ℂ) (hz : z≠0)
    (regular : fullMomentum spatial z∈regularSource) (pair : Fin 6) (a : Fin 12) :
    fullGaugeCurvature (fullMomentum spatial z) (voltageInitialResponse spatial z regular) pair a+
      fullGaugeCurvature (fullMomentum spatial z) (voltageContinuationResponse spatial z regular) pair a+
      fullGaugeCurvature (fullMomentum spatial z) (voltageNullData spatial z) pair a=
      fullGaugeCurvature (fullMomentum spatial z)
        (PreparationPhysicalVoltageCompleteReturn.sourceVoltageLaplaceRamp spatial z) pair a := by
  change fullGaugeRead _ _ _ _+fullGaugeRead _ _ _ _+fullGaugeRead _ _ _ _=fullGaugeRead _ _ _ _
  rw [←map_add,←map_add,voltage_same_green_response spatial z hz regular]

end LowEnergy.GaussComposite.ActualEMGaugeCurvature
