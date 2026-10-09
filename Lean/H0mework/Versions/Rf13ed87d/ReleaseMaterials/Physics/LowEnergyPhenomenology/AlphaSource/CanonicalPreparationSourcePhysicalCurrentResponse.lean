import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePhysicalCurrentWave

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalCurrentLaplaceReturn
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField
open PreparationVacuumElectromagneticIdentity CanonicalGradedSpatialSource
open PreparationVacuumPhysicalFeedback PreparationVacuumCurrentSignalRealization
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumCurrentConstrainedInverse PreparationVacuumMixedFieldReturn
open PreparationVacuumOriginalGreenFeedback PreparationVacuumGaugeSourceInjection
open PreparationVacuumFieldConstraintResponse
open SourcePropagationNativeActionHessian SourcePropagationNativeEulerHistory SourcePropagationMotherEulerKernel
open Filter MeasureTheory Set
open scoped BigOperators ContDiff Topology Matrix Interval
attribute [local irreducible] nativeHessian originalJacobi sourceDressedField sourceDressedGreen sourceCompatibility
  sourcePhysicalCurrentAmplitude actualMovingNativeForcing sourceMovingGaugeVertex

def sourcePhysicalCurrentWindow (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) (T : ℝ) : SignalAmplitude:=fun i=>
  ∫t in (0:ℝ)..T,laplaceWeight lambda t*
    sourceMovingWaveForcing (nativeTimePoint t) leftMomentum rightMomentum left right i

def sourcePhysicalCurrentHalf (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) : SignalAmplitude:=fun i=>
  ∫t in Ioi (0:ℝ),laplaceWeight lambda t*
    sourceMovingWaveForcing (nativeTimePoint t) leftMomentum rightMomentum left right i

private theorem physicalCurrent_weighted (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) (t : ℝ) (i : Fin 289) :
    laplaceWeight lambda t*sourceMovingWaveForcing (nativeTimePoint t) leftMomentum rightMomentum left right i=
      Complex.exp ((sourcePhysicalClock leftMomentum rightMomentum left right-lambda)*(t:ℂ))*
        sourcePhysicalCurrentAmplitude leftMomentum rightMomentum left right i :=by
  rw [sourceMovingWaveForcing_signal]
  change laplaceWeight lambda t*sourceSignalAmplitude
    (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial (sourcePhysicalTransfer leftMomentum rightMomentum))
      (sourcePhysicalClock leftMomentum rightMomentum left right))
        (sourcePhysicalCurrentAmplitude leftMomentum rightMomentum left right) (nativeTimePoint t) i=_
  exact congrFun (sourceNativeSignal_weighted _ _ lambda _ t) i

theorem sourcePhysicalCurrent_integrable (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) (off : 0<lambda.re) (i : Fin 289) :
    IntegrableOn (fun t : ℝ=>laplaceWeight lambda t*
      sourceMovingWaveForcing (nativeTimePoint t) leftMomentum rightMomentum left right i) (Ioi (0:ℝ)) :=by
  simp_rw [physicalCurrent_weighted]
  have negative : (sourcePhysicalClock leftMomentum rightMomentum left right-lambda).re<0:=by
    simp only [Complex.sub_re,sourcePhysicalClock_re,zero_sub]
    linarith
  exact (integrableOn_exp_mul_complex_Ioi negative 0).mul_const _

theorem sourcePhysicalCurrentWindow_generated (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) (T : ℝ) :
    sourcePhysicalCurrentWindow leftMomentum rightMomentum left right lambda T=
      sourceNativePlaneWindow (sourcePhysicalClock leftMomentum rightMomentum left right) lambda T
        (sourcePhysicalCurrentAmplitude leftMomentum rightMomentum left right) :=by
  funext i
  unfold sourcePhysicalCurrentWindow
  simp_rw [physicalCurrent_weighted]
  rw [intervalIntegral.integral_mul_const]
  rfl

theorem sourcePhysicalCurrentHalf_generated (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) (off : 0<lambda.re) :
    sourcePhysicalCurrentHalf leftMomentum rightMomentum left right lambda=
      (lambda-sourcePhysicalClock leftMomentum rightMomentum left right)⁻¹ •
        sourcePhysicalCurrentAmplitude leftMomentum rightMomentum left right :=by
  funext i
  unfold sourcePhysicalCurrentHalf
  simp_rw [physicalCurrent_weighted]
  rw [integral_mul_const]
  have domain : (sourcePhysicalClock leftMomentum rightMomentum left right).re<lambda.re:=by
    rw [sourcePhysicalClock_re]
    exact off
  change sourcePlaneHalfScalar (sourcePhysicalClock leftMomentum rightMomentum left right) lambda*
    sourcePhysicalCurrentAmplitude leftMomentum rightMomentum left right i=_
  rw [sourcePlaneHalfScalar_actual _ _ domain]
  rfl

theorem sourcePhysicalCurrentHalf_initial (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) (off : 0<lambda.re) :
    (lambda-sourcePhysicalClock leftMomentum rightMomentum left right) •
        sourcePhysicalCurrentHalf leftMomentum rightMomentum left right lambda=
      sourceMovingWaveForcing 0 leftMomentum rightMomentum left right :=by
  rw [sourcePhysicalCurrentHalf_generated _ _ _ _ lambda off,sourceMovingWaveForcing_initial,smul_smul]
  have different : lambda-sourcePhysicalClock leftMomentum rightMomentum left right≠0:=by
    intro equal
    have real:=congrArg Complex.re equal
    simp only [Complex.sub_re,sourcePhysicalClock_re,Complex.zero_re,sub_zero] at real
    linarith
  rw [mul_inv_cancel₀ different,one_smul]

private theorem planeWindow_remainder (clock lambda : ℂ) (T : ℝ) (different : lambda-clock≠0) :
    (lambda-clock)⁻¹-sourcePlaneWindowScalar clock lambda T=
      (lambda-clock)⁻¹*Complex.exp ((clock-lambda)*(T:ℂ)) :=by
  have paid:=sourcePlaneWindowScalar_derivative clock lambda T
  change (clock-lambda)*sourcePlaneWindowScalar clock lambda T=
    Complex.exp ((clock-lambda)*(T:ℂ))-1 at paid
  apply (mul_right_injective₀ different)
  dsimp only
  rw [mul_sub,mul_inv_cancel₀ different,←mul_assoc,mul_inv_cancel₀ different,one_mul]
  linear_combination paid

theorem sourcePhysicalCurrent_tail (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) (off : 0<lambda.re) (T : ℝ) :
    sourcePhysicalCurrentHalf leftMomentum rightMomentum left right lambda-
        sourcePhysicalCurrentWindow leftMomentum rightMomentum left right lambda T=
      ((lambda-sourcePhysicalClock leftMomentum rightMomentum left right)⁻¹*
        Complex.exp ((sourcePhysicalClock leftMomentum rightMomentum left right-lambda)*(T:ℂ))) •
          sourcePhysicalCurrentAmplitude leftMomentum rightMomentum left right :=by
  have different : lambda-sourcePhysicalClock leftMomentum rightMomentum left right≠0:=by
    intro equal
    have real:=congrArg Complex.re equal
    simp only [Complex.sub_re,sourcePhysicalClock_re,Complex.zero_re,sub_zero] at real
    linarith
  rw [sourcePhysicalCurrentHalf_generated _ _ _ _ lambda off,sourcePhysicalCurrentWindow_generated,
    sourceNativePlaneWindow,←sub_smul,planeWindow_remainder _ _ T different]

theorem sourcePhysicalCurrent_tailPrice (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (lambda : ℂ) (off : 0<lambda.re) (T : ℝ) :
    ‖sourcePhysicalCurrentHalf leftMomentum rightMomentum left right lambda-
        sourcePhysicalCurrentWindow leftMomentum rightMomentum left right lambda T‖=
      (‖lambda-sourcePhysicalClock leftMomentum rightMomentum left right‖⁻¹*Real.exp (-lambda.re*T))*
        ‖sourcePhysicalCurrentAmplitude leftMomentum rightMomentum left right‖ :=by
  rw [sourcePhysicalCurrent_tail _ _ _ _ lambda off T,norm_smul,norm_mul,norm_inv,Complex.norm_exp]
  congr 2
  simp [Complex.mul_re,Complex.sub_re,sourcePhysicalClock_re]

def sourcePhysicalCurrentRead (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (field : SignalAmplitude) : ℂ:=
  ∑i : Fin 289,sourcePhysicalCurrentAmplitude leftMomentum rightMomentum left right i*field i

theorem sourcePhysicalCurrentRead_original (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (field : SignalAmplitude) :
    sourcePhysicalCurrentRead leftMomentum rightMomentum left right field=
      sourceNativeGaugeCurrentComplex 0 (actualMovingPairPoint 0 leftMomentum rightMomentum left right) (fun i=>(field i).re)+
        Complex.I*sourceNativeGaugeCurrentComplex 0 (actualMovingPairPoint 0 leftMomentum rightMomentum left right) (fun i=>(field i).im) :=by
  rw [←actualMovingNativeForcing_generated,←actualMovingNativeForcing_generated]
  unfold sourcePhysicalCurrentRead sourcePhysicalCurrentAmplitude
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _=actualMovingNativeForcing 0 leftMomentum rightMomentum left right i*
      ((field i).re+(field i).im*Complex.I) :=by rw [Complex.re_add_im]
    _=_ :=by ring

theorem sourcePhysicalCurrentRead_kinetic (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (field : Field289) :
    HasDerivAt (actualMovingGaugeKineticCurve 0 leftMomentum rightMomentum left right field)
      (sourcePhysicalCurrentRead leftMomentum rightMomentum left right (fun i=>(field i:ℂ))).re 0 :=by
  have actual:=actualMovingGaugeKineticCurve_hasDerivAt 0 leftMomentum rightMomentum left right field 0
  convert actual using 1
  unfold sourcePhysicalCurrentRead sourcePhysicalCurrentAmplitude
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  apply Finset.sum_congr rfl
  intro i _
  ring

def sourcePhysicalMediumPoint (q : PhysicalResponsePoint) (leftMomentum rightMomentum : PhysicalMomentum) :
    PhysicalResponsePoint:={q with k:=sourcePhysicalTransfer leftMomentum rightMomentum}

def sourcePhysicalDrivenField (q : PhysicalResponsePoint) (leftMomentum rightMomentum : PhysicalMomentum)
    (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q leftMomentum rightMomentum)
      (sourcePhysicalClock leftMomentum rightMomentum left right)) : SignalAmplitude:=
  sourceDressedField (sourcePhysicalMediumPoint q leftMomentum rightMomentum)
    (sourcePhysicalClock leftMomentum rightMomentum left right) frequency
    (sourcePhysicalCurrentHalf leftMomentum rightMomentum left right frequency.val.val.val)

theorem sourcePhysicalFrequency_positive (q : PhysicalResponsePoint) (leftMomentum rightMomentum : PhysicalMomentum)
    (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q leftMomentum rightMomentum)
      (sourcePhysicalClock leftMomentum rightMomentum left right)) :
    0<frequency.val.val.val.re :=by
  have paid:=frequency.val.property
  change sourceClockGrowth (fullMomentum
    (PreparationVacuumPhysicalFeedback.physicalSpatial (sourcePhysicalMediumPoint q leftMomentum rightMomentum).k)
      (sourcePhysicalClock leftMomentum rightMomentum left right))<frequency.val.val.val.re at paid
  simpa only [sourceClockGrowth,fullMomentum,Fin.cases_zero,sourcePhysicalClock_re,max_self] using paid

def sourcePhysicalWindowField (q : PhysicalResponsePoint) (leftMomentum rightMomentum : PhysicalMomentum)
    (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q leftMomentum rightMomentum)
      (sourcePhysicalClock leftMomentum rightMomentum left right)) (T : ℝ) : SignalAmplitude:=
  sourceDressedField (sourcePhysicalMediumPoint q leftMomentum rightMomentum)
    (sourcePhysicalClock leftMomentum rightMomentum left right) frequency
    (sourcePhysicalCurrentWindow leftMomentum rightMomentum left right frequency.val.val.val T)

theorem sourcePhysicalDrivenField_tailPrice (q : PhysicalResponsePoint) (leftMomentum rightMomentum : PhysicalMomentum)
    (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q leftMomentum rightMomentum)
      (sourcePhysicalClock leftMomentum rightMomentum left right)) (T : ℝ) (row : Fin 289) :
    ‖(sourcePhysicalDrivenField q leftMomentum rightMomentum left right frequency-
        sourcePhysicalWindowField q leftMomentum rightMomentum left right frequency T) row‖≤
      sourceDressedFieldEntryPrice (sourcePhysicalMediumPoint q leftMomentum rightMomentum)
        (sourcePhysicalClock leftMomentum rightMomentum left right) frequency row*
        ((‖frequency.val.val.val-sourcePhysicalClock leftMomentum rightMomentum left right‖⁻¹*
          Real.exp (-frequency.val.val.val.re*T))*‖sourcePhysicalCurrentAmplitude leftMomentum rightMomentum left right‖) :=by
  have difference : sourcePhysicalDrivenField q leftMomentum rightMomentum left right frequency-
      sourcePhysicalWindowField q leftMomentum rightMomentum left right frequency T=
    sourceDressedField (sourcePhysicalMediumPoint q leftMomentum rightMomentum)
      (sourcePhysicalClock leftMomentum rightMomentum left right) frequency
      (sourcePhysicalCurrentHalf leftMomentum rightMomentum left right frequency.val.val.val-
        sourcePhysicalCurrentWindow leftMomentum rightMomentum left right frequency.val.val.val T) :=by
    rw [sourcePhysicalDrivenField,sourcePhysicalWindowField,sourceDressedField,sourceDressedField,sourceDressedField,
      Matrix.mulVec_sub]
  rw [difference]
  have paid:=sourceDressedField_entryPrice (sourcePhysicalMediumPoint q leftMomentum rightMomentum)
    (sourcePhysicalClock leftMomentum rightMomentum left right) frequency
    (sourcePhysicalCurrentHalf leftMomentum rightMomentum left right frequency.val.val.val-
      sourcePhysicalCurrentWindow leftMomentum rightMomentum left right frequency.val.val.val T) row
  rw [sourcePhysicalCurrent_tailPrice _ _ _ _ _ (sourcePhysicalFrequency_positive q leftMomentum rightMomentum left right frequency) T] at paid
  exact paid

theorem sourcePhysicalDrivenField_generated (q : PhysicalResponsePoint) (leftMomentum rightMomentum : PhysicalMomentum)
    (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q leftMomentum rightMomentum)
      (sourcePhysicalClock leftMomentum rightMomentum left right)) :
    sourcePhysicalDrivenField q leftMomentum rightMomentum left right frequency=
      sourceCommonFieldUpdate (sourcePhysicalMediumPoint q leftMomentum rightMomentum)
        (sourcePhysicalClock leftMomentum rightMomentum left right) frequency.val.val
          (sourcePhysicalCurrentHalf leftMomentum rightMomentum left right frequency.val.val.val)
          (sourcePhysicalDrivenField q leftMomentum rightMomentum left right frequency) :=
  sourceDressedField_generated _ _ _ _

theorem sourcePhysicalDrivenField_native (q : PhysicalResponsePoint) (leftMomentum rightMomentum : PhysicalMomentum)
    (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q leftMomentum rightMomentum)
      (sourcePhysicalClock leftMomentum rightMomentum left right)) :
    nativeFourierHessian nativeHessian (fullMomentum
      (PreparationVacuumPhysicalFeedback.physicalSpatial (sourcePhysicalTransfer leftMomentum rightMomentum)) frequency.val.val.val)*ᵥ
        sourcePhysicalDrivenField q leftMomentum rightMomentum left right frequency=
      sourceDressedSource (sourcePhysicalMediumPoint q leftMomentum rightMomentum)
        (sourcePhysicalClock leftMomentum rightMomentum left right) frequency
          (sourcePhysicalCurrentHalf leftMomentum rightMomentum left right frequency.val.val.val)-
        originalRowLift (fullMomentum
          (PreparationVacuumPhysicalFeedback.physicalSpatial (sourcePhysicalTransfer leftMomentum rightMomentum)) frequency.val.val.val)*ᵥ
          sourceCompatibility (fullMomentum
            (PreparationVacuumPhysicalFeedback.physicalSpatial (sourcePhysicalTransfer leftMomentum rightMomentum)) frequency.val.val.val)
            (sourceDressedSource (sourcePhysicalMediumPoint q leftMomentum rightMomentum)
              (sourcePhysicalClock leftMomentum rightMomentum left right) frequency
                (sourcePhysicalCurrentHalf leftMomentum rightMomentum left right frequency.val.val.val)) :=
  sourceDressedField_native _ _ _ _

def sourcePhysicalDrivenCurvature (q : PhysicalResponsePoint) (leftMomentum rightMomentum : PhysicalMomentum)
    (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q leftMomentum rightMomentum)
      (sourcePhysicalClock leftMomentum rightMomentum left right)) : Fin 36→ℂ:=
  sourceDressedCurvature (sourcePhysicalMediumPoint q leftMomentum rightMomentum)
    (sourcePhysicalClock leftMomentum rightMomentum left right) frequency*ᵥ
    sourcePhysicalCurrentHalf leftMomentum rightMomentum left right frequency.val.val.val

theorem sourcePhysicalDrivenCurvature_actual (q : PhysicalResponsePoint) (leftMomentum rightMomentum : PhysicalMomentum)
    (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q leftMomentum rightMomentum)
      (sourcePhysicalClock leftMomentum rightMomentum left right)) :
    sourcePhysicalDrivenCurvature q leftMomentum rightMomentum left right frequency=
      originalReader36 (fullMomentum
        (PreparationVacuumPhysicalFeedback.physicalSpatial (sourcePhysicalTransfer leftMomentum rightMomentum)) frequency.val.val.val)*ᵥ
        sourcePhysicalDrivenField q leftMomentum rightMomentum left right frequency :=
  sourceDressedCurvature_actual _ _ _ _

def sourcePhysicalDrivenRead (q : PhysicalResponsePoint) (leftMomentum rightMomentum : PhysicalMomentum)
    (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q leftMomentum rightMomentum)
      (sourcePhysicalClock leftMomentum rightMomentum left right))
    (readerLeftMomentum readerRightMomentum : PhysicalMomentum) (readerLeft readerRight : RestStateIndex) : ℂ:=
  sourcePhysicalCurrentRead readerLeftMomentum readerRightMomentum readerLeft readerRight
    (sourcePhysicalDrivenField q leftMomentum rightMomentum left right frequency)

theorem sourcePhysicalDrivenRead_original (q : PhysicalResponsePoint) (leftMomentum rightMomentum : PhysicalMomentum)
    (left right : RestStateIndex)
    (frequency : sourceCurrentRegularDomain (sourcePhysicalMediumPoint q leftMomentum rightMomentum)
      (sourcePhysicalClock leftMomentum rightMomentum left right))
    (readerLeftMomentum readerRightMomentum : PhysicalMomentum) (readerLeft readerRight : RestStateIndex) :
    sourcePhysicalDrivenRead q leftMomentum rightMomentum left right frequency
      readerLeftMomentum readerRightMomentum readerLeft readerRight=
      sourceNativeGaugeCurrentComplex 0 (actualMovingPairPoint 0 readerLeftMomentum readerRightMomentum readerLeft readerRight)
        (fun i=>(sourcePhysicalDrivenField q leftMomentum rightMomentum left right frequency i).re)+
      Complex.I*sourceNativeGaugeCurrentComplex 0 (actualMovingPairPoint 0 readerLeftMomentum readerRightMomentum readerLeft readerRight)
        (fun i=>(sourcePhysicalDrivenField q leftMomentum rightMomentum left right frequency i).im) :=
  sourcePhysicalCurrentRead_original _ _ _ _ _

end LowEnergy.PreparationVacuumPhysicalCurrentLaplaceReturn
