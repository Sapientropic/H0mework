import H0mework.Versions.X.NavierStokes.SourceAction.ChartPhaseWard
import H0mework.Physics.Fluid.Differential

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeTimeChartVorticityReadout

open Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeFullOrderSynthesis NativeFullOrderAction NativeMixedTimeSpace NativeReceiptTimeProfile
open NativeFinitePrefixTimeChart NativeTimeChartPhaseWard
open PhysicsCore.ProofFreeRicherAnholonomicSource PhysicsCore.StageNineHolonomicField

noncomputable section

def derivativeRead (direction output : Coordinate) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 1 => PhysicalSpace) PhysicalSpace →L[ℝ] ℝ :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Coordinate => ℝ) output).comp
    (evaluateJet 1 (fun _ => EuclideanSpace.single direction 1))

def curlRead : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => PhysicalSpace) PhysicalSpace →L[ℝ] PhysicalSpace :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![derivativeRead 1 2 - derivativeRead 2 1,
      derivativeRead 2 0 - derivativeRead 0 2, derivativeRead 0 1 - derivativeRead 1 0])

theorem curlRead_apply (jet : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => PhysicalSpace) PhysicalSpace) :
    curlRead jet = WithLp.toLp 2 ![
      (jet (fun _ => EuclideanSpace.single 1 1)) 2 - (jet (fun _ => EuclideanSpace.single 2 1)) 1,
      (jet (fun _ => EuclideanSpace.single 2 1)) 0 - (jet (fun _ => EuclideanSpace.single 0 1)) 2,
      (jet (fun _ => EuclideanSpace.single 0 1)) 1 - (jet (fun _ => EuclideanSpace.single 1 1)) 0] := by
  ext output
  fin_cases output <;> rfl

def spatialCurl (field : PhysicalSpace → PhysicalSpace) (point : PhysicalSpace) : PhysicalSpace :=
  WithLp.toLp 2 ![
    (fderiv ℝ field point (EuclideanSpace.single 1 1)) 2 - (fderiv ℝ field point (EuclideanSpace.single 2 1)) 1,
    (fderiv ℝ field point (EuclideanSpace.single 2 1)) 0 - (fderiv ℝ field point (EuclideanSpace.single 0 1)) 2,
    (fderiv ℝ field point (EuclideanSpace.single 0 1)) 1 - (fderiv ℝ field point (EuclideanSpace.single 1 1)) 0]

theorem curlRead_iterated (field : PhysicalSpace → PhysicalSpace) (point : PhysicalSpace) :
    curlRead (iteratedFDeriv ℝ 1 field point) = spatialCurl field point := by
  rw [curlRead_apply]
  simp only [iteratedFDeriv_one_apply, spatialCurl]

theorem mode_curl (velocity : ComplexVorticityHilbertState) (wave : IntegerWavevector) (point : PhysicalSpace) :
    curlRead (iteratedFDeriv ℝ 1 (mode velocity wave) point) =
      WithLp.toLp 2 (fun output =>
        (fourierCurlCoefficient wave (velocity wave) output * UnitAddTorus.mFourier wave (circlePoint point)).re) := by
  rw [curlRead_apply]
  simp_rw [mode_word_eq]
  simp only [Fin.prod_univ_one, pow_one, phase_single]
  ext output
  fin_cases output <;>
    simp [value, fourierCurlCoefficient, cross_apply, complexWavevector, Complex.real_smul,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem spatialCurl_of_fourier (velocity vorticity : ComplexVorticityHilbertState)
    (moments : ∀ order : ℕ, Summable fun wave => frequencySize wave ^ order * amplitude velocity wave)
    (vorticityPaid : Summable (amplitude vorticity))
    (action : ∀ wave, fourierCurlCoefficient wave (velocity wave) = vorticity wave) (point : PhysicalSpace) :
    spatialCurl (spatialField velocity) point = spatialField vorticity point := by
  have paid : Summable fun wave => iteratedFDeriv ℝ 1 (mode velocity wave) point :=
    ((moments 1).mul_left ((2 * Real.pi) ^ 1)).of_norm_bounded (fun wave => mode_iterated_bound velocity wave 1 point)
  have written := curlRead.map_tsum paid
  rw [← spatialField_iterated_eq velocity moments 1 point, curlRead_iterated] at written
  rw [written, spatialField_eq_tsum vorticity vorticityPaid]
  apply tsum_congr
  intro wave
  rw [mode_curl, action wave]
  rfl

def sourceState (index : ℕ) (parameter : ℝ) : ComplexVorticityHilbertState :=
  NativeReceiptSpacetime.state (receipt index) (physicalTime index parameter)

theorem source_curl_row (index : ℕ) (parameter : ℝ) (wave : IntegerWavevector) :
    fourierCurlCoefficient wave (velocity index parameter wave) = sourceState index parameter wave := by
  change fourierCurlCoefficient wave (biotSavartVelocityCoefficient wave (sourceState index parameter wave)) = _
  by_cases nonzero : wave ≠ 0
  · exact fourierCurlCoefficient_biotSavartVelocityCoefficient_of_transverse wave _ nonzero
      (NativeReceiptSpacetime.state_transverse (receipt index) (physicalTime index parameter) wave)
  · have zero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    rw [show sourceState index parameter 0 = 0 from NativeReceiptSpacetime.state_zero _ _]
    simp [fourierCurlCoefficient]

theorem source_vorticity_paid (index : ℕ) (parameter : ℝ) : Summable (amplitude (sourceState index parameter)) := by
  have inside : physicalTime index parameter ∈ Icc (window index).first (window index).last :=
    ⟨(physicalTime_mem index parameter).1.le, (physicalTime_mem index parameter).2.le⟩
  unfold sourceState
  rw [← NativeReceiptSpacetime.vorticity_read (window index) _ inside]
  simpa only [pow_zero, one_mul] using summable_moment_of_square _ 0
    (profile_square_moments (NativeReceiptSpacetime.vorticityFamily (window index) 0) 2 _).1

theorem source_spatial_curl (index : ℕ) (parameter : ℝ) (point : PhysicalSpace) :
    spatialCurl (spatialField (velocity index parameter)) point = spatialField (sourceState index parameter) point :=
  spatialCurl_of_fourier _ _ (velocity_moments index parameter) (source_vorticity_paid index parameter)
    (source_curl_row index parameter) point

theorem chart_spatial_curve (index : ℕ) (point : BasePoint) (direction : Coordinate) (amount : ℝ) :
    field index (point + amount • coordinateDirection direction.succ) =
      spatialField (velocity index (point 0)) (spatialRead point + amount • EuclideanSpace.single direction 1) := by
  have temporal : (point + amount • coordinateDirection direction.succ) 0 = point 0 := by
    simp [coordinateDirection, PiLp.add_apply, PiLp.smul_apply]
  have spatial : spatialRead (point + amount • coordinateDirection direction.succ) =
      spatialRead point + amount • EuclideanSpace.single direction 1 := by
    ext output
    simp [spatialRead, coordinateDirection, PiLp.add_apply, PiLp.smul_apply]
  change spatialField (NativeReceiptSpacetime.velocity (receipt index)
    (physicalTime index ((point + amount • coordinateDirection direction.succ) 0)))
      (spatialRead (point + amount • coordinateDirection direction.succ)) = _
  rw [temporal, spatial]
  rfl

theorem chart_spatial_derivative (index : ℕ) (point : BasePoint) (direction : Coordinate) :
    PhysicsCore.Stage9CU.Fluid.coordinateDerivative (field index) direction.succ point =
      fderiv ℝ (spatialField (velocity index (point 0))) (spatialRead point) (EuclideanSpace.single direction 1) := by
  have curve : HasDerivAt (fun amount : ℝ => point + amount • coordinateDirection direction.succ)
      (coordinateDirection direction.succ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateDirection direction.succ)).const_add point
  have left := ((field_contDiff index).differentiable (by simp)
    (point + 0 • coordinateDirection direction.succ)).hasFDerivAt.comp_hasDerivAt 0 curve
  have spatialCurve : HasDerivAt (fun amount : ℝ => spatialRead point + amount • EuclideanSpace.single direction 1)
      (EuclideanSpace.single direction 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single direction 1 : PhysicalSpace)).const_add (spatialRead point)
  have right := ((spatialField_smooth _ (velocity_moments index (point 0))).differentiable (by simp)
    (spatialRead point + 0 • EuclideanSpace.single direction 1)).hasFDerivAt.comp_hasDerivAt 0 spatialCurve
  simp only [zero_smul, add_zero] at left right
  have same : (fun amount : ℝ => field index (point + amount • coordinateDirection direction.succ)) =
      fun amount => spatialField (velocity index (point 0)) (spatialRead point + amount • EuclideanSpace.single direction 1) :=
    funext (chart_spatial_curve index point direction)
  change HasDerivAt (fun amount => field index (point + amount • coordinateDirection direction.succ)) _ _ at left
  rw [same] at left
  exact left.unique right

theorem unified_curl_original (index : ℕ) (point : BasePoint) :
    PhysicsCore.Stage9CU.Fluid.curl (field index) point = spatialField (sourceState index (point 0)) (spatialRead point) := by
  rw [← source_spatial_curl]
  change WithLp.toLp 2 ![
    PhysicsCore.Stage9CU.Fluid.coordinateDerivative (field index) (1 : Fin 3).succ point 2 -
      PhysicsCore.Stage9CU.Fluid.coordinateDerivative (field index) (2 : Fin 3).succ point 1,
    PhysicsCore.Stage9CU.Fluid.coordinateDerivative (field index) (2 : Fin 3).succ point 0 -
      PhysicsCore.Stage9CU.Fluid.coordinateDerivative (field index) (0 : Fin 3).succ point 2,
    PhysicsCore.Stage9CU.Fluid.coordinateDerivative (field index) (0 : Fin 3).succ point 1 -
      PhysicsCore.Stage9CU.Fluid.coordinateDerivative (field index) (1 : Fin 3).succ point 0] = _
  simp only [chart_spatial_derivative, spatialCurl]

theorem unified_curl_physical_read (index : ℕ) (actual : ℝ)
    (inside : actual ∈ Ioo (0 : ℝ) (duration index)) (space : PhysicalSpace) :
    PhysicsCore.Stage9CU.Fluid.curl (field index) (sourcePoint index actual space) =
      spatialField ((receipt index).wholePath ⟨actual, inside.1.le, inside.2.le⟩) space := by
  rw [unified_curl_original, sourcePoint_time, spatialRead_sourcePoint]
  unfold sourceState
  rw [physicalTime_inverse index actual inside,
    NativeReceiptSpacetime.state_on_interval (receipt index) ⟨actual, inside.1.le, inside.2.le⟩]

theorem unified_curl_contact (index : ℕ) (space : PhysicalSpace) :
    PhysicsCore.Stage9CU.Fluid.curl (field index) (sourcePoint index (contactTime index) space) =
      spatialField (run stackedShortCurrent index).contact.physicalState space := by
  rw [unified_curl_physical_read index _ (contactTime_mem index), contact_state]

theorem unified_curl_next (index : ℕ) (space : PhysicalSpace) :
    PhysicsCore.Stage9CU.Fluid.curl (field index) (sourcePoint index (nextContactTime index) space) =
      spatialField (run stackedShortCurrent index).next.contact.physicalState space := by
  rw [unified_curl_physical_read index _ (nextContactTime_mem index), next_contact_state]

end
end SaturationMonoid.NavierStokes.NativeTimeChartVorticityReadout
