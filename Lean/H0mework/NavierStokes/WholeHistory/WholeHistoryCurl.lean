import H0mework.NavierStokes.WholeHistory.WholeHistoryAction

set_option autoImplicit false
open scoped ContDiff Topology

namespace SaturationMonoid.NavierStokes.NativeWholeHistoryCurl

open Set
open PhysicsCore.ProofFreeRicherAnholonomicSource PhysicsCore.StageNineHolonomicField
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open NativeFullOrderSynthesis NativeFullOrderAction NativeMixedTimeSpace NativeReceiptTimeProfile
open NativeWholeHistoryClock NativeWholeHistoryField
open NativeFinitePrefixTimeChart (spatialRead)
open NativeTimeChartVorticityReadout (spatialCurl spatialCurl_of_fourier)

noncomputable section

theorem velocity_moments (parameter : ℝ) (order : ℕ) :
    Summable fun wave => frequencySize wave ^ order * amplitude (velocity parameter) wave := by
  have inside : physicalTime parameter ∈ Icc (window (cover parameter)).first (window (cover parameter)).last :=
    ⟨(physicalTime_pos parameter).le, (cover_spec parameter).le⟩
  unfold velocity
  rw [← NativeReceiptSpacetime.velocity_read (window (cover parameter)) _ inside]
  exact summable_moment_of_square _ order
    (profile_square_moments (jets (window (cover parameter)) 0) (order + 2) _).1

theorem vorticity_paid (parameter : ℝ) : Summable (amplitude (vorticity parameter)) := by
  have inside : physicalTime parameter ∈ Icc (window (cover parameter)).first (window (cover parameter)).last :=
    ⟨(physicalTime_pos parameter).le, (cover_spec parameter).le⟩
  unfold vorticity
  rw [← NativeReceiptSpacetime.vorticity_read (window (cover parameter)) _ inside]
  simpa only [pow_zero, one_mul] using summable_moment_of_square _ 0
    (profile_square_moments (NativeReceiptSpacetime.vorticityFamily (window (cover parameter)) 0) 2 _).1

theorem curl_row (parameter : ℝ) (wave : IntegerWavevector) :
    fourierCurlCoefficient wave (velocity parameter wave) = vorticity parameter wave := by
  change fourierCurlCoefficient wave (biotSavartVelocityCoefficient wave (vorticity parameter wave)) = _
  by_cases nonzero : wave ≠ 0
  · exact fourierCurlCoefficient_biotSavartVelocityCoefficient_of_transverse wave _ nonzero
      (NativeReceiptSpacetime.state_transverse (receipt (cover parameter)) (physicalTime parameter) wave)
  · have zero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    rw [show vorticity parameter 0 = 0 from NativeReceiptSpacetime.state_zero _ _]
    simp [fourierCurlCoefficient]

theorem spatial_curl (parameter : ℝ) (space : PhysicalSpace) :
    spatialCurl (spatialField (velocity parameter)) space = spatialField (vorticity parameter) space :=
  spatialCurl_of_fourier _ _ (velocity_moments parameter) (vorticity_paid parameter) (curl_row parameter) space

theorem spatial_curve (point : BasePoint) (direction : Coordinate) (amount : ℝ) :
    field (point + amount • coordinateDirection direction.succ) =
      spatialField (velocity (point 0)) (spatialRead point + amount • EuclideanSpace.single direction 1) := by
  have temporal : (point + amount • coordinateDirection direction.succ) 0 = point 0 := by
    simp [coordinateDirection, PiLp.add_apply, PiLp.smul_apply]
  have spatial : spatialRead (point + amount • coordinateDirection direction.succ) =
      spatialRead point + amount • EuclideanSpace.single direction 1 := by
    ext output
    simp [spatialRead, coordinateDirection, PiLp.add_apply, PiLp.smul_apply]
  rw [field, temporal, spatial]

theorem spatial_derivative (point : BasePoint) (direction : Coordinate) :
    PhysicsCore.Stage9CU.Fluid.coordinateDerivative field direction.succ point =
      fderiv ℝ (spatialField (velocity (point 0))) (spatialRead point) (EuclideanSpace.single direction 1) := by
  have curve : HasDerivAt (fun amount : ℝ => point + amount • coordinateDirection direction.succ)
      (coordinateDirection direction.succ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateDirection direction.succ)).const_add point
  have left := (field_contDiff.differentiable (by simp)
    (point + 0 • coordinateDirection direction.succ)).hasFDerivAt.comp_hasDerivAt 0 curve
  have spatialCurve : HasDerivAt (fun amount : ℝ => spatialRead point + amount • EuclideanSpace.single direction 1)
      (EuclideanSpace.single direction 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single direction 1 : PhysicalSpace)).const_add (spatialRead point)
  have right := ((spatialField_smooth _ (velocity_moments (point 0))).differentiable (by simp)
    (spatialRead point + 0 • EuclideanSpace.single direction 1)).hasFDerivAt.comp_hasDerivAt 0 spatialCurve
  simp only [zero_smul, add_zero] at left right
  have same : (fun amount : ℝ => field (point + amount • coordinateDirection direction.succ)) =
      fun amount => spatialField (velocity (point 0)) (spatialRead point + amount • EuclideanSpace.single direction 1) :=
    funext (spatial_curve point direction)
  change HasDerivAt (fun amount => field (point + amount • coordinateDirection direction.succ)) _ _ at left
  rw [same] at left
  exact left.unique right

theorem unified_curl_original (point : BasePoint) :
    PhysicsCore.Stage9CU.Fluid.curl field point = spatialField (vorticity (point 0)) (spatialRead point) := by
  rw [← spatial_curl]
  change WithLp.toLp 2 ![
    PhysicsCore.Stage9CU.Fluid.coordinateDerivative field (1 : Fin 3).succ point 2 -
      PhysicsCore.Stage9CU.Fluid.coordinateDerivative field (2 : Fin 3).succ point 1,
    PhysicsCore.Stage9CU.Fluid.coordinateDerivative field (2 : Fin 3).succ point 0 -
      PhysicsCore.Stage9CU.Fluid.coordinateDerivative field (0 : Fin 3).succ point 2,
    PhysicsCore.Stage9CU.Fluid.coordinateDerivative field (0 : Fin 3).succ point 1 -
      PhysicsCore.Stage9CU.Fluid.coordinateDerivative field (1 : Fin 3).succ point 0] = _
  simp only [spatial_derivative, spatialCurl]

theorem unified_curl_hasDerivAt (parameter : ℝ) (space : PhysicalSpace) :
    HasDerivAt (fun sample => PhysicsCore.Stage9CU.Fluid.curl field
      (PhysicsCore.StageNineCanonicalCauchyState.canonicalCauchySlicePoint sample space))
      (clockRate parameter • spatialField (NativeWholeHistoryAction.vorticityAction parameter) space) parameter := by
  have spaceRead (sample : ℝ) : spatialRead
      (PhysicsCore.StageNineCanonicalCauchyState.canonicalCauchySlicePoint sample space) = space := by
    apply PiLp.ext
    intro direction
    exact PhysicsCore.StageNineCanonicalCauchyState.canonicalCauchySlicePoint_spatial sample space direction
  have timeRead (sample : ℝ) :
      PhysicsCore.StageNineCanonicalCauchyState.canonicalCauchySlicePoint sample space 0 = sample :=
    PhysicsCore.StageNineCanonicalCauchyState.canonicalCauchySlicePoint_time sample space
  simp only [unified_curl_original, spaceRead, timeRead]
  exact NativeWholeHistoryAction.physical_vorticity_hasDerivAt parameter space

end
end SaturationMonoid.NavierStokes.NativeWholeHistoryCurl
