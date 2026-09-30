import H0mework.Versions.X.NavierStokes.ResolvedAction.ResolvedSpacetime

set_option autoImplicit false
open scoped ContDiff

namespace SaturationMonoid.NavierStokes.NativeResolvedUnifiedOperators

open PhysicsCore.ProofFreeRicherAnholonomicSource PhysicsCore.Stage9CU
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFullVorticityStretching
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open NativeWholeHistoryClock NativeWholeHistoryField NativeResolvedSpacetime
open NativeFluidSpatialOperators
open NativeFinitePrefixTimeChart (spatialRead)

noncomputable section

def source (radius : ℕ) (parameter : ℝ) : RawVorticityFourierSource :=
  NativeResolvedNonlinearReadout.source radius (vorticity parameter)

theorem source_transverse (parameter : ℝ) : WholeStateTransverse (vorticity parameter) :=
  NativeReceiptSpacetime.state_transverse (receipt (cover parameter)) (physicalTime parameter)

theorem source_reality (parameter : ℝ) : FiniteStateFourierReality (vorticity parameter) :=
  NativePhysicalSource.receipt_reality _ _

theorem physical_vorticity_read (radius : ℕ) (parameter : ℝ) :
    physicalVorticity (source radius parameter) = finiteRealComplexFourierField (wholeRestartModes radius) (vorticity parameter) :=
  NativeResolvedNonlinearReadout.vorticity_read radius _ (source_transverse parameter) (source_reality parameter)

theorem physical_velocity_read (radius : ℕ) (parameter : ℝ) :
    physicalVelocity (source radius parameter) = finiteRealComplexFourierField (wholeRestartModes radius)
      (fun wave => biotSavartVelocityCoefficient wave (vorticity parameter wave)) :=
  NativeResolvedNonlinearReadout.velocity_read radius _ (source_transverse parameter) (source_reality parameter)

theorem slice_vorticity_source (radius : ℕ) (parameter : ℝ) :
    restrict (resolvedVorticity (wholeRestartModes radius)) parameter = physicalVorticity (source radius parameter) := by
  rw [slice_vorticity, physical_vorticity_read]

theorem slice_velocity_source (radius : ℕ) (parameter : ℝ) :
    restrict (resolvedVelocity (wholeRestartModes radius)) parameter = physicalVelocity (source radius parameter) := by
  rw [slice_velocity, physical_velocity_read]

theorem slice_reconstruct (point : BasePoint) : slice (point 0) (spatialRead point) = point := by
  apply PiLp.ext
  intro direction
  refine Fin.cases ?_ (fun coordinate => ?_) direction
  · exact slice_time _ _
  · exact slice_spatial _ _ coordinate

theorem unified_curl (radius : ℕ) :
    Fluid.curl (resolvedVelocity (wholeRestartModes radius)) = resolvedVorticity (wholeRestartModes radius) := by
  funext point
  have original := congrFun (curl_restrict _ (resolvedVelocity_contDiff (wholeRestartModes radius)) (point 0)) (spatialRead point)
  rw [slice_velocity_source, vorticityField_physicalVelocity] at original
  have read := congrFun (slice_vorticity_source radius (point 0)) (spatialRead point)
  change resolvedVorticity _ (slice (point 0) (spatialRead point)) = _ at read
  change _ = Fluid.curl _ (slice (point 0) (spatialRead point)) at original
  rw [slice_reconstruct] at original read
  exact original.symm.trans read.symm

theorem unified_laplacian (radius : ℕ) (point : BasePoint) :
    Fluid.laplacian (resolvedVorticity (wholeRestartModes radius)) point =
      spatialLaplacian (physicalVorticity (source radius (point 0))) (spatialRead point) := by
  have original := congrFun (laplacian_restrict _ (resolvedVorticity_contDiff (wholeRestartModes radius)) (point 0)) (spatialRead point)
  rw [slice_vorticity_source] at original
  change _ = Fluid.laplacian _ (slice (point 0) (spatialRead point)) at original
  rw [slice_reconstruct] at original
  exact original.symm

theorem unified_nonlinear (radius : ℕ) (point : BasePoint) :
    Fluid.curl (Fluid.cross (resolvedVelocity (wholeRestartModes radius)) (resolvedVorticity (wholeRestartModes radius))) point =
      resolvedWholeNonlinearField (wholeRestartModes radius) (vorticity (point 0)) (spatialRead point) := by
  have original := congrFun (NativeFluidCurlCross.curl_cross_restrict _ _
    (resolvedVelocity_contDiff (wholeRestartModes radius)) (resolvedVorticity_contDiff (wholeRestartModes radius)) (point 0))
    (spatialRead point)
  rw [slice_velocity_source, slice_vorticity_source, ← NativeFluidCurlCross.source_nonlinear_curl] at original
  change _ = Fluid.curl _ (slice (point 0) (spatialRead point)) at original
  rw [slice_reconstruct] at original
  rw [NativeResolvedNonlinearReadout.resolved_nonlinear_read radius _ (source_transverse (point 0)) (source_reality (point 0))]
  exact original.symm

theorem unified_classical_action (radius : ℕ) (viscosity : ℝ) (point : BasePoint) :
    resolvedClassicalPhysicalTangent (wholeRestartModes radius) viscosity (vorticity (point 0)) (spatialRead point) =
      viscosity • Fluid.laplacian (resolvedVorticity (wholeRestartModes radius)) point +
        Fluid.curl (Fluid.cross (resolvedVelocity (wholeRestartModes radius)) (resolvedVorticity (wholeRestartModes radius))) point := by
  rw [unified_laplacian, unified_nonlinear, physical_vorticity_read]
  change resolvedWholeNonlinearField _ _ _ - resolvedViscousField _ _ _ _ = _
  rw [NativeResolvedViscousReadout.resolved_viscous_read]
  simp only [neg_smul, sub_neg_eq_add]
  abel

end
end SaturationMonoid.NavierStokes.NativeResolvedUnifiedOperators
