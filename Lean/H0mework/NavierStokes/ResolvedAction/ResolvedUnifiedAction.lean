import H0mework.NavierStokes.ResolvedAction.ResolvedUnifiedOperators

set_option autoImplicit false
open scoped ContDiff Topology BigOperators

namespace SaturationMonoid.NavierStokes.NativeResolvedUnifiedAction

open PhysicsCore.ProofFreeRicherAnholonomicSource PhysicsCore.StageNineHolonomicField PhysicsCore.Stage9CU
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open NativeWholeHistoryClock NativeWholeHistoryField NativeResolvedSpacetime NativeResolvedUnifiedOperators
open NativeStressSource NativeFluidSpatialOperators
open NativeFinitePrefixTimeChart (spatialRead)
open RationalVorticityEvaluator

noncomputable section

theorem slice_hasDerivAt (parameter : ℝ) (space : PhysicalSpace) :
    HasDerivAt (fun sample => slice sample space) (coordinateDirection 0) parameter := by
  have same : (fun sample => slice sample space) = fun sample => sample • coordinateDirection 0 + spatialEmbedding space := by
    funext sample
    unfold slice
    congr 1
    ext direction
    simp [coordinateDirection]
  rw [same]
  simpa using ((hasDerivAt_id parameter).smul_const (coordinateDirection 0)).add_const (spatialEmbedding space)

theorem resolved_hasDerivAt (modes : Finset IntegerWavevector) (parameter : ℝ) (space : PhysicalSpace) :
    HasDerivAt (fun sample => finiteRealComplexFourierField modes (vorticity sample) space)
      (clockRate parameter • projectedWholePhysicalTangent modes butterflyGainViscosity.coeff
        (vorticity parameter) space) parameter := by
  rw [← NativeResolvedSourceAction.finite_tangent_read]
  change HasDerivAt (fun sample => ∑ wave ∈ modes, realModeCLM wave space (vorticity sample wave))
    (clockRate parameter • ∑ wave ∈ modes, realModeCLM wave space
      (wholeLatticeVorticityFourierTangentAt butterflyGainViscosity.coeff (vorticity parameter) wave)) parameter
  rw [Finset.smul_sum]
  apply HasDerivAt.fun_sum
  intro wave _
  have source := (realModeCLM wave space).hasFDerivAt.comp_hasDerivAt parameter
    ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).hasFDerivAt.comp_hasDerivAt parameter
      (NativeWholeHistoryAction.vorticity_hasDerivAt parameter))
  change HasDerivAt (fun sample => realModeCLM wave space (vorticity sample wave))
    (realModeCLM wave space (clockRate parameter • NativeWholeHistoryAction.vorticityAction parameter wave)) parameter at source
  simpa only [map_smul, NativeWholeHistoryAction.vorticityAction_row] using source

theorem unified_time_action (modes : Finset IntegerWavevector) (point : BasePoint) :
    Fluid.coordinateDerivative (resolvedVorticity modes) 0 point =
      clockRate (point 0) • projectedWholePhysicalTangent modes butterflyGainViscosity.coeff
        (vorticity (point 0)) (spatialRead point) := by
  have original := ((resolvedVorticity_contDiff modes).differentiable (by simp)
    (slice (point 0) (spatialRead point))).hasFDerivAt.comp_hasDerivAt (point 0)
      (slice_hasDerivAt (point 0) (spatialRead point))
  have same : (fun sample => resolvedVorticity modes (slice sample (spatialRead point))) =
      fun sample => finiteRealComplexFourierField modes (vorticity sample) (spatialRead point) :=
    funext fun sample => congrFun (slice_vorticity modes sample) (spatialRead point)
  change HasDerivAt (fun sample => resolvedVorticity modes (slice sample (spatialRead point))) _ _ at original
  rw [slice_reconstruct, same] at original
  exact original.unique (resolved_hasDerivAt modes (point 0) (spatialRead point))

theorem source_native_correction (radius : ℕ) (point : BasePoint) :
    (clockRate (point 0))⁻¹ • Fluid.coordinateDerivative (resolvedVorticity (wholeRestartModes radius)) 0 point -
      (butterflyGainViscosity.coeff • Fluid.laplacian (resolvedVorticity (wholeRestartModes radius)) point +
        Fluid.curl (Fluid.cross (resolvedVelocity (wholeRestartModes radius)) (resolvedVorticity (wholeRestartModes radius))) point) =
      nativeTurbulenceCorrectionField (wholeRestartModes radius) (vorticity (point 0)) (spatialRead point) := by
  rw [unified_time_action, smul_smul, inv_mul_cancel₀ (clockRate_pos (point 0)).ne', one_smul,
    projectedWholePhysicalTangent_eq_classical_add_nativeTurbulence, Pi.add_apply, unified_classical_action]
  abel

theorem source_unified_evolution (radius : ℕ) (point : BasePoint) :
    Fluid.coordinateDerivative (resolvedVorticity (wholeRestartModes radius)) 0 point =
      clockRate (point 0) •
        (butterflyGainViscosity.coeff • Fluid.laplacian (resolvedVorticity (wholeRestartModes radius)) point +
          Fluid.curl (Fluid.cross (resolvedVelocity (wholeRestartModes radius)) (resolvedVorticity (wholeRestartModes radius))) point +
          nativeTurbulenceCorrectionField (wholeRestartModes radius) (vorticity (point 0)) (spatialRead point)) := by
  rw [unified_time_action, projectedWholePhysicalTangent_eq_classical_add_nativeTurbulence, Pi.add_apply, unified_classical_action]

end
end SaturationMonoid.NavierStokes.NativeResolvedUnifiedAction
