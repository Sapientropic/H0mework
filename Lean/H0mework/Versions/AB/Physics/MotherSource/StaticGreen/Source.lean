import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.Green
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.CanonicalSource

/-! The Green identity directly consumes the original full U Euler three-form through the same molecular spatial coordinates. -/

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineCanonicalCauchyState StageNineCoframeLocalDifferentiability
open SU7MotherLieAlgebra Stage9C.Material.SpinPair
open scoped SchwartzMap LineDeriv
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb UnifiedAction
noncomputable section
attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

def sourceSpatialMap (scale : ℝ) : BasePoint →L[ℝ] Point :=
  ContinuousLinearMap.pi (fun i => scale • (EuclideanSpace.proj i.succ : BasePoint →L[ℝ] ℝ))

theorem sourceSpatialMap_apply (scale : ℝ) (point : BasePoint) :
    sourceSpatialMap scale point = spatialPoint scale point := rfl

theorem sourceSpatialMap_direction (scale : ℝ) (index : Fin 3) :
    sourceSpatialMap scale (coordinateDirection index.succ) = scale • axis index := by
  funext i
  simp [sourceSpatialMap, coordinateDirection, axis, Pi.single_apply]

def sourceTest (scale : ℝ) (test : 𝓢(Point, ℝ)) (point : BasePoint) : ℝ :=
  test (spatialPoint scale point)

theorem sourceTest_differentiable (scale : ℝ) (test : 𝓢(Point, ℝ)) :
    Differentiable ℝ (sourceTest scale test) :=
  test.differentiable.comp (sourceSpatialMap scale).differentiable

theorem sourceTest_derivative (scale : ℝ) (test : 𝓢(Point, ℝ)) (point : BasePoint) (index : Fin 3) :
    fieldDirectionalDerivative (sourceTest scale test) point index.succ =
      scale*(∂_{axis index} test) (spatialPoint scale point) := by
  have generated := (SchwartzMap.hasFDerivAt test (sourceSpatialMap scale point)).comp point
    (sourceSpatialMap scale).hasFDerivAt
  change HasFDerivAt (sourceTest scale test) _ point at generated
  unfold fieldDirectionalDerivative
  rw [generated.fderiv]
  simp only [ContinuousLinearMap.comp_apply, sourceSpatialMap_direction, map_smul, smul_eq_mul]
  rfl

theorem sourceTest_regular (scale : ℝ) (test : 𝓢(Point, ℝ)) :
    CanonicalGauss.ScalarRegular (sourceTest scale test) := by
  refine ⟨sourceTest_differentiable scale test, ?_⟩
  intro index
  simp only [sourceTest_derivative]
  exact (sourceTest_differentiable scale (∂_{axis index} test)).const_mul scale

theorem sourceTest_laplacian (scale : ℝ) (test : 𝓢(Point, ℝ)) (point : BasePoint) :
    CanonicalGauss.spatialLaplacian (sourceTest scale test) point =
      scale^2*testLaplacian test (spatialPoint scale point) := by
  unfold CanonicalGauss.spatialLaplacian
  simp only [sourceTest_derivative]
  have derivative (index : Fin 3) :
      fieldDirectionalDerivative (fun p => scale*(∂_{axis index} test) (spatialPoint scale p))
        point index.succ = scale^2*(∂_{axis index} (∂_{axis index} test)) (spatialPoint scale point) := by
    unfold fieldDirectionalDerivative
    change (fderiv ℝ (fun p => scale*sourceTest scale (∂_{axis index} test) p) point)
      (coordinateDirection index.succ) = _
    rw [((sourceTest_differentiable scale (∂_{axis index} test) point).hasFDerivAt.const_mul scale).fderiv]
    change scale*fieldDirectionalDerivative (sourceTest scale (∂_{axis index} test)) point index.succ = _
    rw [sourceTest_derivative]
    ring
  simp only [derivative, testLaplacian, sum_apply, Finset.mul_sum]

theorem slice_source_coordinates (point : Point) :
    spatialPoint 1 (canonicalCauchySlicePoint 0 (WithLp.toLp 2 point)) = point := by
  funext i
  simp [spatialPoint, canonicalCauchySlicePoint, Pi.single_apply]

def sourceEuler (test : 𝓢(Point, ℝ)) (point : Point) : ℝ :=
  p286CoordinateLiePairing (p286CoordinateEquiv HyperchargeResponse.chargeDirection)
    (holonomicFormNativeP286GaugeEulerThreeForm Stage10.Runtime.source 0
      (CanonicalGauss.withMatter (CanonicalGauss.abelianPotential (sourceTest 1 test))
        Stage10.Runtime.configuration.matter Stage10.Runtime.configuration.conjugateMatter)
      (canonicalCauchySlicePoint 0 (WithLp.toLp 2 point)) 3)

theorem sourceEuler_laplacian (test : 𝓢(Point, ℝ)) (point : Point) :
    sourceEuler test point = -(2*lapse)*testLaplacian test point := by
  rw [sourceEuler, CanonicalGauss.poisson_gauss _ (sourceTest_regular 1 test),
    CanonicalSource.original_current_zero, add_zero, sourceTest_laplacian,
    slice_source_coordinates]
  simp

theorem green_original_euler (test : 𝓢(Point, ℝ)) :
    (∫ point : Point, green point*sourceEuler test point) = test 0 := by
  simp only [sourceEuler_laplacian]
  exact green_fundamental test

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen
