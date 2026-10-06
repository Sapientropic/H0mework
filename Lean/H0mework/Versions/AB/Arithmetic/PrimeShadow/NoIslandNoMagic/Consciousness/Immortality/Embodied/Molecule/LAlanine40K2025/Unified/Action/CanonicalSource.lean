import H0mework.Versions.AB.Physics.MotherSource.CanonicalGauss.Poisson
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.GaussSource

/-! The original AO and D3 fields directly force the same-source canonical Poisson equation. -/

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.CanonicalSource
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource
open StageNineHolonomicField StageNineGlobalIntegratedAction SU7MotherLieAlgebra
open StageNineP286GaugeAuxiliaryVariation StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineCanonicalCauchyState
open DiracExteriorMatterAction Stage9C.Material.SpinPair Stage9DEF
open Stage10.ChargedPreparation Stage10.TemporalGauge Stage10.CanonicalGauss
open BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient
open GaussSource
noncomputable section
attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

def backgroundEuler (potential : Potential) (space : StageNineSpatialPoint) (data : P286LieBlockData) : ℝ :=
  p286CoordinateLiePairing (p286CoordinateEquiv data)
    (holonomicFormNativeP286GaugeEulerThreeForm Stage10.Runtime.source 0
      (Stage10.CanonicalGauss.withMatter potential Stage10.Runtime.configuration.matter
        Stage10.Runtime.configuration.conjugateMatter) (canonicalCauchySlicePoint 0 space) 3)

def preparedEuler (potential : Potential) (first second : Basis) (scale : ℝ)
    (space : StageNineSpatialPoint) (data : P286LieBlockData) : ℝ :=
  p286CoordinateLiePairing (p286CoordinateEquiv data)
    (holonomicFormNativeP286GaugeEulerThreeForm Stage10.Runtime.source 0
      (Stage10.CanonicalGauss.withMatter potential (preparedMatter second scale) (preparedDual first scale))
      (canonicalCauchySlicePoint 0 space) 3)

def D3Euler (potential : Potential) (scale : ℝ) (space : StageNineSpatialPoint) (data : P286LieBlockData) : ℝ :=
  backgroundEuler potential space data + ∑ first : Basis, ∑ second : Basis,
    (densityMatrix first second : ℝ) *
      (preparedEuler potential first second scale space data-backgroundEuler potential space data)

theorem original_current_zero (point : BasePoint) (data : P286LieBlockData) :
    (Stage10.Runtime.configuration.conjugateMatter point
      (Compatibility.currentAction 0 data (Stage10.Runtime.configuration.matter point))).re = 0 := by
  have original := congrArg Complex.re (Stage10.TemporalGauge.temporal_dual_zero data point)
  exact original

theorem background_gauss (potential : Potential) (smooth : PotentialDifferentiable potential)
    (space : StageNineSpatialPoint) (regular : ElectricDifferentiableAt potential (canonicalCauchySlicePoint 0 space))
    (data : P286LieBlockData) :
    backgroundEuler potential space data =
      2*lapse*p286LiePairing data (divergence potential (canonicalCauchySlicePoint 0 space)) := by
  rw [backgroundEuler, Stage10.CanonicalGauss.gauss_projection potential smooth _ _ space regular,
    original_current_zero, add_zero]

theorem prepared_euler_response (potential : Potential) (smooth : PotentialDifferentiable potential)
    (first second : Basis) (scale : ℝ) (space : StageNineSpatialPoint)
    (regular : ElectricDifferentiableAt potential (canonicalCauchySlicePoint 0 space)) (data : P286LieBlockData) :
    preparedEuler potential first second scale space data-backgroundEuler potential space data =
      (preparedDual first scale (canonicalCauchySlicePoint 0 space)
        (Compatibility.currentAction 0 data (preparedMatter second scale (canonicalCauchySlicePoint 0 space)))).re := by
  rw [preparedEuler, Stage10.CanonicalGauss.gauss_projection potential smooth _ _ space regular,
    background_gauss potential smooth space regular]
  ring

theorem original_D3_gauss (potential : Potential) (smooth : PotentialDifferentiable potential)
    (scale : ℝ) (space : StageNineSpatialPoint)
    (regular : ElectricDifferentiableAt potential (canonicalCauchySlicePoint 0 space)) :
    D3Euler potential scale space Stage10.HyperchargeResponse.chargeDirection =
      2*lapse*p286LiePairing Stage10.HyperchargeResponse.chargeDirection
        (divergence potential (canonicalCauchySlicePoint 0 space)) -
      4*spinScale*sourceDensity (spatialPoint scale (canonicalCauchySlicePoint 0 space)) := by
  simp only [D3Euler, prepared_euler_response potential smooth _ _ scale space regular]
  rw [D3_current, ChargedSource.classical_D3_current, background_gauss potential smooth space regular]
  simp
  ring

theorem original_D3_poisson (potential : BasePoint → ℝ) (regular : ScalarRegular potential)
    (scale : ℝ) (space : StageNineSpatialPoint) :
    D3Euler (abelianPotential potential) scale space Stage10.HyperchargeResponse.chargeDirection =
      -(2*lapse)*spatialLaplacian potential (canonicalCauchySlicePoint 0 space) -
        4*spinScale*sourceDensity (spatialPoint scale (canonicalCauchySlicePoint 0 space)) := by
  rw [original_D3_gauss _ (abelian_differentiable potential regular.1) _ _
    (abelian_electric_regular potential regular _), abelian_divergence potential regular,
    p286LiePairing_smul_right, charge_pairing]
  ring

end
end LAlanine40K2025.UnifiedAction.CanonicalSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
