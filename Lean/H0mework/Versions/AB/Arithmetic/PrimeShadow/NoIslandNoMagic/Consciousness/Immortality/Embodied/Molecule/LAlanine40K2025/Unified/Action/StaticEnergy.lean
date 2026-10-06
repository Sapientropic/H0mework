import H0mework.Versions.AB.Physics.MotherSource.StaticHamiltonian.Legendre
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.CanonicalSource

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.StaticEnergy
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineGlobalIntegratedAction StageNineCanonicalCauchyState
open Stage10.StaticHamiltonian Stage10.TemporalGauge Stage10.CanonicalGauss
open SU7MotherLieAlgebra SU7MotherGaugeTheory DiracExteriorMatterAction Stage9C.Material.SpinPair Stage9DEF
open StageNineP286GaugeConnectionVariation
open BasinRefinement SourceFiniteData SourceGaussianModel ContinuousGradient GaussSource
noncomputable section
attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

def backgroundDifference (potential : Potential) (space : StageNineSpatialPoint) : ℝ :=
  hamiltonianDensity Stage10.Runtime.source
    (Stage10.CanonicalGauss.withMatter potential Stage10.Runtime.configuration.matter Stage10.Runtime.configuration.conjugateMatter)
    (canonicalCauchySlicePoint 0 space) -
  hamiltonianDensity Stage10.Runtime.source
    (reference Stage10.Runtime.configuration.matter Stage10.Runtime.configuration.conjugateMatter) (canonicalCauchySlicePoint 0 space)

def pairDifference (potential : Potential) (first second : Basis) (scale : ℝ) (space : StageNineSpatialPoint) : ℝ :=
  hamiltonianDensity Stage10.Runtime.source (Stage10.CanonicalGauss.withMatter potential
    (preparedMatter second scale) (preparedDual first scale)) (canonicalCauchySlicePoint 0 space) -
  hamiltonianDensity Stage10.Runtime.source (reference (preparedMatter second scale) (preparedDual first scale))
    (canonicalCauchySlicePoint 0 space)

/-- The original D3 contracts matter responses; the shared gauge/gravity background is counted once. -/
def D3Difference (potential : Potential) (scale : ℝ) (space : StageNineSpatialPoint) : ℝ :=
  backgroundDifference potential space + ∑ first : Basis, ∑ second : Basis,
    (densityMatrix first second : ℝ)*(pairDifference potential first second scale space-backgroundDifference potential space)

theorem background_energy (potential : Potential) (regular : PotentialDifferentiable potential) (space : StageNineSpatialPoint) :
    backgroundDifference potential space = -lapse*squared (electric potential (canonicalCauchySlicePoint 0 space)) := by
  rw [backgroundDifference, original_hamiltonian_shift potential regular, CanonicalSource.original_current_zero, sub_zero]

theorem pair_response (potential : Potential) (regular : PotentialDifferentiable potential)
    (first second : Basis) (scale : ℝ) (space : StageNineSpatialPoint) :
    pairDifference potential first second scale space-backgroundDifference potential space =
      -(preparedDual first scale (canonicalCauchySlicePoint 0 space)
        (Compatibility.currentAction 0 (potential (canonicalCauchySlicePoint 0 space))
          (preparedMatter second scale (canonicalCauchySlicePoint 0 space)))).re := by
  rw [pairDifference, original_hamiltonian_shift potential regular, background_energy potential regular]
  ring

private theorem current_smul (amount : ℝ) (data : P286LieBlockData) (matter : DiracExteriorMatterCarrier) :
    Compatibility.currentAction 0 (amount • data) matter =
      (amount : ℂ) • Compatibility.currentAction 0 data matter := by
  simp [Compatibility.currentAction, p286LieBlockEmbed_real_smul,
    diracExteriorMotherLieAction_real_smul, smul_smul, mul_comm]
  let value : DiracExteriorMatterCarrier := diracMatrixMatterAction (DiracCliffordRepresentation.diracGamma 0)
    (diracExteriorMotherLieAction (p286LieBlockEmbed data) matter)
  change Complex.I • ((amount : ℂ) • value) = (Complex.I*(amount : ℂ)) • value
  simp only [smul_smul]

theorem original_D3_hamiltonian (potential : BasePoint → ℝ) (regular : Differentiable ℝ potential)
    (scale : ℝ) (space : StageNineSpatialPoint) :
    D3Difference (abelianPotential potential) scale space =
      -lapse*squared (electric (abelianPotential potential) (canonicalCauchySlicePoint 0 space)) +
        4*spinScale*potential (canonicalCauchySlicePoint 0 space)*sourceDensity (spatialPoint scale (canonicalCauchySlicePoint 0 space)) := by
  unfold D3Difference
  simp only [pair_response _ (abelian_differentiable potential regular)]
  rw [background_energy _ (abelian_differentiable potential regular)]
  simp only [abelianPotential,
    current_smul, map_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have response := D3_current scale (canonicalCauchySlicePoint 0 space)
  rw [ChargedSource.classical_D3_current] at response
  have move : (∑ first : Basis, ∑ second : Basis, (densityMatrix first second : ℝ)*
      -(potential (canonicalCauchySlicePoint 0 space)*
        (preparedDual first scale (canonicalCauchySlicePoint 0 space)
          (Compatibility.currentAction 0 Stage10.HyperchargeResponse.chargeDirection
            (preparedMatter second scale (canonicalCauchySlicePoint 0 space)))).re)) =
      -potential (canonicalCauchySlicePoint 0 space)*
        (∑ first : Basis, ∑ second : Basis, (densityMatrix first second : ℝ)*
          (preparedDual first scale (canonicalCauchySlicePoint 0 space)
            (Compatibility.currentAction 0 Stage10.HyperchargeResponse.chargeDirection
              (preparedMatter second scale (canonicalCauchySlicePoint 0 space)))).re) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro second _
    ring
  rw [move, response]
  simp
  ring

end
end LAlanine40K2025.UnifiedAction.StaticEnergy
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
