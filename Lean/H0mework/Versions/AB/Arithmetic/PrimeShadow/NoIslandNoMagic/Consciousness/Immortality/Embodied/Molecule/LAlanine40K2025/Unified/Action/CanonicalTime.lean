import H0mework.Versions.AB.Physics.MotherSource.CanonicalMatter.Time
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.GaussSource

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.CanonicalTime
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField
open DiracExteriorMatterAction Stage9C.Material.SpinPair LowEnergy.FullQuantum
open StageNineMatterPointwiseEquation StageNineGlobalIntegratedAction
open Stage10.CanonicalMatter Stage10.ChargedPreparation YangMills.FullPairing
open BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient MeasureTheory
open GaussSource
open scoped InnerProductSpace
noncomputable section
attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

private theorem normalized_replace (background : StageNineHolonomicConfiguration)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (point : BasePoint)
    (argument : DiracExteriorMatterCarrier) :
    normalizedMomentum (Stage10.ChargedGauss.replaceMatter background matter dual) point (dual point) argument =
      normalizedMomentum background point (dual point) argument := rfl

private theorem normalized_scaled (configuration : StageNineHolonomicConfiguration) (point : BasePoint)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) (matter : DiracExteriorMatterCarrier)
    (left right : ℂ) :
    normalizedMomentum configuration point (left • dual) (right • matter) =
      left*right*normalizedMomentum configuration point dual matter := by
  simp only [normalizedMomentum, LinearMap.smul_apply, LinearMap.comp_apply, map_smul, smul_eq_mul]
  ring

def configuration (first second : Basis) (scale : ℝ) : StageNineHolonomicConfiguration :=
  Stage10.ChargedGauss.replaceMatter Stage10.Runtime.configuration (preparedMatter second scale) (preparedDual first scale)

def timePair (first second : Basis) (scale : ℝ) (point : BasePoint) : ℂ :=
  normalizedMomentum (configuration first second scale) point
    (preparedDual first scale point) (preparedMatter second scale point)

theorem time_pair (first second : Basis) (scale : ℝ) (point : BasePoint) :
    timePair first second scale point =
      (4*(spinScale : ℂ))*(star (orbitalWeight first scale point)*orbitalWeight second scale point) := by
  unfold timePair configuration
  rw [normalized_replace]
  unfold preparedDual preparedMatter
  rw [Stage10.Runtime.configuration_eq, normalized_scaled, prepared_time_pair]
  ring

theorem time_pair_gram (first second : Basis) (scale : ℝ) (point : BasePoint) :
    timePair first second scale point =
      (4*(spinScale : ℂ))*inner ℂ (ChargedSource.chargedSection first scale point)
        (ChargedSource.chargedSection second scale point) := by
  rw [time_pair]
  simp only [ChargedSource.chargedSection, preparedSection, inner_smul_left, inner_smul_right,
    full_prepared_inner, mul_one]
  change (4*(spinScale : ℂ))*(star (orbitalWeight first scale point)*orbitalWeight second scale point) =
    (4*(spinScale : ℂ))*(orbitalWeight second scale point*star (orbitalWeight first scale point))
  ring

theorem original_action_time_pair (first second : Basis) (scale : ℝ) (point : BasePoint) :
    matterDifferentialMomentum Stage10.Runtime.source (configuration first second scale)
      (matterCoordinateEquiv ((-Complex.I) • (configuration first second scale).matter point)) 0 point =
      ((4*(spinScale : ℂ))*inner ℂ (ChargedSource.chargedSection first scale point)
        (ChargedSource.chargedSection second scale point)).re := by
  rw [Stage10.Runtime.source_eq, action_time_momentum]
  change (timePair first second scale point).re = _
  rw [time_pair_gram]

def timeDensity (scale : ℝ) (point : BasePoint) : ℂ :=
  ∑ first : Basis, ∑ second : Basis, (densityMatrix first second : ℂ)*timePair first second scale point

theorem original_D3_time (scale : ℝ) (point : BasePoint) :
    timeDensity scale point = 4*(spinScale : ℂ)*(sourceDensity (spatialPoint scale point) : ℂ) := by
  have same : timeDensity scale point = (4*(spinScale : ℂ))*sectionDensity scale point := by
    simp only [timeDensity, sectionDensity, scalarSection_pair, time_pair, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro second _
    ring
  rw [same, original_D3_section_density]

theorem time_charge_alignment (scale : ℝ) (point : BasePoint) :
    timeDensity scale point = -ChargedSource.classicalCurrentDensity scale point := by
  rw [original_D3_time, ChargedSource.classical_D3_current]
  ring

theorem time_pair_integrable (time : ℝ) (first second : Basis) :
    Integrable (fun point : Point => timePair first second 1 (spatialSlice time point)) := by
  simp_rw [time_pair_gram]
  exact (full_preparation_integrable time preparation preparation first second).const_mul _

theorem original_time_overlap (time : ℝ) (first second : Basis) :
    (∫ point : Point, timePair first second 1 (spatialSlice time point)) =
      (4*(spinScale : ℂ))*(UnifiedOrbitals.overlap first second : ℂ) := by
  simp_rw [time_pair]
  have pair (point : Point) : star (orbitalWeight first 1 (spatialSlice time point))*
      orbitalWeight second 1 (spatialSlice time point) =
      (UnifiedOrbitals.ao first point*UnifiedOrbitals.ao second point : ℝ) := by
    rw [← scalarSection_pair, slice_pair]
  simp_rw [pair]
  rw [integral_const_mul, integral_complex_ofReal]
  rfl

theorem time_density_integrable (time : ℝ) :
    Integrable (fun point : Point => timeDensity 1 (spatialSlice time point)) := by
  simp_rw [original_D3_time, slice_coordinates]
  exact (GlobalSource.source_bilinear_integrable zeroJet zeroJet).ofReal.const_mul _

theorem original_total_time (time : ℝ) :
    (∫ point : Point, timeDensity 1 (spatialSlice time point)) =
      (4*(spinScale : ℂ))*((∫ point : Point, sourceDensity point : ℝ) : ℂ) := by
  simp_rw [original_D3_time, slice_coordinates]
  rw [integral_const_mul, integral_complex_ofReal]

end
end LAlanine40K2025.UnifiedAction.CanonicalTime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
