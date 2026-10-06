import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.NuclearGreen
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.GreenPotential

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.PreciseNuclear
open SaturationMonoid.PhysicsCore Stage10.StaticGreen Stage9C.Material.SpinPair
open MeasureTheory BasinRefinement SourceGaussianModel SourceCoulomb ContinuousGradient WholeBandBasin.Family.All.Nuclear
noncomputable section

def electronNuclearDensity (point : Point) : ℝ := -(GreenSource.sourceCurrent point*potential 1 point)
def electronNuclearEnergy : ℝ := ∫ point : Point, electronNuclearDensity point

theorem electron_nuclear_density (point : Point) :
    electronNuclearDensity point = (4*spinScale)^2/(8*Real.pi*lapse)*
      ∑ atom : Fin 13, -nuclearCharge atom*(sourceDensity point*kernel (point-PreciseTarget.centre atom)) := by
  simp only [electronNuclearDensity, GreenSource.sourceCurrent_value, potential, pointSourcePotential,
    sourcePosition, one_smul, green_kernel, Finset.mul_sum, mul_neg, neg_neg]
  apply Finset.sum_congr rfl
  intro atom _
  ring

theorem electron_nuclear_integrable : Integrable electronNuclearDensity := by
  have same : electronNuclearDensity = fun point => (4*spinScale)^2/(8*Real.pi*lapse)*
      ∑ atom : Fin 13, -nuclearCharge atom*(sourceDensity point*kernel (point-PreciseTarget.centre atom)) :=
    funext electron_nuclear_density
  rw [same]
  exact (integrable_finsetSum Finset.univ (fun atom _ => PreciseTarget.zone_attraction_integrable atom)).const_mul _

/-- The original D3 current and full target nuclear source feed the existing exact AO attraction consumer. -/
theorem original_electron_nuclear_energy :
    electronNuclearEnergy = (4*spinScale)^2/(8*Real.pi*lapse)*UnifiedOrbitals.Attraction.Precise.totalIntegral := by
  unfold electronNuclearEnergy
  simp_rw [electron_nuclear_density]
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun atom _ => PreciseTarget.zone_attraction_integrable atom)]
  rw [← PreciseTarget.nuclear_total_original_ao]
  rfl

end
end LAlanine40K2025.UnifiedAction.PreciseNuclear
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
