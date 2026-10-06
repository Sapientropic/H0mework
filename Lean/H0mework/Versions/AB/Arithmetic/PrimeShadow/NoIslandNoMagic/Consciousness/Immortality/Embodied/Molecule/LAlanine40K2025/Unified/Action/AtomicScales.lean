import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.CanonicalParticle.Evolution
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.NormalizedCoulomb

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.AtomicScales
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair Stage10.ActionNormalization
open Stage10.ChargedPreparation Stage10.ChargedPreparation.SpatialSpectrum
open BasinRefinement SourceFiniteData SourceGaussianModel
noncomputable section

def mass : ℝ := Dispersion.inertia
def sourceLength : ℝ := (mass*coulombCoefficient)⁻¹
def sourceEnergy : ℝ := mass*coulombCoefficient^2
def sourceTime : ℝ := sourceEnergy⁻¹

theorem mass_positive : 0 < mass := Dispersion.inertia_pos
theorem length_positive : 0 < sourceLength := inv_pos.mpr (mul_pos mass_positive coulombCoefficient_positive)
theorem energy_positive : 0 < sourceEnergy := mul_pos mass_positive (sq_pos_of_pos coulombCoefficient_positive)
theorem time_positive : 0 < sourceTime := inv_pos.mpr energy_positive

theorem source_coulomb_unit : coulombCoefficient/sourceLength = sourceEnergy := by
  unfold sourceLength sourceEnergy
  field_simp

theorem source_kinetic_unit : 1/(2*mass*sourceLength^2) = sourceEnergy/2 := by
  unfold sourceLength sourceEnergy
  field_simp [mass_positive.ne', coulombCoefficient_positive.ne']

theorem source_phase_unit : sourceTime*sourceEnergy = 1 := inv_mul_cancel₀ energy_positive.ne'

def momentumInSource (momentum : Fin 3 → ℝ) : Fin 3 → ℝ := sourceLength⁻¹ • momentum

theorem momentum_square (momentum : Fin 3 → ℝ) :
    spatialSquare (momentumInSource momentum) = (sourceLength⁻¹)^2*spatialSquare momentum := by
  simp only [momentumInSource, spatialSquare, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]

def correction (momentum : Fin 3 → ℝ) : ℝ :=
  (lapse^4*(spatialSquare (momentumInSource momentum))^2 /
    (2*frequency*(rate (momentumInSource momentum)+frequency)^2))/sourceEnergy

theorem original_spectrum_atomic (momentum : Fin 3 → ℝ) :
    (CanonicalParticle.energy (momentumInSource momentum)-CanonicalParticle.energy 0)/sourceEnergy =
      spatialSquare momentum/2-correction momentum := by
  rw [CanonicalParticle.source_excitation, excitation_quadratic_remainder, sub_div]
  change spatialSquare (momentumInSource momentum)/(2*mass)/sourceEnergy-correction momentum = _
  rw [momentum_square]
  unfold sourceLength sourceEnergy
  field_simp [mass_positive.ne', coulombCoefficient_positive.ne']

/-- Native source current coupling, whole-action phase normalization, and source energy units act on the original Green ERI. -/
def greenERI (i j k l : Basis) : ℝ :=
  actionScale*(4*spinScale)^2*GreenSource.greenMatrixEntry sourceLength i j k l/sourceEnergy

theorem original_ERI (i j k l : Basis) : greenERI i j k l = UnifiedOrbitals.electronRepulsion i j k l := by
  rw [greenERI, GreenSource.original_ERI_green sourceLength length_positive, actionScale_source]
  unfold GreenSource.greenCoefficient sourceLength sourceEnergy coulombCoefficient
  field_simp [mass_positive.ne', spinScale_pos.ne', Real.pi_pos.ne', lapse_pos.ne']

theorem original_nuclear_repulsion : actionScale*PreciseNuclear.repulsion sourceLength/sourceEnergy =
    WholeBandBasin.Family.All.Nuclear.PreciseTarget.totalRepulsion := by
  rw [PreciseNuclear.original_repulsion_green sourceLength length_positive, actionScale_source]
  unfold GreenSource.greenCoefficient sourceLength sourceEnergy coulombCoefficient
  field_simp [mass_positive.ne', spinScale_pos.ne', Real.pi_pos.ne', lapse_pos.ne']

theorem original_atomic_phase (point : BasePoint) (momentum : Fin 3 → ℝ) (time : ℝ) :
    CanonicalParticle.relativeEvolution point (momentumInSource momentum) (time/sourceEnergy) =
      Complex.exp (-Complex.I*(time : ℂ)*((spatialSquare momentum/2-correction momentum : ℝ) : ℂ)) •
        CanonicalParticle.state point (momentumInSource momentum) := by
  have spectrum : excitation (momentumInSource momentum)/sourceEnergy =
      spatialSquare momentum/2-correction momentum := by
    rw [← CanonicalParticle.source_excitation]
    exact original_spectrum_atomic momentum
  rw [CanonicalParticle.original_relative_evolution, ← spectrum]
  congr 2
  push_cast
  ring


end
end LAlanine40K2025.UnifiedAction.AtomicScales
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
