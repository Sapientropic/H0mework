import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.CanonicalParticle.Plane.Hamiltonian
import H0mework.Versions.R3bbcbd59.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.AtomicScales

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.AtomicScales
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField
open Stage9C.Material.SpinPair Stage10.ActionNormalization Stage10.StaticHamiltonian
open Stage10.ChargedPreparation Stage10.ChargedPreparation.CanonicalParticle
open Stage10.ChargedPreparation.SpatialSpectrum StageNineMatterPointwiseEquation
noncomputable section
attribute [local irreducible] Stage10.Runtime.source Stage10.Runtime.configuration

def canonicalMass : ℝ := phaseMomentum*mass
def canonicalCoulomb : ℝ := phaseMomentum*coulombCoefficient
def canonicalHartree : ℝ := phaseMomentum*sourceEnergy

theorem canonical_mass_positive : 0 < canonicalMass := mul_pos phaseMomentum_positive mass_positive
theorem canonical_hartree_positive : 0 < canonicalHartree := mul_pos phaseMomentum_positive energy_positive

def nativeMomentum (momentum : Fin 3 → ℝ) (point : BasePoint) (axis : Fin 3) : ℝ :=
  matterDifferentialMomentum Stage10.Runtime.source (Plane.fields momentum)
    (-fieldDirectionalDerivative (fun candidate => matterCoordinateEquiv ((Plane.fields momentum).matter candidate)) point axis.succ)
    0 point

theorem original_momentum (momentum : Fin 3 → ℝ) (point : BasePoint) (axis : Fin 3) :
    nativeMomentum momentum point axis = phaseMomentum*momentum axis := by
  rw [nativeMomentum, Plane.actual_translation_momentum, phaseMomentum_source]

theorem original_momentum_square (momentum : Fin 3 → ℝ) (point : BasePoint) :
    spatialSquare (nativeMomentum momentum point) = phaseMomentum^2*spatialSquare momentum := by
  simp only [spatialSquare, original_momentum, mul_pow, ← Finset.mul_sum]

theorem original_energy_excitation (momentum : Fin 3 → ℝ) (point : BasePoint) :
    hamiltonianDensity Stage10.Runtime.source (Plane.fields momentum) point -
      hamiltonianDensity Stage10.Runtime.source (Plane.fields 0) point =
        phaseMomentum*(CanonicalParticle.energy momentum-CanonicalParticle.energy 0) := by
  have moving := Plane.complete_hamiltonian_difference momentum point
  have resting := Plane.complete_hamiltonian_difference 0 point
  nlinarith

theorem original_mass_shell (momentum : Fin 3 → ℝ) (point : BasePoint) :
    hamiltonianDensity Stage10.Runtime.source (Plane.fields momentum) point -
      hamiltonianDensity Stage10.Runtime.source (Plane.fields 0) point =
        spatialSquare (nativeMomentum momentum point)/(2*canonicalMass) -
          phaseMomentum*(lapse^4*(spatialSquare momentum)^2/(2*frequency*(rate momentum+frequency)^2)) := by
  rw [original_energy_excitation, CanonicalParticle.source_excitation,
    excitation_quadratic_remainder, original_momentum_square]
  change phaseMomentum*(spatialSquare momentum/(2*mass)-_) = _
  unfold canonicalMass
  field_simp [phaseMomentum_positive.ne', mass_positive.ne']

theorem original_coulomb_coefficient : canonicalCoulomb = (4*spinScale)^2/(8*Real.pi*lapse) := by
  unfold canonicalCoulomb coulombCoefficient
  rw [phaseMomentum_source]
  ring

theorem source_bohr_from_action : phaseMomentum^2/(canonicalMass*canonicalCoulomb) = sourceLength := by
  unfold canonicalMass canonicalCoulomb sourceLength
  field_simp [phaseMomentum_positive.ne', mass_positive.ne', coulombCoefficient_positive.ne']

theorem source_hartree_from_action :
    canonicalMass*canonicalCoulomb^2/phaseMomentum^2 = canonicalHartree := by
  unfold canonicalMass canonicalCoulomb canonicalHartree sourceEnergy
  field_simp [phaseMomentum_positive.ne']

theorem source_time_from_action : phaseMomentum/canonicalHartree = sourceTime := by
  unfold canonicalHartree sourceTime
  field_simp [phaseMomentum_positive.ne', energy_positive.ne']

theorem original_hamiltonian_atomic (momentum : Fin 3 → ℝ) (point : BasePoint) :
    (hamiltonianDensity Stage10.Runtime.source (Plane.fields (momentumInSource momentum)) point -
      hamiltonianDensity Stage10.Runtime.source (Plane.fields 0) point)/canonicalHartree =
        spatialSquare momentum/2-correction momentum := by
  rw [original_energy_excitation, canonicalHartree, mul_div_mul_left _ _ phaseMomentum_positive.ne']
  exact original_spectrum_atomic momentum

theorem original_ERI_canonical (i j k l : BasinRefinement.SourceFiniteData.Basis) :
    (4*spinScale)^2*GreenSource.greenMatrixEntry sourceLength i j k l/canonicalHartree =
      UnifiedOrbitals.electronRepulsion i j k l := by
  have normalized := original_ERI i j k l
  rw [greenERI, actionScale] at normalized
  convert normalized using 1
  unfold canonicalHartree
  field_simp [phaseMomentum_positive.ne', energy_positive.ne']

theorem rejects_frequency_mass_as_classical : canonicalMass ≠ mass := by
  intro same
  have factor : phaseMomentum = 1 := by
    apply mul_right_cancel₀ mass_positive.ne'
    simpa only [canonicalMass, one_mul] using same
  rw [phaseMomentum_source] at factor
  nlinarith [spinScale_sq]

end
end LAlanine40K2025.UnifiedAction.AtomicScales
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
