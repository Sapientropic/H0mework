import H0mework.Versions.AB.Physics.LowEnergy.Electromagnetic.Canonical

/-! The complete normalized action, rather than a newly named quantum energy,
returns through the existing canonical external state's original phase. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic.ActionUnits
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage10.ChargedPreparation
open Stage10.ActionNormalization
open NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open UnifiedAction.AtomicScales
noncomputable section

theorem normalized_action_phase (point : BasePoint) (momentum : Fin 3 → ℝ) (time : ℝ) :
    FullQuantum.evolution Stage10.Runtime.configuration point momentum time
        (CanonicalParticle.state point momentum) =
      Complex.exp (-Complex.I * (time : ℂ) *
        ((hamiltonian (CanonicalParticle.Plane.fields momentum) point -
          hamiltonian CanonicalParticle.Plane.reference point : ℝ) : ℂ)) •
            CanonicalParticle.state point momentum := by
  rw [CanonicalParticle.Plane.normalized_hamiltonian_difference]
  exact CanonicalParticle.original_evolution point momentum time

theorem normalized_translation_momentum (point : BasePoint)
    (momentum : Fin 3 → ℝ) (axis : Fin 3) :
    actionScale * nativeMomentum momentum point axis = momentum axis := by
  rw [original_momentum, actionScale, ← mul_assoc,
    inv_mul_cancel₀ phaseMomentum_positive.ne', one_mul]

end
end SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic.ActionUnits
