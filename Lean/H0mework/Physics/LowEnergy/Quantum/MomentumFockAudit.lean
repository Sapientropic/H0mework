import H0mework.Physics.LowEnergy.Quantum.MomentumFock

/-! Independent occupied-state consumers of arbitrary ordered source coefficients.
The two coefficients may be filled by the ordinary or contact readouts of the
source kernel; this finite algebraic audit does not replace their producer. -/
set_option autoImplicit false
namespace SourceMomentumFockAudit
open SaturationMonoid.PhysicsCore
open SaturationMonoid.PhysicsCore.LowEnergy.Fermion
open QuantizationCheck.Fermion SourceMomentumFock
open scoped BigOperators
noncomputable section

def orderedKernel (first second : ℂ) (i j k l : Fin 4) : ℂ :=
  if i = 2 ∧ j = 0 ∧ k = 3 ∧ l = 1 then first
  else if i = 3 ∧ j = 1 ∧ k = 2 ∧ l = 0 then second
  else 0

def pairCharge (first second : ℂ) : Fin 4 → ℂ := ![first, second, first + second, 0]

theorem occupied_incoming_unit :
    pairing (twoParticle (Pi.single (0 : Fin 4) 1) (Pi.single 1 1))
      (twoParticle (Pi.single (0 : Fin 4) 1) (Pi.single 1 1)) = 1 := by
  simp [pairing_twoParticle, modePair, Pi.single_apply]

theorem occupied_outgoing_unit :
    pairing (twoParticle (Pi.single (2 : Fin 4) 1) (Pi.single 3 1))
      (twoParticle (Pi.single (2 : Fin 4) 1) (Pi.single 3 1)) = 1 := by
  simp [pairing_twoParticle, modePair, Pi.single_apply]

theorem actual_two_ordered_matrixElement (first second : ℂ) :
    pairing (twoParticle (Pi.single (2 : Fin 4) 1) (Pi.single 3 1))
      (quartic (orderedKernel first second)
        (twoParticle (Pi.single (0 : Fin 4) 1) (Pi.single 1 1))) = first + second := by
  rw [quartic_matrixElement]
  simp [orderedKernel, Pi.single_apply, Fin.sum_univ_four]

theorem reversed_incoming_sign (first second : ℂ) :
    pairing (twoParticle (Pi.single (2 : Fin 4) 1) (Pi.single 3 1))
      (quartic (orderedKernel first second)
        (twoParticle (Pi.single (1 : Fin 4) 1) (Pi.single 0 1))) = -(first + second) := by
  rw [quartic_matrixElement]
  simp [orderedKernel, Pi.single_apply, Fin.sum_univ_four]
  ring

theorem actual_two_ordered_charge (first second chargeFirst chargeSecond : ℂ) :
    occupationCharge (pairCharge chargeFirst chargeSecond) * quartic (orderedKernel first second) =
      quartic (orderedKernel first second) * occupationCharge (pairCharge chargeFirst chargeSecond) := by
  apply quartic_charge
  intro i j k l
  simp only [orderedKernel]
  split_ifs with direct exchanged
  · rcases direct with ⟨rfl, rfl, rfl, rfl⟩
    simp [pairCharge]
  · rcases exchanged with ⟨rfl, rfl, rfl, rfl⟩
    simp [pairCharge]
  · simp

theorem actual_two_ordered_number (first second : ℂ) :
    occupationCharge (fun _ : Fin 4 => 1) * quartic (orderedKernel first second) =
      quartic (orderedKernel first second) * occupationCharge (fun _ : Fin 4 => 1) :=
  quartic_number _

#print axioms SourceMomentumFock.quartic
#print axioms SourceMomentumFock.quartic_factorized
#print axioms SourceMomentumFock.quartic_add
#print axioms SourceMomentumFock.quartic_smul
#print axioms SourceMomentumFock.quartic_twoParticle
#print axioms SourceMomentumFock.quartic_charge
#print axioms SourceMomentumFock.quartic_number
#print axioms SourceMomentumFock.quartic_matrixElement
#print axioms occupied_incoming_unit
#print axioms occupied_outgoing_unit
#print axioms actual_two_ordered_matrixElement
#print axioms reversed_incoming_sign
#print axioms actual_two_ordered_charge
#print axioms actual_two_ordered_number

end
end SourceMomentumFockAudit
