import H0mework.Physics.LowEnergyFermion.Consumer

/-! Focused Lean consumer for the selected source-color contact channel.
    The exact pole and no-open-channel statement is independently recomputed
    by the neighbouring Python receipt; this file keeps the selected operator
    on the original CAR/source occurrence and checks its source matrix element.
-/
set_option autoImplicit false
namespace ExternalCompositeDecayAudit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open QuantizationCheck.Fermion LowEnergy.Fermion
open DiracExteriorMatterAction Stage9C.Material.SpinPair
open scoped BigOperators Matrix
noncomputable section
attribute [local instance] fullIndexOrder

def selectedContactOperator : Module.End ℂ (Fock Quantum.Index) :=
  (-1 / 2 : ℂ) • ∑ axis : Fin 3,
    normalProduct
      (currentVertex (actual.coframe 0) spinScale axis.succ
        (sourceColorP286Generator axis))
      (currentVertex (actual.coframe 0) spinScale axis.succ
        (sourceColorP286Generator axis))

theorem selectedContact_matrixElement :
    pairing normalizedDoubleOccupation
      (selectedContactOperator normalizedDoubleOccupation) = -(81 / 125 : ℂ) := by
  unfold selectedContactOperator
  simp only [LinearMap.smul_apply]
  rw [pairing_smul_right]
  simp only [LinearMap.sum_apply]
  have pairing_sum : pairing normalizedDoubleOccupation
      (∑ axis : Fin 3,
        normalProduct
          (currentVertex (actual.coframe 0) spinScale axis.succ
            (sourceColorP286Generator axis))
          (currentVertex (actual.coframe 0) spinScale axis.succ
            (sourceColorP286Generator axis)) normalizedDoubleOccupation) =
      ∑ axis : Fin 3,
        pairing normalizedDoubleOccupation
          (normalProduct
            (currentVertex (actual.coframe 0) spinScale axis.succ
              (sourceColorP286Generator axis))
            (currentVertex (actual.coframe 0) spinScale axis.succ
              (sourceColorP286Generator axis)) normalizedDoubleOccupation) := by
      simp only [pairing, Finset.sum_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
  rw [pairing_sum]
  simp_rw [actual_color_fourFermion_normalized]
  norm_num

#print axioms selectedContact_matrixElement

end
end ExternalCompositeDecayAudit
