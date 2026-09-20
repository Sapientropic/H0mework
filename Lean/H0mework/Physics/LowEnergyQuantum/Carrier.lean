import H0mework.Physics.LowEnergyContact.ReturnChannel
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.StdBasis

/-! The whole native exterior-matter basis retains intermediate Yukawa
outputs. Operator composition is represented before endpoint compression. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Quantum
open DiracCliffordRepresentation DiracExteriorMatterAction SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction SU7ExteriorBreakingYukawa
open StageNineHolonomicField StageNineDiracDualYukawaSpinJurisdiction
open scoped Matrix
noncomputable section

abbrev InternalIndex := ExteriorBasisIndex 6 ⊕ (ExteriorBasisIndex 2 ⊕ ExteriorBasisIndex 4)
abbrev Index := (_ : DiracSpinorIndex) × InternalIndex

local instance : DecidableEq Index := Classical.decEq _

def internalBasis : Module.Basis InternalIndex ℂ SU7ExteriorSpinorMatterCarrier :=
  (su7ExteriorBasis 6).prod ((su7ExteriorBasis 2).prod (su7ExteriorBasis 4))

def wholeBasis : Module.Basis Index ℂ DiracExteriorMatterCarrier := Pi.basis (fun _ => internalBasis)

theorem index_card : Fintype.card Index = 252 := by
  rw [← Module.finrank_eq_card_basis wholeBasis]
  change Module.finrank ℂ (DiracSpinorIndex → SU7ExteriorSpinorMatterCarrier) = 252
  rw [Module.finrank_pi_fintype]
  norm_num [su7ExteriorPower_finrank, Nat.choose, DiracSpinorIndex]

def coordinates : DiracExteriorMatterCarrier ≃ₗ[ℂ] (Index → ℂ) := wholeBasis.equivFun

def operatorMatrix : Module.End ℂ DiracExteriorMatterCarrier ≃ₐ[ℂ] Matrix Index Index ℂ :=
  LinearMap.toMatrixAlgEquiv wholeBasis

theorem matrix_action (action : Module.End ℂ DiracExteriorMatterCarrier) (matter : DiracExteriorMatterCarrier) :
    operatorMatrix action *ᵥ coordinates matter = coordinates (action matter) :=
  LinearMap.toMatrix_mulVec_repr wholeBasis wholeBasis action matter

theorem matrix_composition (first second : Module.End ℂ DiracExteriorMatterCarrier) :
    operatorMatrix (first.comp second) = operatorMatrix first * operatorMatrix second :=
  operatorMatrix.map_mul first second

theorem matrix_faithful {first second : Module.End ℂ DiracExteriorMatterCarrier} :
    operatorMatrix first = operatorMatrix second ↔ first = second := operatorMatrix.injective.eq_iff

def dualCoordinates (dual : Module.Dual ℂ DiracExteriorMatterCarrier) (index : Index) : ℂ :=
  dual (wholeBasis index)

theorem full_response (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (action : Module.End ℂ DiracExteriorMatterCarrier) (matter : DiracExteriorMatterCarrier) :
    dual (action matter) = ∑ index, dualCoordinates dual index *
      (operatorMatrix action *ᵥ coordinates matter) index := by
  rw [matrix_action]
  conv_lhs => rw [← wholeBasis.sum_repr (action matter)]
  simp only [map_sum, map_smul, smul_eq_mul, dualCoordinates]
  apply Finset.sum_congr rfl
  intro index _
  exact mul_comm _ _

theorem matrix_yukawa_products (first second : ExteriorBreakingScalarCarrier) :
    operatorMatrix (diracDualRightChiralYukawaAction first) *
      operatorMatrix (diracDualRightChiralYukawaAction second) = 0 := by
  rw [← matrix_composition, Response.Yukawa.ordered_product_zero, map_zero]

theorem matrix_yukawa_nonzero : operatorMatrix (diracDualRightChiralYukawaAction exteriorBreakingScalar) ≠ 0 := by
  intro zero
  apply diracDualRightChiralYukawaAction_nonzero
  exact operatorMatrix.injective (zero.trans (operatorMatrix.map_zero).symm)

theorem full_return_detected :
    operatorMatrix Contact.ReturnChannel.returnMap *
      operatorMatrix (diracDualRightChiralYukawaAction Response.MixedWitness.scalarDirection) ≠ 0 := by
  rw [← matrix_composition]
  intro zero
  have actionZero : Contact.ReturnChannel.detectedAction = 0 :=
    operatorMatrix.injective (zero.trans (operatorMatrix.map_zero).symm)
  have paired : Stage9C.Material.SpinPair.actual.conjugateMatter 0
      (Contact.ReturnChannel.detectedAction Contact.ReturnChannel.prepared) = 0 := by
    rw [actionZero]
    simp
  rw [Contact.ReturnChannel.detected_pairing] at paired
  exact mul_ne_zero Contact.ReturnChannel.amplitude_nonzero
    (mul_ne_zero (by norm_num) (by exact_mod_cast ne_of_gt Stage9C.Material.SpinPair.spinScale_pos)) paired

end
end SaturationMonoid.PhysicsCore.LowEnergy.Quantum
