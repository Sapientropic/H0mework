import H0mework.Physics.LowEnergy.FullQuantum.TriangularSource
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-! The actual full resolvent is generated with exactly one Yukawa insertion. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.Triangular
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
noncomputable section

def freeKernel (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (z : ℂ) : Mother := z • 1 - freeHamiltonian C p k

def fullKernel (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (z : ℂ) : Mother := z • 1 - hamiltonian C p k

def freeResolvent (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (z : ℂ) : Mother := Ring.inverse (freeKernel C p k z)

def fullResolvent (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (z : ℂ) : Mother :=
  freeResolvent C p k z +
    freeResolvent C p k z * interactionHamiltonian C p * freeResolvent C p k z

theorem kernel_split (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (z : ℂ) :
    fullKernel C p k z = freeKernel C p k z - interactionHamiltonian C p := by
  rw [fullKernel, hamiltonian_split]
  unfold freeKernel
  abel

theorem grade_freeKernel (d : Fin 3) (C : StageNineHolonomicConfiguration)
    (p : BasePoint) (k : Fin 3 → ℝ) (z : ℂ) : Commute (grade d) (freeKernel C p k z) := by
  apply LinearMap.ext
  intro v
  have commute := LinearMap.congr_fun (grade_freeHamiltonian d C p k).eq v
  simp only [Module.End.mul_apply] at commute
  change grade d (z • v - freeHamiltonian C p k v) =
    z • grade d v - freeHamiltonian C p k (grade d v)
  rw [map_sub, map_smul, commute]

theorem grade_freeResolvent (d : Fin 3) (C : StageNineHolonomicConfiguration)
    (p : BasePoint) (k : Fin 3 → ℝ) (z : ℂ)
    (regular : IsUnit (freeKernel C p k z)) : Commute (grade d) (freeResolvent C p k z) := by
  apply LinearMap.ext
  intro v
  have left (w : DiracExteriorMatterAction.DiracExteriorMatterCarrier) :
      freeResolvent C p k z (freeKernel C p k z w) = w :=
    LinearMap.congr_fun (Ring.inverse_mul_cancel _ regular) w
  have right (w : DiracExteriorMatterAction.DiracExteriorMatterCarrier) :
      freeKernel C p k z (freeResolvent C p k z w) = w :=
    LinearMap.congr_fun (Ring.mul_inverse_cancel _ regular) w
  have commute (w : DiracExteriorMatterAction.DiracExteriorMatterCarrier) :
      grade d (freeKernel C p k z w) = freeKernel C p k z (grade d w) :=
    LinearMap.congr_fun (grade_freeKernel d C p k z).eq w
  change grade d (freeResolvent C p k z v) = freeResolvent C p k z (grade d v)
  calc
    _ = freeResolvent C p k z (freeKernel C p k z (grade d (freeResolvent C p k z v))) := (left _).symm
    _ = freeResolvent C p k z (grade d (freeKernel C p k z (freeResolvent C p k z v))) := by rw [commute]
    _ = _ := by rw [right]

theorem resolvent_insertions_zero (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (z : ℂ) (regular : IsUnit (freeKernel C p k z)) :
    interactionHamiltonian C p * freeResolvent C p k z * interactionHamiltonian C p = 0 :=
  source_insertions C p _ (grade_freeResolvent 0 C p k z regular)

theorem fullResolvent_two_sided (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (z : ℂ) (regular : IsUnit (freeKernel C p k z)) :
    fullKernel C p k z * fullResolvent C p k z = 1 ∧
      fullResolvent C p k z * fullKernel C p k z = 1 := by
  have negative : (-interactionHamiltonian C p) * freeResolvent C p k z *
      (-interactionHamiltonian C p) = 0 := by
    apply LinearMap.ext
    intro v
    change -interactionHamiltonian C p (freeResolvent C p k z (-interactionHamiltonian C p v)) = 0
    rw [map_neg, map_neg, neg_neg]
    exact LinearMap.congr_fun (resolvent_insertions_zero C p k z regular) v
  have generated := MixedSymbol.inverse_of_inserted_square_zero (freeKernel C p k z)
    (freeResolvent C p k z) (-interactionHamiltonian C p)
    (Ring.inverse_mul_cancel _ regular) (Ring.mul_inverse_cancel _ regular) negative
  have diagonal : freeKernel C p k z + (-interactionHamiltonian C p) = fullKernel C p k z := by
    rw [kernel_split]
    exact (sub_eq_add_neg (freeKernel C p k z) (interactionHamiltonian C p)).symm
  have inverse : freeResolvent C p k z - freeResolvent C p k z *
      (-interactionHamiltonian C p) * freeResolvent C p k z = fullResolvent C p k z := by
    apply LinearMap.ext
    intro v
    change freeResolvent C p k z v - freeResolvent C p k z
      (-interactionHamiltonian C p (freeResolvent C p k z v)) =
        freeResolvent C p k z v + freeResolvent C p k z
          (interactionHamiltonian C p (freeResolvent C p k z v))
    rw [map_neg, sub_neg_eq_add]
  rwa [diagonal, inverse] at generated

theorem fullKernel_isUnit (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (z : ℂ) (regular : IsUnit (freeKernel C p k z)) :
    IsUnit (fullKernel C p k z) := by
  have inverse := fullResolvent_two_sided C p k z regular
  exact ⟨⟨fullKernel C p k z, fullResolvent C p k z, inverse.1, inverse.2⟩, rfl⟩

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.Triangular
