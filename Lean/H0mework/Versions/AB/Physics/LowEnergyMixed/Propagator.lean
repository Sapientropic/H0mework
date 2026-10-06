import H0mework.Versions.AB.Physics.LowEnergyMixed.Degree
import Mathlib.Tactic.NoncommRing

/-! Finite propagation expansions for the actual triangular Yukawa placement.
These algebraic consumers require inverses only of the diagonal kinetic blocks. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.MixedSymbol
open DiracExteriorMatterAction SU7ExteriorBreakingYukawa
open StageNineDiracDualYukawaSpinJurisdiction
noncomputable section

theorem inverse_of_inserted_square_zero {R : Type*} [Ring R]
    (diagonal inverse coupling : R)
    (left : inverse * diagonal = 1) (right : diagonal * inverse = 1)
    (acyclic : coupling * inverse * coupling = 0) :
    (diagonal + coupling) * (inverse - inverse * coupling * inverse) = 1 ∧
    (inverse - inverse * coupling * inverse) * (diagonal + coupling) = 1 := by
  constructor
  · calc
      _ = diagonal * inverse - (diagonal * inverse) * coupling * inverse +
          coupling * inverse - (coupling * inverse * coupling) * inverse := by noncomm_ring
      _ = 1 := by rw [right, acyclic]; noncomm_ring
  · calc
      _ = inverse * diagonal - inverse * coupling * (inverse * diagonal) +
          inverse * coupling - inverse * (coupling * inverse * coupling) := by noncomm_ring
      _ = 1 := by rw [left, acyclic]; noncomm_ring

/-- No Yukawa Gram is introduced: only one original Y insertion survives. -/
theorem actual_yukawa_propagator
    (scalar : ExteriorBreakingScalarCarrier)
    (diagonal inverse : Module.End ℂ DiracExteriorMatterCarrier)
    (left : ∀ field, inverse (diagonal field) = field)
    (right : ∀ field, diagonal (inverse field) = field)
    (preserves : degreeSix.comp inverse = inverse.comp degreeSix) :
    let yukawa := diracDualRightChiralYukawaAction scalar
    (∀ field, (diagonal + yukawa)
        (inverse field - inverse (yukawa (inverse field))) = field) ∧
    (∀ field, inverse ((diagonal + yukawa) field) -
        inverse (yukawa (inverse ((diagonal + yukawa) field))) = field) := by
  dsimp only
  have acyclic (field : DiracExteriorMatterCarrier) :
      diracDualRightChiralYukawaAction scalar
        (inverse (diracDualRightChiralYukawaAction scalar field)) = 0 :=
    LinearMap.congr_fun (yukawa_propagator_yukawa scalar scalar inverse preserves) field
  constructor
  · intro field
    simp only [LinearMap.add_apply, map_sub, right, acyclic]
    module
  · intro field
    simp only [LinearMap.add_apply, map_add, left, acyclic, map_zero]
    module

/-- Three grades with arrows 0→1, 0→2, 1→2 admit exactly two insertions. -/
theorem inverse_of_inserted_cube_zero {R : Type*} [Ring R]
    (diagonal inverse coupling : R)
    (left : inverse * diagonal = 1) (right : diagonal * inverse = 1)
    (acyclic : coupling * inverse * coupling * inverse * coupling = 0) :
    let propagator := inverse - inverse * coupling * inverse +
      inverse * coupling * inverse * coupling * inverse
    (diagonal + coupling) * propagator = 1 ∧
      propagator * (diagonal + coupling) = 1 := by
  dsimp
  constructor
  · calc
      _ = diagonal * inverse - (diagonal * inverse) * coupling * inverse +
          (diagonal * inverse) * coupling * inverse * coupling * inverse +
          coupling * inverse - coupling * inverse * coupling * inverse +
          (coupling * inverse * coupling * inverse * coupling) * inverse := by noncomm_ring
      _ = 1 := by rw [right, acyclic]; noncomm_ring
  · calc
      _ = inverse * diagonal - inverse * coupling * (inverse * diagonal) +
          inverse * coupling * inverse * coupling * (inverse * diagonal) +
          inverse * coupling - inverse * coupling * inverse * coupling +
          inverse * (coupling * inverse * coupling * inverse * coupling) := by noncomm_ring
      _ = 1 := by rw [left, acyclic]; noncomm_ring

section Cascade
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [Module ℝ A] [Module ℝ B] [Module ℝ C]

/-- The native order is (dual6+matter2+matter4+dual4, dual2+scalar, matter6). -/
def cascade (first : A →ₗ[ℝ] B) (direct : A →ₗ[ℝ] C) (second : B →ₗ[ℝ] C) :
    Module.End ℝ (A × B × C) where
  toFun state := (0, first state.1, direct state.1 + second state.2.1)
  map_add' := by intros; ext <;> simp [add_add_add_comm]
  map_smul' := by intros; ext <;> simp [smul_add]

def diagonalBlocks (first : Module.End ℝ A) (second : Module.End ℝ B)
    (third : Module.End ℝ C) : Module.End ℝ (A × B × C) :=
  first.prodMap (second.prodMap third)

/-- Block-preserving Green operators cannot turn the two-step source chain into a loop. -/
theorem cascade_inserted_cube_zero
    (first : A →ₗ[ℝ] B) (direct : A →ₗ[ℝ] C) (second : B →ₗ[ℝ] C)
    (a : Module.End ℝ A) (b : Module.End ℝ B) (c : Module.End ℝ C) :
    let coupling := cascade first direct second
    let inverse := diagonalBlocks a b c
    coupling * inverse * coupling * inverse * coupling = 0 := by
  apply LinearMap.ext
  intro state
  simp [cascade, diagonalBlocks, Module.End.mul_apply]

theorem cascade_propagator
    (first : A →ₗ[ℝ] B) (direct : A →ₗ[ℝ] C) (second : B →ₗ[ℝ] C)
    (a : Module.End ℝ A) (b : Module.End ℝ B) (c : Module.End ℝ C)
    (diagonal : Module.End ℝ (A × B × C))
    (left : diagonalBlocks a b c * diagonal = 1)
    (right : diagonal * diagonalBlocks a b c = 1) :
    let inverse := diagonalBlocks a b c
    let coupling := cascade first direct second
    let propagator := inverse - inverse * coupling * inverse +
      inverse * coupling * inverse * coupling * inverse
    (diagonal + coupling) * propagator = 1 ∧
      propagator * (diagonal + coupling) = 1 := by
  exact inverse_of_inserted_cube_zero _ _ _ left right
    (cascade_inserted_cube_zero first direct second a b c)

end Cascade

end
end SaturationMonoid.PhysicsCore.LowEnergy.MixedSymbol
