import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Abel

/-! Finite source words generate their successor boundary certificate and complete mass residual. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceSuccessorBoundary

noncomputable section

universe u

variable (R : Type u) [CommRing R]

def push : (Nat →₀ R) →ₗ[R] (Nat →₀ R) :=
  Finsupp.lmapDomain R R Nat.succ

def boundary : (Nat →₀ R) →ₗ[R] (Nat →₀ R) :=
  push R - LinearMap.id

def mass : (Nat →₀ R) →ₗ[R] R :=
  Finsupp.linearCombination R fun _ : Nat => (1 : R)

def certificate : (Nat →₀ R) →ₗ[R] (Nat →₀ R) :=
  Finsupp.linearCombination R fun index =>
    ∑ source ∈ Finset.range index, Finsupp.single source (1 : R)

theorem boundary_single (index : Nat) (scalar : R) :
    boundary R (Finsupp.single index scalar) =
      Finsupp.single (index + 1) scalar - Finsupp.single index scalar := by
  simp [boundary, push]

theorem certificate_single (index : Nat) (scalar : R) :
    certificate R (Finsupp.single index scalar) =
      scalar • ∑ source ∈ Finset.range index, Finsupp.single source (1 : R) :=
  Finsupp.linearCombination_single _ _ _

theorem boundary_prefix (index : Nat) :
    boundary R (∑ source ∈ Finset.range index, Finsupp.single source (1 : R)) =
      Finsupp.single index (1 : R) - Finsupp.single 0 (1 : R) := by
  induction index with
  | zero => simp
  | succ index inductionHypothesis =>
      rw [Finset.sum_range_succ, map_add, inductionHypothesis, boundary_single]
      abel

theorem mass_single (index : Nat) (scalar : R) :
    mass R (Finsupp.single index scalar) = scalar := by
  simp [mass]

theorem mass_unit : mass R (Finsupp.single 0 (1 : R)) = 1 :=
  mass_single R 0 1

theorem mass_push (word : Nat →₀ R) : mass R (push R word) = mass R word := by
  change Finsupp.linearCombination R (fun _ : Nat => (1 : R))
    (Finsupp.mapDomain Nat.succ word) = _
  rw [Finsupp.linearCombination_mapDomain]
  rfl

theorem mass_boundary (word : Nat →₀ R) : mass R (boundary R word) = 0 := by
  change mass R (push R word - word) = 0
  rw [map_sub, mass_push, sub_self]

theorem boundary_certificate (word : Nat →₀ R) :
    boundary R (certificate R word) = word - mass R word • Finsupp.single 0 (1 : R) := by
  induction word using Finsupp.induction with
  | zero => simp
  | @single_add index scalar word notMem nonzero inductionHypothesis =>
      simp only [map_add, certificate_single, map_smul, boundary_prefix, mass_single,
        smul_sub, Finsupp.smul_single, smul_eq_mul, mul_one, add_smul, inductionHypothesis]
      abel

theorem range_boundary_eq_ker_mass : (boundary R).range = (mass R).ker := by
  ext word
  constructor
  · rintro ⟨preimage, rfl⟩
    exact mass_boundary R preimage
  · intro zeroMass
    change mass R word = 0 at zeroMass
    refine ⟨certificate R word, ?_⟩
    simpa only [zeroMass, zero_smul, sub_zero] using boundary_certificate R word

end
end SourceSuccessorBoundary
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
