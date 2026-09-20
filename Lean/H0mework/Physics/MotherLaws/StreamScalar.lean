import H0mework.Physics.MotherLaws.CompletionCompactDensity
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Topology.MetricSpace.PiNat

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherStreamLaws

open Set Filter
open scoped Topology

noncomputable section

abbrev Stream := ℕ → ℝ

example : CompactlyCoherentSpace Stream := inferInstance
example : CompleteSpace C(Stream, Stream) := inferInstance

def restrictedPolynomial (K : Set Stream) : MvPolynomial ℕ ℚ →ₐ[ℚ] C(K, ℝ) :=
  MvPolynomial.aeval fun i =>
    ⟨fun x => x.val i, (continuous_apply i).comp continuous_subtype_val⟩

@[simp] theorem restrictedPolynomial_apply (K : Set Stream) (p : MvPolynomial ℕ ℚ) (x : K) :
    restrictedPolynomial K p x = MotherLawCompletion.scalarPolynomial p x.val := by
  change (ContinuousMap.evalAlgHom ℚ ℝ x) (MvPolynomial.aeval _ p) = _
  rw [MvPolynomial.comp_aeval_apply]
  rfl

theorem restrictedPolynomial_separates (K : Set Stream) :
    (restrictedPolynomial K).range.SeparatesPoints := by
  intro x y different
  have coord : ∃ i, x.val i ≠ y.val i := by
    by_contra! same
    exact different (Subtype.ext (funext same))
  obtain ⟨i, hi⟩ := coord
  refine ⟨restrictedPolynomial K (MvPolynomial.X i),
    ⟨restrictedPolynomial K (MvPolynomial.X i), ⟨MvPolynomial.X i, rfl⟩, rfl⟩, ?_⟩
  simpa [restrictedPolynomial] using hi

theorem compact_scalar_dense (K : Set Stream) [CompactSpace K] :
    DenseRange (restrictedPolynomial K) := by
  have closed := MotherLawCompletion.rational_closure_eq_top (restrictedPolynomial K).range
    (restrictedPolynomial_separates K)
  rw [DenseRange, dense_iff_closure_eq]
  exact congrArg (fun A : Subalgebra ℚ C(K, ℝ) => (A : Set C(K, ℝ))) closed

theorem compact_scalar_approximation (K : Set Stream) [CompactSpace K]
    (f : C(K, ℝ)) (ε : ℝ) (positive : 0 < ε) :
    ∃ p : MvPolynomial ℕ ℚ, ∀ x : K,
      dist (MotherLawCompletion.scalarPolynomial p x.val) (f x) < ε := by
  obtain ⟨p, close⟩ := (compact_scalar_dense K).exists_dist_lt f positive
  have near : dist (restrictedPolynomial K p) f < ε := by simpa only [dist_comm] using close
  refine ⟨p, fun x => ?_⟩
  rw [← restrictedPolynomial_apply]
  exact lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist x) near

/-- A finite family uses one finite input prefix; no extra stream material is introduced. -/
theorem polynomial_prefix {m : ℕ} (family : Fin m → MvPolynomial ℕ ℚ) :
    ∃ n, ∃ finite : Fin m → MvPolynomial (Fin n) ℚ,
      ∀ output, MvPolynomial.rename Fin.val (finite output) = family output := by
  classical
  let allVars : Finset ℕ := Finset.univ.biUnion fun output => (family output).vars
  let count := allVars.sup id + 1
  have each (output : Fin m) : ∃ p : MvPolynomial (Fin count) ℚ,
      MvPolynomial.rename Fin.val p = family output := by
    apply MvPolynomial.exists_rename_eq_of_vars_subset_range _ Fin.val Fin.val_injective
    intro i hi
    have member : i ∈ allVars := Finset.mem_biUnion.mpr ⟨output, Finset.mem_univ _, hi⟩
    exact ⟨⟨i, Nat.lt_succ_of_le (Finset.le_sup (f := id) member)⟩, rfl⟩
  choose finite generated using each
  exact ⟨count, finite, generated⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherStreamLaws
