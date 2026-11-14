import H0mework.Foundation.Relations.ScalarDifferentialResidual
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Isomorphisms

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.OrthogonalSourceObservation

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedScalarDifferentialResidual
open scoped InnerProductSpace BigOperators

variable {I E : Type*} [Fintype I] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (column : I → E)

/-- Each coordinate reads its own source covector. -/
def observe : E →L[ℂ] (I → ℂ) :=
  ContinuousLinearMap.pi (fun i => innerSL ℂ (column i))

/-- The diagonal Gram solve uses only the actual source columns. -/
def representative (value : I → ℂ) : E :=
  ∑ i, (value i / inner ℂ (column i) (column i)) • column i

theorem read_representative
    (orthogonal : Pairwise (fun i j => inner ℂ (column i) (column j) = 0))
    (live : ∀ i, column i ≠ 0) (value : I → ℂ) :
    observe column (representative column value) = value := by
  classical
  funext i
  change inner ℂ (column i) (∑ j, (value j / inner ℂ (column j) (column j)) • column j) = value i
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [inner_smul_right, div_mul_cancel₀ _ (fun zero => live i (inner_self_eq_zero.mp zero))]
  · intro j _ different
    rw [inner_smul_right, orthogonal different.symm, mul_zero]
  · simp

/-- The canonical scalar coimage identifies exactly the observed coordinates. -/
def coimageEquiv
    (orthogonal : Pairwise (fun i j => inner ℂ (column i) (column j) = 0))
    (live : ∀ i, column i ≠ 0) : ResidualCarrier (observe column).toLinearMap ≃ₗ[ℂ] (I → ℂ) :=
  LinearMap.quotKerEquivOfSurjective (observe column).toLinearMap
    (fun value => ⟨representative column value, read_representative column orthogonal live value⟩)

theorem coimage_source
    (orthogonal : Pairwise (fun i j => inner ℂ (column i) (column j) = 0))
    (live : ∀ i, column i ≠ 0) (source : E) :
    coimageEquiv column orthogonal live (canonicalResidual (observe column).toLinearMap source) =
      observe column source :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _ _ source

theorem representative_orthogonal (value : I → ℂ) {invisible : E}
    (silence : observe column invisible = 0) :
    inner ℂ (representative column value) invisible = 0 := by
  unfold representative
  rw [sum_inner]
  apply Finset.sum_eq_zero
  intro i _
  have atSlot : inner ℂ (column i) invisible = 0 := congrFun silence i
  rw [inner_smul_left, atSlot, mul_zero]

/-- The same observation retains its entire invisible fibre and pays the exact energy split. -/
theorem fibre_split
    (orthogonal : Pairwise (fun i j => inner ℂ (column i) (column j) = 0))
    (live : ∀ i, column i ≠ 0) (source : E) :
    let visible := representative column (observe column source)
    let invisible := source - visible
    observe column invisible = 0 ∧ ‖source‖^2 = ‖visible‖^2 + ‖invisible‖^2 := by
  let visible := representative column (observe column source)
  let invisible := source - visible
  have silence : observe column invisible = 0 := by
    dsimp [invisible, visible]
    rw [map_sub, read_representative column orthogonal live, sub_self]
  have orth := representative_orthogonal column (observe column source) silence
  have energy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero visible invisible orth
  have whole : visible + invisible = source := by dsimp [invisible]; abel
  rw [whole] at energy
  exact ⟨silence, by simpa only [pow_two] using energy⟩

end SaturationMonoid.OrthogonalSourceObservation
