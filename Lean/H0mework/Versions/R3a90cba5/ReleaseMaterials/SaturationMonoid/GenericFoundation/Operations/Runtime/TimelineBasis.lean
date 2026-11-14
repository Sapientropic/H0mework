import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.MatrixBorder
import Mathlib.Algebra.BigOperators.Finsupp.Basic

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationRuntime.TimelineBasis

open SourceGeneratedFiniteGram.MatrixBorder
open scoped Matrix BigOperators

universe a r
variable {A : Type a} {R : Type r} [CommRing R] {n : Nat}

/-- The first column is the initial material; each other column is a consecutive effect. -/
def word (point : Fin (n + 1) → A) : Fin (n + 1) → A →₀ R :=
  Fin.cases (Finsupp.single (point 0) 1) (fun i =>
    Finsupp.single (point i.succ) 1 - Finsupp.single (point i.castSucc) 1)

@[simp] theorem word_zero (point : Fin (n + 1) → A) :
    word (R := R) point 0 = Finsupp.single (point 0) 1 := Fin.cases_zero

@[simp] theorem word_succ (point : Fin (n + 1) → A) (i : Fin n) :
    word (R := R) point i.succ =
      Finsupp.single (point i.succ) 1 - Finsupp.single (point i.castSucc) 1 := Fin.cases_succ i

def observe (point : Fin (n + 1) → A) (material : A →₀ R) : Fin (n + 1) → R :=
  fun i => material (point i)

def observed (point : Fin (n + 1) → A) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of (fun i j => observe point (word point j) i)

private abbrev prior (point : Fin (n + 2) → A) : Fin (n + 1) → A :=
  point ∘ Fin.castSucc

private theorem word_retained (point : Fin (n + 2) → A) (j : Fin (n + 1)) :
    word (R := R) point j.castSucc = word (prior point) j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [Fin.castSucc_zero, word_zero, Function.comp_apply]
  · simp only [Fin.castSucc_succ, word_succ, Function.comp_apply]

private def newColumn (point : Fin (n + 2) → A) (i : Fin (n + 1)) : R :=
  observed point i.castSucc (Fin.last (n + 1))

private def newRow (point : Fin (n + 2) → A) (j : Fin (n + 1)) : R :=
  observed point (Fin.last (n + 1)) j.castSucc

private def newCell (point : Fin (n + 2) → A) : R :=
  observed point (Fin.last (n + 1)) (Fin.last (n + 1))

theorem observed_border (point : Fin (n + 2) → A) :
    observed (R := R) point =
      border (observed (prior point)) (newColumn point) (newRow point) (newCell point) := by
  apply Matrix.ext
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [border_new_new, newCell]
    · simp only [border_new_old, newRow]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [border_old_new, newColumn]
    · rw [border_old_old]
      change word (R := R) point j.castSucc (point i.castSucc) =
        word (prior point) j (point i.castSucc)
      rw [word_retained]

private theorem word_vanishes (point : Fin (n + 1) → A) (x : A)
    (absent : ∀ i, x ≠ point i) (j : Fin (n + 1)) : word (R := R) point j x = 0 := by
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [word_zero, Finsupp.single_eq_of_ne (absent 0)]
  · rw [word_succ, Finsupp.sub_apply, Finsupp.single_eq_of_ne (absent i.succ),
      Finsupp.single_eq_of_ne (absent i.castSucc), sub_zero]

/-- The new occurrence reads no old column and reads its own actual effect with coefficient one. -/
theorem observed_pivot (point : Fin (n + 2) → A) (distinct : Function.Injective point)
    [Invertible (observed (R := R) (prior point))] :
    pivot (observed (R := R) (prior point)) (newColumn point) (newRow point) (newCell point) = 1 := by
  have absent (i : Fin (n + 1)) : point (Fin.last (n + 1)) ≠ point i.castSucc :=
    fun eq => Fin.castSucc_ne_last i (distinct eq.symm)
  have oldRow : newRow (R := R) point = 0 := by
    funext j
    change word (R := R) point j.castSucc (point (Fin.last (n + 1))) = 0
    rw [word_retained]
    exact word_vanishes (prior point) _ absent j
  have newEntry : newCell (R := R) point = 1 := by
    have effect := word_succ (R := R) point (Fin.last n)
    rw [Fin.succ_last] at effect
    change word (R := R) point (Fin.last (n + 1)) (point (Fin.last (n + 1))) = 1
    rw [effect, Finsupp.sub_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne (absent (Fin.last n)), sub_zero]
  rw [pivot, oldRow, zero_dotProduct, sub_zero, newEntry]

private theorem singleton_det (point : Fin 1 → A) : (observed (R := R) point).det = 1 := by
  rw [Matrix.det_fin_one]
  change word (R := R) point 0 (point 0) = 1
  rw [word_zero, Finsupp.single_eq_same]

private theorem prior_injective (point : Fin (n + 2) → A) (distinct : Function.Injective point) :
    Function.Injective (prior point) := by
  intro i j same
  have retained : i.castSucc = j.castSucc := distinct same
  exact Fin.ext (congrArg (fun k : Fin (n + 2) => k.val) retained)

/-- Read the old inverse, then append the actual row and column using their unit pivot. -/
@[instance_reducible]
def inverse (point : Fin (n + 1) → A) (distinct : Function.Injective point) :
    Invertible (observed (R := R) point) :=
  (Nat.rec (motive := fun length => (points : Fin (length + 1) → A) →
      Function.Injective points → Invertible (observed (R := R) points))
    (fun points _ => Matrix.invertibleOfIsUnitDet _ (by rw [singleton_det]; exact isUnit_one))
    (fun _ previous points injective => by
      letI : Invertible (observed (R := R) (prior points)) :=
        previous (prior points) (prior_injective points injective)
      have unitPivot : IsUnit (pivot (observed (R := R) (prior points))
          (newColumn points) (newRow points) (newCell points)) := by
        rw [observed_pivot (R := R) points injective]
        exact isUnit_one
      rw [observed_border]
      exact borderInverse _ _ _ _ unitPivot)
    n) point distinct

theorem determinant_one (point : Fin (n + 1) → A) (distinct : Function.Injective point) :
    (observed (R := R) point).det = 1 := by
  induction n with
  | zero => exact singleton_det point
  | succ n previous =>
      have retained := prior_injective point distinct
      let retainedInverse := inverse (R := R) (prior point) retained
      rw [observed_border, border_det, observed_pivot (R := R) point distinct, previous (prior point) retained, one_mul]

def synth (point : Fin (n + 1) → A) (coeff : Fin (n + 1) → R) : A →₀ R :=
  ∑ j, coeff j • word point j

def recover (point : Fin (n + 1) → A) (inverse : Invertible (observed (R := R) point))
    (material : A →₀ R) : Fin (n + 1) → R :=
  inverse.invOf *ᵥ observe point material

theorem observe_synth (point : Fin (n + 1) → A) (coeff : Fin (n + 1) → R) :
    observe point (synth point coeff) = observed point *ᵥ coeff := by
  funext i
  simp only [observe, synth, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    Matrix.mulVec_apply_eq_sum, observed, Matrix.of_apply]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

theorem recover_synth (point : Fin (n + 1) → A) (inv : Invertible (observed (R := R) point))
    (coeff : Fin (n + 1) → R) : recover point inv (synth point coeff) = coeff := by
  let retainedInverse := inv
  change ⅟(observed point) *ᵥ observe point (synth point coeff) = coeff
  rw [observe_synth, Matrix.mulVec_mulVec, invOf_mul_self, Matrix.one_mulVec]

theorem synth_terminal (point : Fin (n + 1) → A) :
    synth (R := R) point (fun _ => 1) = Finsupp.single (point (Fin.last n)) 1 := by
  simp only [synth, one_smul]
  induction n with
  | zero =>
      rw [Fin.last_zero]
      exact (Fin.sum_univ_one (word (R := R) point)).trans (word_zero point)
  | succ n previous =>
      rw [Fin.sum_univ_castSucc]
      have retained : (∑ j : Fin (n + 1), word (R := R) point j.castSucc) =
          ∑ j, word (R := R) (prior point) j :=
        Finset.sum_congr rfl (fun j _ => word_retained point j)
      rw [retained, previous (prior point), ← Fin.succ_last n, word_succ]
      change Finsupp.single (point (Fin.last n).castSucc) (1 : R) +
        (Finsupp.single (point (Fin.last n).succ) 1 - Finsupp.single (point (Fin.last n).castSucc) 1) = _
      abel

end SourceOperationRuntime.TimelineBasis
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
