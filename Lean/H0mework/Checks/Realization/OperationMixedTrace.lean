import H0mework.Realization.Operations.MixedTrace
import H0mework.Checks.Realization.OperationEffects
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Exact mixed-term inventory and noncommutative direct consumers. -/

set_option autoImplicit false

namespace SaturationMonoid.SourceOperationEffects.MixedTraceControls

section Cubic

variable (R : Type*) [NonUnitalNonAssocRing R]

abbrev Tagged := Expr (fun _ : Unit => R) (ChangedVar (fun _ => ℕ)) ()

def oldVar (n : ℕ) : Tagged R := .var (n, .old)

def incrementVar (n : ℕ) : Tagged R := .var (n, .increment)

def mulTerm (a b : Tagged R) : Tagged R :=
  .bilinear (s := ()) (t := ()) AddMonoidHom.mul a b

/-- All seven syntactic terms, in generated order, before any semantic summation. -/
theorem cubic_ordered_terms :
    (Controls.cubic R).mixedTerms =
      [mulTerm R (mulTerm R (oldVar R 0) (oldVar R 1)) (incrementVar R 2),
       mulTerm R (mulTerm R (oldVar R 0) (incrementVar R 1)) (oldVar R 2),
       mulTerm R (mulTerm R (incrementVar R 0) (oldVar R 1)) (oldVar R 2),
       mulTerm R (mulTerm R (incrementVar R 0) (incrementVar R 1)) (oldVar R 2),
       mulTerm R (mulTerm R (oldVar R 0) (incrementVar R 1)) (incrementVar R 2),
       mulTerm R (mulTerm R (incrementVar R 0) (oldVar R 1)) (incrementVar R 2),
       mulTerm R (mulTerm R (incrementVar R 0) (incrementVar R 1)) (incrementVar R 2)] :=
  rfl

theorem cubic_trace_length : (Controls.cubic R).mixedTerms.length = 7 := rfl

theorem cubic_termwise_values (x y z dx dy dz : R) :
    ((Controls.cubic R).mixedTerms.map (fun term => term.eval
      (mixedEnvironment (Controls.tripleEnvironment R x y z)
        (Controls.tripleEnvironment R dx dy dz)))) =
      [(x * y) * dz, (x * dy) * z, (dx * y) * z, (dx * dy) * z,
       (x * dy) * dz, (dx * y) * dz, (dx * dy) * dz] := rfl

theorem cubic_trace_update (x y z dx dy dz : R) :
    ((x + dx) * (y + dy)) * (z + dz) = (x * y) * z +
      [(x * y) * dz, (x * dy) * z, (dx * y) * z, (dx * dy) * z,
       (x * dy) * dz, (dx * y) * dz, (dx * dy) * dz].sum := by
  have h := (Controls.cubic R).eval_update_mixedTerms
    (Controls.tripleEnvironment R x y z) (Controls.tripleEnvironment R dx dy dz)
  rw [cubic_termwise_values] at h
  exact h

/-- Repeated source occurrences remain repeated symbolic terms. -/
theorem duplicate_occurrences_retained :
    (Expr.add (Expr.var 0) (Expr.var 0) :
      Expr (fun _ : Unit => R) (fun _ => ℕ) ()).mixedTerms =
        [incrementVar R 0, incrementVar R 0] := rfl

end Cubic

abbrev Mat := Matrix (Fin 2) (Fin 2) ℤ

def matrixA : Mat := !![0, 1; 0, 0]

def matrixB : Mat := !![0, 0; 1, 0]

def matrixSquare : Expr (fun _ : Unit => Mat) (fun _ => Unit) () :=
  .bilinear (s := ()) (t := ()) AddMonoidHom.mul (.var ()) (.var ())

theorem matrix_ordered_terms :
    matrixSquare.mixedTerms.map (fun term => term.eval
      (mixedEnvironment (fun _ _ => matrixA) (fun _ _ => matrixB))) =
        [matrixA * matrixB, matrixB * matrixA, matrixB * matrixB] := rfl

/-- Actual matrix multiplication distinguishes the two generated cross terms. -/
theorem matrix_cross_terms_distinct : matrixA * matrixB ≠ matrixB * matrixA := by
  intro h
  have h00 := congrArg (fun m : Mat => m 0 0) h
  simp [matrixA, matrixB] at h00

theorem matrix_trace_update :
    (matrixA + matrixB) * (matrixA + matrixB) = matrixA * matrixA +
      [matrixA * matrixB, matrixB * matrixA, matrixB * matrixB].sum := by
  have h := matrixSquare.eval_update_mixedTerms
    (fun _ _ => matrixA) (fun _ _ => matrixB)
  rw [matrix_ordered_terms] at h
  exact h

end SaturationMonoid.SourceOperationEffects.MixedTraceControls
