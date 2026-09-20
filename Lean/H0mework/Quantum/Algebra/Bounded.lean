import Mathlib.Analysis.CStarAlgebra.lpSpace
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-! The actual bounded family of complete Hilbert-space operators carries
Mathlib's product C⋆-algebra structure and its original coordinate evaluations. -/

set_option autoImplicit false

open scoped ENNReal

namespace SaturationMonoid.Quantum.Dynamics

noncomputable section

variable (E : ℕ → Type*) [∀ k, NormedAddCommGroup (E k)] [∀ k, InnerProductSpace ℂ (E k)]
  [∀ k, CompleteSpace (E k)] [∀ k, Nontrivial (E k)]

abbrev Bounded := lp (fun k => E k →L[ℂ] E k) ∞

instance boundedStarModule : StarModule ℂ (Bounded E) :=
  lp.instStarModuleSubtypePreLpMemAddSubgroup

instance boundedCStarAlgebra : CStarAlgebra (Bounded E) where

def eval (k : ℕ) : Bounded E →⋆ₐ[ℂ] (E k →L[ℂ] E k) where
  toFun A := A k
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

theorem eval_apply (k : ℕ) (A : Bounded E) : eval E k A = A k := rfl

theorem eval_norm_le (k : ℕ) (A : Bounded E) : ‖eval E k A‖ ≤ ‖A‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero A k

end
end SaturationMonoid.Quantum.Dynamics
