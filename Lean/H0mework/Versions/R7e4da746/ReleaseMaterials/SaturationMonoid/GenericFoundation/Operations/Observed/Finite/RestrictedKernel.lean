import H0mework.Realization.Operations.ObservationKernel
import Mathlib.RingTheory.Artinian.Module

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.FiniteRestriction

open SourceGeneratedActionObservationHistory

universe r u

variable {R : Type r} {C B : Type u} [CommRing R] [AddCommGroup C] [Module R C]
  [AddCommGroup B] [Module R B]
variable (action : C →ₗ[R] C) (observation : C →ₗ[R] B) (source : Submodule R C)

/-- Restrict the already generated observation to a finite source inventory. The source need not
be invariant: each slot still observes the original ambient action. -/
theorem restricted_kernel_attained [IsArtinian R source] :
    ∃ last : ℕ, LinearMap.ker ((prefixEvaluator action observation last).comp source.subtype) =
      (LinearMap.ker (sourceMap action observation)).comap source.subtype := by
  let kernel (n : ℕ) : Submodule R source :=
    LinearMap.ker ((prefixEvaluator action observation n).comp source.subtype)
  have nested : Antitone kernel := by
    intro early late le x hx
    change prefixEvaluator action observation early (x : C) = 0
    change prefixEvaluator action observation late (x : C) = 0 at hx
    funext i
    let j : Fin (late+1) := ⟨i.val, i.isLt.trans_le (Nat.succ_le_succ le)⟩
    exact congrFun hx j
  let chain : ℕ →o (Submodule R source)ᵒᵈ := ⟨kernel, nested⟩
  obtain ⟨last, stable⟩ := IsArtinian.monotone_stabilizes chain
  refine ⟨last, ?_⟩
  ext x
  change x ∈ kernel last ↔ (x : C) ∈ LinearMap.ker (sourceMap action observation)
  rw [mem_kernel_iff]
  constructor
  · intro zero n
    let bound := max n last
    have changeBound : kernel last = kernel bound := stable bound (le_max_right _ _)
    have visible : x ∈ kernel bound := changeBound ▸ zero
    change prefixEvaluator action observation bound (x : C) = 0 at visible
    exact congrFun visible ⟨n, Nat.lt_succ_of_le (le_max_left _ _)⟩
  · intro silent
    change prefixEvaluator action observation last (x : C) = 0
    funext i
    exact silent i.val

end SourceGeneratedActionObservationHistory.FiniteRestriction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
