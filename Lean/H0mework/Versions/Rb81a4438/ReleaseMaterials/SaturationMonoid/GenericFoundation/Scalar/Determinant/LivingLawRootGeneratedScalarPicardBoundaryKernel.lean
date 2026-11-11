import Mathlib.Algebra.Module.StablyFree.FreeOfInvertible
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.Flat.LocallyFree

/-!
# Scalar Picard boundary

The finite-free face already generates an invertible top exterior power.
A finite projective module of constant stalk rank already generates actual
free charts around every prime.  The second result does not yet generate
top-exterior invertibility: the exterior-power base-change and the converse
from locally free rank one to `Module.Invertible` remain API residuals.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarPicardBoundary

open Module

noncomputable section

universe r o

variable {R : Type r} [CommRing R]
variable {O : Type o} [AddCommGroup O] [Module R O]

/-- The top exterior power of a finite free module is an invertible module. -/
theorem freeTopExteriorInvertible
    [Module.Free R O] [Module.Finite R O] :
    Module.Invertible R (⋀[R]^(Module.finrank R O) O) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · let _ : Subsingleton R := hR
    let _ : Subsingleton (⋀[R]^(Module.finrank R O) O) := Module.subsingleton R _
    exact Module.Invertible.congr
      (LinearEquiv.ofSubsingleton R (⋀[R]^(Module.finrank R O) O))
  · let _ : Nontrivial R := hR
    let equivalence : R ≃ₗ[R] ⋀[R]^(Module.finrank R O) O :=
      (Module.nonempty_linearEquiv_of_finrank_eq_one (by
        simp [exteriorPower.finrank_eq])).some
    exact Module.Invertible.congr equivalence

/-- A finite projective constant-rank module is free on an actual neighborhood of every prime. -/
theorem finiteProjectiveConstantRank_awayFree
    [Module.Finite R O] [Module.Projective R O] {n : ℕ}
    (rankAtStalk : Module.rankAtStalk (R := R) O = n)
    (prime : Ideal R) [prime.IsPrime] :
    ∃ element ∉ prime,
      Module.Free (Localization.Away element) (LocalizedModule.Away element O) := by
  apply Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant O prime
  intro maximal _
  simp [rankAtStalk]

end
end SourceGeneratedScalarPicardBoundary
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
