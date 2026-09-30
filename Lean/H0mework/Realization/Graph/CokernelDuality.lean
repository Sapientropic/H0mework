import Mathlib.Analysis.InnerProductSpace.Dual
import H0mework.Realization.Graph.Cokernel

/-!
# Automatic Riesz duality of the functional graph cokernel

The closed-range quotient is already a complete complex Hilbert space, so Fréchet–Riesz gives its
canonical conjugate-linear isometric equivalence with the strong dual.  Thus the descended
functional has a canonical Riesz vector without any additional premise.

Over `ℂ`, Riesz duality is conjugate-linear, hence the precise type is `≃ₗᵢ⋆[ℂ]`, not
`≃ₗᵢ[ℂ]`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedFunctionalGraphCokernel

open SourceGeneratedHilbertCokernel
open scoped InnerProductSpace

noncomputable section

universe c r h

variable {C : Type c} [AddCommGroup C] [Module ℂ C]
variable {Rel : Type r} [AddCommGroup Rel] [Module ℂ Rel]
variable {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The source-generated relation range is closed by construction.  Registering this exact fact
lets the quotient inherit Mathlib's normed-group structure without a new hypothesis. -/
instance relationClosedRange_isClosed
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ)
    (relation : Rel →ₗ[ℂ] C) :
    IsClosed
      ((closedRange (relationGraphMap feature functional relation)).toSubmodule :
        Set (GraphCompletion feature functional)) :=
  (closedRange (relationGraphMap feature functional relation)).isClosed

/-- Canonical Fréchet–Riesz duality of the generated closed-range quotient. -/
def closedRangeQuotientRiesz
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ)
    (relation : Rel →ₗ[ℂ] C) :
    ClosedRangeQuotient feature functional relation ≃ₗᵢ⋆[ℂ]
      StrongDual ℂ (ClosedRangeQuotient feature functional relation) :=
  InnerProductSpace.toDual ℂ (ClosedRangeQuotient feature functional relation)

@[simp]
theorem closedRangeQuotientRiesz_apply_apply
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ)
    (relation : Rel →ₗ[ℂ] C)
    (representer quotient : ClosedRangeQuotient feature functional relation) :
    closedRangeQuotientRiesz feature functional relation representer quotient =
      ⟪representer, quotient⟫_ℂ :=
  rfl

/-- The canonical Riesz vector representing the descended functional. -/
def descendedRieszVector
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ)
    (relation : Rel →ₗ[ℂ] C)
    (annihilates : functional.comp relation = 0) :
    ClosedRangeQuotient feature functional relation :=
  (closedRangeQuotientRiesz feature functional relation).symm
    (descendedFunctional feature functional relation annihilates)

/-- Riesz readback on every quotient class. -/
@[simp]
theorem descendedRieszVector_inner
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ)
    (relation : Rel →ₗ[ℂ] C)
    (annihilates : functional.comp relation = 0)
    (quotient : ClosedRangeQuotient feature functional relation) :
    ⟪descendedRieszVector feature functional relation annihilates, quotient⟫_ℂ =
      descendedFunctional feature functional relation annihilates quotient := by
  exact InnerProductSpace.toDual_symm_apply

/-- On the dense canonical source, the Riesz pairing reads the original functional exactly. -/
@[simp]
theorem descendedRieszVector_source_readback
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ)
    (relation : Rel →ₗ[ℂ] C)
    (annihilates : functional.comp relation = 0) (value : C) :
    ⟪descendedRieszVector feature functional relation annihilates,
      canonicalSourceMap feature functional relation value⟫_ℂ = functional value := by
  rw [descendedRieszVector_inner, descendedFunctional_source_readback]

/-- A nonzero source functional generates a nonzero canonical Riesz
representer after relation descent. -/
theorem descendedRieszVector_ne_zero
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ)
    (relation : Rel →ₗ[ℂ] C)
    (annihilates : functional.comp relation = 0)
    (nonzero : functional ≠ 0) :
    descendedRieszVector feature functional relation annihilates ≠ 0 := by
  intro vectorZero
  have mapped := congrArg
    (closedRangeQuotientRiesz feature functional relation) vectorZero
  have rieszZero :
      closedRangeQuotientRiesz feature functional relation
          (0 : ClosedRangeQuotient feature functional relation) = 0 := by
    apply ContinuousLinearMap.ext
    intro quotient
    rw [closedRangeQuotientRiesz_apply_apply]
    simp
  rw [rieszZero] at mapped
  have functionalZero :
      descendedFunctional feature functional relation annihilates = 0 := by
    simpa [descendedRieszVector] using mapped
  exact descendedFunctional_ne_zero feature functional relation
    annihilates nonzero functionalZero

end


end SourceGeneratedFunctionalGraphCokernel
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
