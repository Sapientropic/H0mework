import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Prod

/-!
# Effectivity-preserving finite fibre disposition

An actual finite candidate family is evaluated before any additive-group or
linear completion is formed.  The generated disposition therefore retains
either one replayable candidate in the target fibre or the complete finite
image together with a proof that the target is absent from it.

The evaluator and target are the only inputs.  Neither a fibre witness nor a
residual-zero certificate is accepted from the caller.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedEffectiveFibreDisposition

universe u v

variable {Candidate : Type u} [Fintype Candidate]
variable {Target : Type v} [DecidableEq Target]

/-- The actual inverse fibre of a finite candidate evaluator.  Its witness
stays in `Type`, so the selected candidate can be replayed downstream. -/
abbrev Fibre (evaluation : Candidate → Target) (target : Target) : Type u :=
  {candidate : Candidate // evaluation candidate = target}

/-- The exact finite effective image, before group completion. -/
def candidateImage (evaluation : Candidate → Target) : Finset Target :=
  Finset.univ.image evaluation

theorem target_mem_candidateImage_iff
    (evaluation : Candidate → Target) (target : Target) :
    target ∈ candidateImage evaluation ↔
      Nonempty (Fibre evaluation target) := by
  constructor
  · intro membership
    obtain ⟨candidate, _candidateMem, evaluates⟩ :=
      Finset.mem_image.mp membership
    exact ⟨⟨candidate, evaluates⟩⟩
  · rintro ⟨⟨candidate, evaluates⟩⟩
    exact Finset.mem_image.mpr ⟨candidate, Finset.mem_univ _, evaluates⟩

/-- Explicit faithful residual.  It records the entire finite effective
image and proves that the requested target is absent from it. -/
structure FaithfulResidual
    (evaluation : Candidate → Target) (target : Target) : Type v where
  private mk ::
  image : Finset Target
  image_eq : image = candidateImage evaluation
  target_not_mem_image : target ∉ image

namespace FaithfulResidual

variable {evaluation : Candidate → Target} {target : Target}

theorem target_not_mem
    (residual : FaithfulResidual evaluation target) :
    target ∉ candidateImage evaluation := by
  rw [← residual.image_eq]
  exact residual.target_not_mem_image

theorem misses
    (residual : FaithfulResidual evaluation target)
    (candidate : Candidate) :
    evaluation candidate ≠ target := by
  intro evaluates
  apply residual.target_not_mem
  exact Finset.mem_image.mpr
    ⟨candidate, Finset.mem_univ candidate, evaluates⟩

theorem fibre_is_empty
    (residual : FaithfulResidual evaluation target) :
    IsEmpty (Fibre evaluation target) := by
  constructor
  rintro ⟨candidate, evaluates⟩
  exact residual.misses candidate evaluates

end FaithfulResidual

/-- Total effectivity-preserving disposition. -/
inductive Disposition
    (evaluation : Candidate → Target) (target : Target) : Type (max u v) where
  | inhabited (witness : Fibre evaluation target)
  | residual (residual : FaithfulResidual evaluation target)

noncomputable def residualOfEmpty
    (evaluation : Candidate → Target) (target : Target)
    (empty : ¬ Nonempty (Fibre evaluation target)) :
    FaithfulResidual evaluation target := by
  refine ⟨candidateImage evaluation, rfl, ?_⟩
  intro membership
  exact empty ((target_mem_candidateImage_iff evaluation target).mp membership)

/-- The classifier decides the finite fibre internally. -/
noncomputable def settle
    (evaluation : Candidate → Target) (target : Target) :
    Disposition evaluation target := by
  classical
  by_cases inhabited : Nonempty (Fibre evaluation target)
  · exact .inhabited (Classical.choice inhabited)
  · exact .residual (residualOfEmpty evaluation target inhabited)

theorem total (evaluation : Candidate → Target) (target : Target) :
    Nonempty (Disposition evaluation target) :=
  ⟨settle evaluation target⟩

theorem settle_eq_inhabited_of_nonempty
    (evaluation : Candidate → Target) (target : Target)
    (inhabited : Nonempty (Fibre evaluation target)) :
    settle evaluation target =
      .inhabited (Classical.choice inhabited) := by
  classical
  simp [settle, inhabited]

theorem settle_eq_residual_of_empty
    (evaluation : Candidate → Target) (target : Target)
    (empty : ¬ Nonempty (Fibre evaluation target)) :
    settle evaluation target =
      .residual (residualOfEmpty evaluation target empty) := by
  classical
  simp [settle, empty]

end SourceGeneratedEffectiveFibreDisposition
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
