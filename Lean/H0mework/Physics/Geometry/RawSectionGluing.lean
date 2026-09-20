import H0mework.Realization.Relations.FintypeDerivation
import Mathlib
import H0mework.Realization.Fields.SectionCover

/-!
# Raw section gluing and transition flatness

This module reuses `SectionIndexedCover`, which stores restriction, overlap,
and glue operations without a descent proof.  A selected local family and a
raw additive transition function are added, still without compatibility or
flatness certificates.

Overlap compatibility, correctness of the computed glue, uniqueness of a
global restriction, and transition flatness are four separate derived laws.
Concrete integer models show that each can fail while the other three hold.
No `SectionDescentCertificate` or caller-supplied compatibility proposition is
used as producer input.
-/

namespace SaturationMonoid
namespace PhysicsCore

universe uIndex uGlobal uLocal uOverlap uTransition

structure RawSectionTransitionInstance
    (Index : Type uIndex) (Global : Type uGlobal) (Local : Type uLocal)
    (Overlap : Type uOverlap) (Transition : Type uTransition) where
  cover :
    SectionIndexedCover Index Global (fun _ => Local) (fun _ _ => Overlap)
  localFamily : ∀ _ : Index, Local
  transition : Index → Index → Transition

namespace RawSectionTransitionInstance

variable {Index : Type uIndex} {Global : Type uGlobal}
variable {Local : Type uLocal} {Overlap : Type uOverlap}
variable {Transition : Type uTransition}

def CurrentOverlapCompatible
    (S : RawSectionTransitionInstance Index Global Local Overlap Transition) :
    Prop :=
  SectionOverlapCompatible S.cover S.localFamily

def CurrentGlueCorrect
    (S : RawSectionTransitionInstance Index Global Local Overlap Transition) :
    Prop :=
  GlobalRestrictsTo S.cover (S.cover.glue S.localFamily) S.localFamily

def CurrentGlueUnique
    (S : RawSectionTransitionInstance Index Global Local Overlap Transition) :
    Prop :=
  ∀ g : Global,
    GlobalRestrictsTo S.cover g S.localFamily →
      g = S.cover.glue S.localFamily

/-- Discrete additive cocycle/flatness law on every index triple. -/
def TransitionFlat
    [AddGroup Transition]
    (S : RawSectionTransitionInstance Index Global Local Overlap Transition) :
    Prop :=
  ∀ i j k : Index,
    S.transition j k + S.transition i j = S.transition i k

def SectionTransitionAdmissible
    [AddGroup Transition]
    (S : RawSectionTransitionInstance Index Global Local Overlap Transition) :
    Prop :=
  S.CurrentOverlapCompatible ∧
    S.CurrentGlueCorrect ∧
      S.CurrentGlueUnique ∧
        S.TransitionFlat

inductive SectionTransitionCoordinate where
  | overlapCompatibility
  | glueCorrectness
  | glueUniqueness
  | transitionFlatness
  deriving DecidableEq, Repr, FintypeViaProxy

def CoordinateHolds
    [AddGroup Transition]
    (S : RawSectionTransitionInstance Index Global Local Overlap Transition) :
    SectionTransitionCoordinate → Prop
  | .overlapCompatibility => S.CurrentOverlapCompatible
  | .glueCorrectness => S.CurrentGlueCorrect
  | .glueUniqueness => S.CurrentGlueUnique
  | .transitionFlatness => S.TransitionFlat

theorem sectionTransitionAdmissible_iff_all_coordinates
    [AddGroup Transition]
    (S : RawSectionTransitionInstance Index Global Local Overlap Transition) :
    S.SectionTransitionAdmissible ↔ ∀ c, S.CoordinateHolds c := by
  constructor
  · rintro ⟨hoverlap, hcorrect, hunique, hflat⟩ c
    cases c with
    | overlapCompatibility => exact hoverlap
    | glueCorrectness => exact hcorrect
    | glueUniqueness => exact hunique
    | transitionFlatness => exact hflat
  · intro hall
    exact ⟨hall .overlapCompatibility, hall .glueCorrectness,
      hall .glueUniqueness, hall .transitionFlatness⟩

theorem not_sectionTransitionAdmissible_iff_exists_failed_coordinate
    [AddGroup Transition]
    (S : RawSectionTransitionInstance Index Global Local Overlap Transition) :
    ¬ S.SectionTransitionAdmissible ↔ ∃ c, ¬ S.CoordinateHolds c := by
  classical
  constructor
  · intro hnot
    by_contra hnone
    push Not at hnone
    exact hnot (S.sectionTransitionAdmissible_iff_all_coordinates.mpr hnone)
  · rintro ⟨c, hc⟩ hadmissible
    exact hc (S.sectionTransitionAdmissible_iff_all_coordinates.mp hadmissible c)

def OnlyFails
    [AddGroup Transition]
    (S : RawSectionTransitionInstance Index Global Local Overlap Transition)
    (failed : SectionTransitionCoordinate) : Prop :=
  ¬ S.CoordinateHolds failed ∧
    ∀ c, c ≠ failed → S.CoordinateHolds c

namespace RawSectionGluingToy

abbrev Cover :=
  SectionIndexedCover Bool ℤ (fun _ => ℤ) (fun _ _ => ℤ)

abbrev System :=
  RawSectionTransitionInstance Bool ℤ ℤ ℤ ℤ

def identityOverlapCover : Cover where
  toLocal := fun _ g => g
  leftToOverlap := fun _ _ sectionValue => sectionValue
  rightToOverlap := fun _ _ sectionValue => sectionValue
  glue := fun sections => sections false

def admissibleSystem : System where
  cover := identityOverlapCover
  localFamily := fun _ => 0
  transition := fun _ _ => 0

/-- The family `0,1` is incompatible, while one global integer still realizes
it through index-dependent restrictions. -/
def overlapFailureSystem : System where
  cover :=
    { toLocal := fun i g => if i then g + 1 else g
      leftToOverlap := fun _ _ sectionValue => sectionValue
      rightToOverlap := fun _ _ sectionValue => sectionValue
      glue := fun sections => sections false }
  localFamily := fun i => if i then 1 else 0
  transition := fun _ _ => 0

/-- No global can restrict to the compatible zero family, so the computed
glue is incorrect while the uniqueness implication is vacuously true. -/
def glueCorrectnessFailureSystem : System where
  cover :=
    { toLocal := fun _ _ => 1
      leftToOverlap := fun _ _ sectionValue => sectionValue
      rightToOverlap := fun _ _ sectionValue => sectionValue
      glue := fun _ => 0 }
  localFamily := fun _ => 0
  transition := fun _ _ => 0

/-- Every global restricts to the zero family, so the selected zero glue is
correct but not unique. -/
def glueUniquenessFailureSystem : System where
  cover :=
    { toLocal := fun _ _ => 0
      leftToOverlap := fun _ _ sectionValue => sectionValue
      rightToOverlap := fun _ _ sectionValue => sectionValue
      glue := fun _ => 0 }
  localFamily := fun _ => 0
  transition := fun _ _ => 0

/-- Section descent is sound, but the constant-one transition violates the
additive cocycle law `1 + 1 = 1`. -/
def transitionFailureSystem : System where
  cover := identityOverlapCover
  localFamily := fun _ => 0
  transition := fun _ _ => 1

theorem admissibleSystem_overlap :
    admissibleSystem.CurrentOverlapCompatible := by
  intro i j
  rfl

theorem admissibleSystem_glueCorrect :
    admissibleSystem.CurrentGlueCorrect := by
  intro i
  rfl

theorem admissibleSystem_glueUnique :
    admissibleSystem.CurrentGlueUnique := by
  intro g hrestricts
  have hfalse := hrestricts false
  simpa [admissibleSystem, identityOverlapCover] using hfalse

theorem admissibleSystem_flat : admissibleSystem.TransitionFlat := by
  intro i j k
  simp [admissibleSystem]

theorem admissibleSystem_admissible :
    admissibleSystem.SectionTransitionAdmissible :=
  ⟨admissibleSystem_overlap, admissibleSystem_glueCorrect,
    admissibleSystem_glueUnique, admissibleSystem_flat⟩

theorem overlapFailureSystem_not_overlap :
    ¬ overlapFailureSystem.CurrentOverlapCompatible := by
  intro hoverlap
  have hvalue := hoverlap false true
  norm_num [overlapFailureSystem] at hvalue

theorem overlapFailureSystem_glueCorrect :
    overlapFailureSystem.CurrentGlueCorrect := by
  intro i
  cases i <;> norm_num [overlapFailureSystem]

theorem overlapFailureSystem_glueUnique :
    overlapFailureSystem.CurrentGlueUnique := by
  intro g hrestricts
  have hfalse := hrestricts false
  simpa [overlapFailureSystem] using hfalse

theorem overlapFailureSystem_flat : overlapFailureSystem.TransitionFlat := by
  intro i j k
  simp [overlapFailureSystem]

theorem glueCorrectnessFailureSystem_overlap :
    glueCorrectnessFailureSystem.CurrentOverlapCompatible := by
  intro i j
  rfl

theorem glueCorrectnessFailureSystem_not_glueCorrect :
    ¬ glueCorrectnessFailureSystem.CurrentGlueCorrect := by
  intro hcorrect
  have hfalse := hcorrect false
  norm_num [glueCorrectnessFailureSystem] at hfalse

theorem glueCorrectnessFailureSystem_glueUnique :
    glueCorrectnessFailureSystem.CurrentGlueUnique := by
  intro g hrestricts
  have hfalse := hrestricts false
  norm_num [glueCorrectnessFailureSystem] at hfalse

theorem glueCorrectnessFailureSystem_flat :
    glueCorrectnessFailureSystem.TransitionFlat := by
  intro i j k
  simp [glueCorrectnessFailureSystem]

theorem glueUniquenessFailureSystem_overlap :
    glueUniquenessFailureSystem.CurrentOverlapCompatible := by
  intro i j
  rfl

theorem glueUniquenessFailureSystem_glueCorrect :
    glueUniquenessFailureSystem.CurrentGlueCorrect := by
  intro i
  rfl

theorem glueUniquenessFailureSystem_not_glueUnique :
    ¬ glueUniquenessFailureSystem.CurrentGlueUnique := by
  intro hunique
  have hone : (1 : ℤ) = 0 := hunique 1 (by
    intro i
    rfl)
  norm_num at hone

theorem glueUniquenessFailureSystem_flat :
    glueUniquenessFailureSystem.TransitionFlat := by
  intro i j k
  simp [glueUniquenessFailureSystem]

theorem transitionFailureSystem_overlap :
    transitionFailureSystem.CurrentOverlapCompatible := by
  intro i j
  rfl

theorem transitionFailureSystem_glueCorrect :
    transitionFailureSystem.CurrentGlueCorrect := by
  intro i
  rfl

theorem transitionFailureSystem_glueUnique :
    transitionFailureSystem.CurrentGlueUnique := by
  intro g hrestricts
  have hfalse := hrestricts false
  simpa [transitionFailureSystem, identityOverlapCover] using hfalse

theorem transitionFailureSystem_not_flat :
    ¬ transitionFailureSystem.TransitionFlat := by
  intro hflat
  have hvalue := hflat false false false
  norm_num [transitionFailureSystem] at hvalue

theorem overlapFailureSystem_onlyFails :
    overlapFailureSystem.OnlyFails .overlapCompatibility := by
  refine ⟨overlapFailureSystem_not_overlap, ?_⟩
  intro c hc
  cases c with
  | overlapCompatibility => exact (hc rfl).elim
  | glueCorrectness => exact overlapFailureSystem_glueCorrect
  | glueUniqueness => exact overlapFailureSystem_glueUnique
  | transitionFlatness => exact overlapFailureSystem_flat

theorem glueCorrectnessFailureSystem_onlyFails :
    glueCorrectnessFailureSystem.OnlyFails .glueCorrectness := by
  refine ⟨glueCorrectnessFailureSystem_not_glueCorrect, ?_⟩
  intro c hc
  cases c with
  | overlapCompatibility => exact glueCorrectnessFailureSystem_overlap
  | glueCorrectness => exact (hc rfl).elim
  | glueUniqueness => exact glueCorrectnessFailureSystem_glueUnique
  | transitionFlatness => exact glueCorrectnessFailureSystem_flat

theorem glueUniquenessFailureSystem_onlyFails :
    glueUniquenessFailureSystem.OnlyFails .glueUniqueness := by
  refine ⟨glueUniquenessFailureSystem_not_glueUnique, ?_⟩
  intro c hc
  cases c with
  | overlapCompatibility => exact glueUniquenessFailureSystem_overlap
  | glueCorrectness => exact glueUniquenessFailureSystem_glueCorrect
  | glueUniqueness => exact (hc rfl).elim
  | transitionFlatness => exact glueUniquenessFailureSystem_flat

theorem transitionFailureSystem_onlyFails :
    transitionFailureSystem.OnlyFails .transitionFlatness := by
  refine ⟨transitionFailureSystem_not_flat, ?_⟩
  intro c hc
  cases c with
  | overlapCompatibility => exact transitionFailureSystem_overlap
  | glueCorrectness => exact transitionFailureSystem_glueCorrect
  | glueUniqueness => exact transitionFailureSystem_glueUnique
  | transitionFlatness => exact (hc rfl).elim

theorem every_sectionTransitionCoordinate_has_only_one_failure_model
    (c : SectionTransitionCoordinate) :
    ∃ S : System, S.OnlyFails c := by
  cases c with
  | overlapCompatibility =>
      exact ⟨overlapFailureSystem, overlapFailureSystem_onlyFails⟩
  | glueCorrectness =>
      exact ⟨glueCorrectnessFailureSystem,
        glueCorrectnessFailureSystem_onlyFails⟩
  | glueUniqueness =>
      exact ⟨glueUniquenessFailureSystem,
        glueUniquenessFailureSystem_onlyFails⟩
  | transitionFlatness =>
      exact ⟨transitionFailureSystem, transitionFailureSystem_onlyFails⟩

end RawSectionGluingToy

end RawSectionTransitionInstance
end PhysicsCore
end SaturationMonoid
