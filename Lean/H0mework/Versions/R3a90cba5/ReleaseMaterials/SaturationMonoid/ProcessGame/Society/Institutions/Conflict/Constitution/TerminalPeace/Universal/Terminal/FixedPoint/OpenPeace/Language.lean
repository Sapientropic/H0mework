import H0mework.Versions.R2.Foundation.Inquiry.MinimalCoface
import Mathlib.Data.Set.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ObstructionGeneratedMinimalCoface

/-- Each extension has one address for the additional refusal scope.
Inherited expressions remain available as codes in the new language. -/
inductive Language (Old Claim : Type)
  | initial
  | extend (prior : Language Old Claim) (fresh : Set Claim)

namespace Language

variable {Old Claim : Type}

def Code : Language Old Claim → Type
  | .initial => Old
  | .extend prior _ => prior.Code ⊕ Unit

/-- Denotations are the claims a code can refuse. The original physical
words do not carry a refusal direction. -/
def denotes : (language : Language Old Claim) → language.Code → Set Claim
  | .initial, _ => ∅
  | .extend prior fresh, code =>
    match code with
    | .inl inherited => prior.denotes inherited
    | .inr _ => fresh

def covered (language : Language Old Claim) : Set Claim :=
  {claim | ∃ code : language.Code, claim ∈ language.denotes code}

def repair (old : Language Old Claim) (observed : Set Claim) : Language Old Claim :=
  .extend old (observed \ old.covered)

variable (old : Language Old Claim) (observed : Set Claim)

def inherited (code : old.Code) : (old.repair observed).Code :=
  Sum.inl code

def fresh : (old.repair observed).Code :=
  Sum.inr ()

@[simp] theorem denotes_inherited (code : old.Code) :
    (old.repair observed).denotes (old.inherited observed code) = old.denotes code :=
  rfl

@[simp] theorem denotes_fresh :
    (old.repair observed).denotes (old.fresh observed) = observed \ old.covered :=
  rfl

@[simp] theorem covered_initial : (Language.initial : Language Old Claim).covered = ∅ := by
  ext claim
  simp [covered, denotes]

@[simp] theorem covered_extend :
    (Language.extend old observed).covered = old.covered ∪ observed := by
  ext claim
  constructor
  · rintro ⟨code, refused⟩
    rcases code with code | _
    · exact Or.inl ⟨code, refused⟩
    · exact Or.inr refused
  · rintro (⟨code, refused⟩ | refused)
    · exact ⟨Sum.inl code, refused⟩
    · exact ⟨Sum.inr (), refused⟩

@[simp] theorem covered_repair :
    (old.repair observed).covered = old.covered ∪ observed := by
  classical
  rw [repair, covered_extend]
  ext claim
  constructor
  · rintro (earlier | ⟨found, _⟩)
    · exact Or.inl earlier
    · exact Or.inr found
  · rintro (earlier | found)
    · exact Or.inl earlier
    · by_cases earlier : claim ∈ old.covered
      · exact Or.inl earlier
      · exact Or.inr ⟨found, earlier⟩

theorem least_repair_iff (candidate : Set Claim) :
    (old.repair observed).covered ⊆ candidate ↔
      old.covered ⊆ candidate ∧ observed ⊆ candidate := by
  rw [covered_repair, Set.union_subset_iff]

theorem fresh_least_iff (candidate : Set Claim) :
    (old.repair observed).denotes (old.fresh observed) ⊆ candidate ↔
      observed ⊆ old.covered ∪ candidate := by
  classical
  rw [denotes_fresh]
  constructor
  · intro covers claim found
    by_cases already : claim ∈ old.covered
    · exact Or.inl already
    · exact Or.inr (covers ⟨found, already⟩)
  · intro covers claim missing
    exact (covers missing.1).resolve_left missing.2

theorem gap_not_denotable (novel : ¬ observed ⊆ old.covered) :
    ∃ claim ∈ observed, (∀ code : old.Code, claim ∉ old.denotes code) ∧
      claim ∈ (old.repair observed).denotes (old.fresh observed) := by
  obtain ⟨claim, found, missing⟩ := Set.not_subset.mp novel
  exact ⟨claim, found, fun code refused => missing ⟨code, refused⟩, ⟨found, missing⟩⟩

private def defaultCode [Inhabited Old] : (language : Language Old Claim) → language.Code
  | .initial => (default : Old)
  | .extend prior _ => Sum.inl (defaultCode prior)

/-- The coface retraction sends every old expression back to itself.
The additional coordinate is the occurrence's new refusal direction. -/
def capacity [Inhabited Old] :
    RelativeExpressiveCapacity old.Code (old.repair observed).Code Unit where
  oldFace := ⟨old.inherited observed, Sum.elim id (fun _ => defaultCode old), fun _ => rfl⟩
  generator := fun _ => old.fresh observed
  embed := id
  embed_old := fun _ => rfl
  embed_new := fun index => by cases index; rfl
  injective := fun _ _ equal => equal

end Language

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace
