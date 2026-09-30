import Mathlib.Data.List.Basic

/-!
# Trace-constrained narratives

A narrative is a readout of an actual occurrence.  Its claims are admissible
only when every claimed atom is witnessed by that occurrence's existing
source trace.  The construction adds no archive, occurrence, or witness
registry: support is a relation on the supplied source trace.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace History

universe uOccurrence uNarrative uAtom

/-- A narrative readout whose emitted claims are all witnessed by the actual
source occurrence trace.  All carriers and functions are unrestricted. -/
structure TraceConstrainedNarrativeReadout
    (Occurrence : Type uOccurrence)
    (Narrative : Type uNarrative)
    (Atom : Type uAtom) where
  trace : Occurrence → List Atom
  narrative : Occurrence → Narrative
  claims : Narrative → List Atom
  emitted_claim_supported : ∀ occurrence atom,
    atom ∈ claims (narrative occurrence) → atom ∈ trace occurrence

variable {Occurrence : Type uOccurrence}
variable {Narrative : Type uNarrative}
variable {Atom : Type uAtom}

namespace TraceConstrainedNarrativeReadout

variable (R : TraceConstrainedNarrativeReadout Occurrence Narrative Atom)

/-- Trace admissibility of any proposed narrative at one actual occurrence. -/
def SupportsAt (occurrence : Occurrence) (story : Narrative) : Prop :=
  ∀ atom, atom ∈ R.claims story → atom ∈ R.trace occurrence

/-- Actual occurrences over one narrative readout.  This is a subtype of the
existing occurrence carrier, not a second archive or occurrence registry. -/
def NarrativeFibreAt (story : Narrative) : Type uOccurrence :=
  { occurrence : Occurrence // R.narrative occurrence = story }

theorem emitted_supports (occurrence : Occurrence) :
    R.SupportsAt occurrence (R.narrative occurrence) :=
  R.emitted_claim_supported occurrence

theorem fibre_member_supports
    {story : Narrative}
    (member : R.NarrativeFibreAt story) :
    R.SupportsAt member.1 story := by
  intro atom claimed
  apply R.emitted_claim_supported member.1 atom
  simpa [member.2] using claimed

/-- Two different actual occurrences with one narrative image make that
trace-constrained narrative fibre genuinely non-singleton. -/
theorem narrativeFibre_not_subsingleton
    (left right : Occurrence)
    (occurrence_ne : left ≠ right)
    (sameNarrative : R.narrative left = R.narrative right) :
    ¬ Subsingleton (R.NarrativeFibreAt (R.narrative left)) := by
  intro subsingleton
  let leftMember : R.NarrativeFibreAt (R.narrative left) :=
    ⟨left, rfl⟩
  let rightMember : R.NarrativeFibreAt (R.narrative left) :=
    ⟨right, sameNarrative.symm⟩
  apply occurrence_ne
  exact congrArg Subtype.val (subsingleton.elim leftMember rightMember)

/-- A narrative containing an unwitnessed claim is inadmissible at that
occurrence.  Hence trace constraint does not collapse into radical narrative
arbitrariness. -/
theorem not_supports_of_claim_absent
    (occurrence : Occurrence)
    (story : Narrative)
    (atom : Atom)
    (claimed : atom ∈ R.claims story)
    (absent : atom ∉ R.trace occurrence) :
    ¬ R.SupportsAt occurrence story := by
  intro supports
  exact absent (supports atom claimed)

end TraceConstrainedNarrativeReadout

end History
end Society
end ProcessGame
end SaturationMonoid
