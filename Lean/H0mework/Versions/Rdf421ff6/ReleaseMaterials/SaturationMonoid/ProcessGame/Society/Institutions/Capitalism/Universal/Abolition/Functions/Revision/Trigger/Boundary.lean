import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Context
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control.Endpoint

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Trigger

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (context : Context (input := input) (review := review) depth count prefixLimit renewalLimit sourceDepth sourceCount)

abbrev Boundary := Abolition.Root.ReviewSource.Control.BoundaryAt input depth count prefixLimit renewalLimit context.germ.snapshot

def IsCurrentPaidBoundary : Boundary context → Prop
  | .materialPaid _ _ _ _ candidate _ _ => context.germ.snapshot = candidate.tailTarget
  | _ => False

/-- Prefix provenance is already in the source boundary. Only a finite
length comparison is needed; later occurrences cannot reuse the old cut. -/
def currentPaidBoundaryFlag : Boundary context → Bool
  | .materialPaid _ _ _ _ candidate _ _ => decide (candidate.tailTarget.past.length = context.germ.snapshot.past.length)
  | _ => false

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
private theorem cursor_eq (left right : Physical.Cursor Party Good Port Technology Instrument)
    (past : left.past = right.past) (incoming : left.incoming = right.incoming) : left = right := by
  cases left
  cases right
  cases past
  cases incoming
  rfl

theorem the_finite_source_clock_test_recovers_the_exact_paid_current
    (boundary : Boundary context) (fresh : currentPaidBoundaryFlag context boundary = true) :
    IsCurrentPaidBoundary context boundary := by
  cases boundary with
  | unavailable => cases fresh
  | stopped => cases fresh
  | materialPaid located original prepared generated candidate occurred source =>
      have length : candidate.tailTarget.past.length = context.germ.snapshot.past.length := of_decide_eq_true fresh
      have snapshot := Abolition.Root.Registered.Macro.Raw.input_uses_the_literal_current_account
        context.native context.data context.reader context.germ
      have incoming : context.germ.snapshot.incoming = .advance := congrArg Physical.Cursor.incoming snapshot.2.1
      exact cursor_eq context.germ.snapshot candidate.tailTarget (occurred.eq_of_length length).symm incoming

theorem an_exact_paid_current_passes_the_finite_source_clock_test
    (boundary : Boundary context) (fresh : IsCurrentPaidBoundary context boundary) :
    currentPaidBoundaryFlag context boundary = true := by
  cases boundary with
  | unavailable => exact fresh.elim
  | stopped => exact fresh.elim
  | materialPaid located original prepared generated candidate occurred source =>
      apply decide_eq_true
      exact (congrArg (fun cursor => cursor.past.length) fresh).symm

#print axioms the_finite_source_clock_test_recovers_the_exact_paid_current
#print axioms an_exact_paid_current_passes_the_finite_source_clock_test

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Trigger
