import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control.Registration
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Current

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)

/-- The location is an existing raw-input occurrence. Invalid fee syntax
still has a location: the later decoder must report it, not skip the code. -/
structure RegistrationAt (event : Physical.Cursor Party Good Port Technology Instrument) where
  private mk ::
  code : Code Party Good Port Technology Instrument
  original : event.incoming = .review code
  accepted : (Compile.compile input depth count prefixLimit renewalLimit
    (Physical.stateAt input depth count prefixLimit renewalLimit event.past) event.incoming).isAccepted = true

def registrationAt (event : Physical.Cursor Party Good Port Technology Instrument) :
    Option (RegistrationAt input depth count prefixLimit renewalLimit event) :=
  match original : event.incoming with
  | .review code =>
      if accepted : (Compile.compile input depth count prefixLimit renewalLimit
          (Physical.stateAt input depth count prefixLimit renewalLimit event.past) event.incoming).isAccepted = true then
        some ⟨code, original, accepted⟩
      else none
  | _ => none

structure Located where
  private mk ::
  event : Physical.Cursor Party Good Port Technology Instrument
  registration : RegistrationAt input depth count prefixLimit renewalLimit event

def firstRegistration (before : Physical.Cursor Party Good Port Technology Instrument) :
    List (Compile.RawInput Party Good Port Technology Instrument) →
      Option (Located input depth count prefixLimit renewalLimit)
  | [] => none
  | raw :: rest =>
      let event := Physical.receive before raw
      match registrationAt input depth count prefixLimit renewalLimit event with
      | some registered => some ⟨event, registered⟩
      | none => firstRegistration (Physical.next event) rest

/-- Incoming proposals are excluded. Only the cursor's already consumed
past can choose the original registration, and the earliest one stays fixed. -/
def recovered (current : Physical.Cursor Party Good Port Technology Instrument) :=
  firstRegistration input depth count prefixLimit renewalLimit Physical.initial current.past

theorem first_registration_survives_every_later_input
    (before : Physical.Cursor Party Good Port Technology Instrument)
    (past later : List (Compile.RawInput Party Good Port Technology Instrument))
    (located : Located input depth count prefixLimit renewalLimit)
    (original : firstRegistration input depth count prefixLimit renewalLimit before past = some located) :
    firstRegistration input depth count prefixLimit renewalLimit before (past ++ later) = some located := by
  induction past generalizing before with
  | nil => cases original
  | cons raw rest ih =>
      cases observed : registrationAt input depth count prefixLimit renewalLimit (Physical.receive before raw) with
      | some registered =>
          simpa only [List.cons_append, firstRegistration, observed] using original
      | none =>
          have tail : firstRegistration input depth count prefixLimit renewalLimit
              (Physical.next (Physical.receive before raw)) rest = some located := by
            simpa only [firstRegistration, observed] using original
          simpa only [List.cons_append, firstRegistration, observed] using
            ih (Physical.next (Physical.receive before raw)) tail

theorem registration_is_located_in_the_original_prefix
    (before : Physical.Cursor Party Good Port Technology Instrument)
    (past : List (Compile.RawInput Party Good Port Technology Instrument))
    (located : Located input depth count prefixLimit renewalLimit)
    (original : firstRegistration input depth count prefixLimit renewalLimit before past = some located) :
    ∃ remaining, before.past ++ past = located.event.past ++ [located.event.incoming] ++ remaining := by
  induction past generalizing before with
  | nil => cases original
  | cons raw rest ih =>
      cases observed : registrationAt input depth count prefixLimit renewalLimit (Physical.receive before raw) with
      | some registered =>
          have same : (⟨Physical.receive before raw, registered⟩ : Located input depth count prefixLimit renewalLimit) = located := by
            simpa only [firstRegistration, observed, Option.some.injEq] using original
          subst located
          exact ⟨rest, by simp only [Physical.receive, List.append_assoc, List.singleton_append]⟩
      | none =>
          have tail : firstRegistration input depth count prefixLimit renewalLimit
              (Physical.next (Physical.receive before raw)) rest = some located := by
            simpa only [firstRegistration, observed] using original
          obtain ⟨remaining, exactPast⟩ := ih (Physical.next (Physical.receive before raw)) tail
          refine ⟨remaining, ?_⟩
          simpa only [Physical.next, Physical.receive, List.append_assoc, List.singleton_append] using exactPast

theorem recovery_uses_a_real_consumed_registration
    (current : Physical.Cursor Party Good Port Technology Instrument)
    (located : Located input depth count prefixLimit renewalLimit)
    (original : recovered input depth count prefixLimit renewalLimit current = some located) :
    ∃ remaining, current.past = located.event.past ++ [.review located.registration.code] ++ remaining := by
  obtain ⟨remaining, exactPast⟩ := registration_is_located_in_the_original_prefix input depth count
    prefixLimit renewalLimit Physical.initial current.past located original
  refine ⟨remaining, ?_⟩
  simpa only [Physical.initial, List.nil_append, located.registration.original] using exactPast

theorem receiving_does_not_create_a_registration
    (current : Physical.Cursor Party Good Port Technology Instrument)
    (proposal : Compile.RawInput Party Good Port Technology Instrument) :
    recovered input depth count prefixLimit renewalLimit (Physical.receive current proposal) =
      recovered input depth count prefixLimit renewalLimit current := rfl

theorem later_registered_code_cannot_replace_the_original_epoch
    (current : Physical.Cursor Party Good Port Technology Instrument)
    (located : Located input depth count prefixLimit renewalLimit)
    (original : recovered input depth count prefixLimit renewalLimit current = some located)
    (proposal : Compile.RawInput Party Good Port Technology Instrument) :
    recovered input depth count prefixLimit renewalLimit (Physical.next (Physical.receive current proposal)) = some located :=
  first_registration_survives_every_later_input input depth count prefixLimit renewalLimit
    Physical.initial current.past [proposal] located original

theorem a_fee_opcode_does_not_mint_review_authority
    (current : Physical.Cursor Party Good Port Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    registrationAt input depth count prefixLimit renewalLimit (Physical.receive current (.primitive request)) = none := rfl

theorem ordinary_repair_code_is_not_a_review_registration
    (current : Physical.Cursor Party Good Port Technology Instrument)
    (submission : Actual.Submission Party Good Port Technology Instrument) :
    registrationAt input depth count prefixLimit renewalLimit (Physical.receive current (.code submission)) = none := rfl

namespace Located
variable (located : Located input depth count prefixLimit renewalLimit)

def epoch := Physical.next located.event

theorem epoch_is_after_the_original_registration :
    (located.epoch input depth count prefixLimit renewalLimit).past =
      located.event.past ++ [.review located.registration.code] := by
  simp only [epoch, Physical.next, located.registration.original]

theorem epoch_keeps_the_complete_original_state :
    Physical.stateAt input depth count prefixLimit renewalLimit (located.epoch input depth count prefixLimit renewalLimit).past =
      Physical.stateAt input depth count prefixLimit renewalLimit located.event.past := by
  dsimp only [epoch]
  rw [Physical.consumed_input_generates_its_own_after, located.registration.original]
  exact registration_preserves_the_complete_state input depth count prefixLimit renewalLimit _ located.registration.code

end Located

#print axioms recovery_uses_a_real_consumed_registration
#print axioms later_registered_code_cannot_replace_the_original_epoch
#print axioms Located.epoch_keeps_the_complete_original_state

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control
