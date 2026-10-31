import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.GeneratedLaw.Trajectory
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.ActualBirth

/-! Membership is read from the already generated original history.  The
source round identifies that history exactly; missing one instruction word
does not erase an earlier actor from the needs and maintenance inventory. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.GeneratedLaw

open Source.Program Source.ProgrammeFace

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def members (current : RawCurrent Party Good Technology Instrument) : List Party :=
  ActualBirth.participants input
    (ProgrammeHistory.visitAt input (current.round - input.initial.round))

theorem members_at_original_visit (index : Nat) :
    members input (ProgrammeSource.rawCurrent input (ProgrammeHistory.visitAt input index).current) =
      ActualBirth.participants input (ProgrammeHistory.visitAt input index) := by
  simp only [members, ProgrammeHistory.visit_round, Nat.add_sub_cancel_left]

theorem members_at_every_actual_cut (cut offset : Nat) :
    members input ((programAt input cut).currentAt offset) =
      ActualBirth.participants input (ProgrammeHistory.visitAt input (cut + offset + 1)) := by
  rw [← original_root_generates_every_finite_prefix]
  exact members_at_original_visit input _

theorem original_need_bearer_is_retained (cut offset : Nat) (party : Party)
    (present : party ∈ members input ((programAt input cut).currentAt offset)) :
    party ∈ members input ((programAt input cut).currentAt (offset + 1)) := by
  rw [members_at_every_actual_cut] at present ⊢
  exact ActualBirth.original_participant_is_retained input
    (ProgrammeHistory.visitAt input (cut + offset + 1)) rfl party present

def memberBirth (cut offset : Nat) (party : Party)
    (present : party ∈ members input ((programAt input cut).currentAt offset)) :
    ActualBirth.At input (ProgrammeHistory.visitAt input (cut + offset + 1)) party :=
  ActualBirth.fromHistory input (ProgrammeHistory.visitAt input (cut + offset + 1)) party
    ((members_at_every_actual_cut input cut offset) ▸ present)

theorem local_source_renews_all_original_members (cut : Nat)
    (invariant : RawCurrent Party Good Technology Instrument → Prop)
    (initial : invariant (ProgrammeSource.rawCurrent input
      (ProgrammeHistory.visitAt input (cut + 1)).current))
    (preserved : ∀ current, invariant current → invariant ((programAt input cut).tick current))
    (available : ∀ current, invariant current →
      Exit.LocalRenewal.attempt (programAt input cut) (members input) current ≠ none) :
    ∀ start, Exit.LocalRenewal.PaidTail (programAt input cut) (members input) start :=
  Exit.LocalRenewal.local_source_generates_paid_continuation
    (programAt input cut) (members input) invariant initial preserved available

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.GeneratedLaw
