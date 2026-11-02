import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work.Lookup
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Prefix

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work.Prefix
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {epoch : Epoch} (inventory : Inventory epoch)
  (model : Native.Authority.Bound (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit))
  (domain : List (Continuation.Cursor model.source.code)) (original : Rule model.source.code)
  (past : List (Rule model.source.code)) (reference : Whole.Program model.source.code (horizon domain))
  (tariff : Restoration.Tariff (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit)) (requested : List (List Action))
  (batch : Batch model domain original requested inventory tariff)

abbrev OriginalCandidate := Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate
  (tariff := tariff) (requested := requested) model domain original past reference

def refine (previous : OriginalCandidate model domain original past reference tariff requested) :
    Option (Feed.Prefix.Candidate inventory model domain original past reference tariff requested) :=
  if accepted : Lookup.check batch reference previous.protocol = true then
    some ⟨previous,(Lookup.check_iff batch reference previous.protocol).mp accepted⟩
  else none

/-- Keep the original paid-prefix pool and check the complete cached relation before taking its head. -/
def candidates :=
  (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.candidates
    (tariff := tariff) (requested := requested) model domain original past reference).filterMap
      (refine inventory model domain original past reference tariff requested batch)

theorem candidates_are_the_original_joint_pool :
    candidates inventory model domain original past reference tariff requested batch =
      Feed.Prefix.candidates inventory model domain original past reference tariff requested := by
  unfold candidates Feed.Prefix.candidates
  congr 1
  funext previous
  unfold refine Feed.Prefix.refine
  by_cases kept : Feed.Selection.acceptable inventory model domain original tariff requested reference previous.protocol
  · have checked := (Lookup.check_iff batch reference previous.protocol).mpr kept
    simp only [dif_pos checked,dif_pos kept]
  · have checked : Lookup.check batch reference previous.protocol ≠ true :=
      fun yes => kept ((Lookup.check_iff batch reference previous.protocol).mp yes)
    simp only [dif_neg checked,dif_neg kept]

def compile : Feed.Prefix.Outcome inventory model domain original past reference tariff requested :=
  match found : (candidates inventory model domain original past reference tariff requested batch).head? with
  | some candidate => .selected candidate
  | none => .blocked fun tail =>
      if verified : Selection.Restoration.verify (tariff := tariff) (requested := requested) model domain original reference
          (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.proposal model domain past tail) = true then
        .history (Lookup.rejectionFrom batch reference
          (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.proposal model domain past tail) (by
            intro checked
            obtain ⟨candidate,member,_⟩ := Feed.Prefix.every_jointly_certified_completion_is_generated
              inventory model domain original past reference tariff requested tail verified
              ((Lookup.check_iff batch reference _).mp checked)
            rw [←candidates_are_the_original_joint_pool inventory model domain original past reference tariff requested batch,
              List.head?_eq_none_iff.mp found] at member
            exact List.not_mem_nil member))
      else .original (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.failure
        (tariff := tariff) (requested := requested)
        (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.proposal model domain past tail) verified)

theorem every_selected_program_keeps_the_cached_complete_relation
    (candidate : Feed.Prefix.Candidate inventory model domain original past reference tariff requested) :
    Lookup.check batch reference candidate.protocol = true :=
  (Lookup.check_iff batch reference candidate.protocol).mpr candidate.accepted

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work.Prefix
