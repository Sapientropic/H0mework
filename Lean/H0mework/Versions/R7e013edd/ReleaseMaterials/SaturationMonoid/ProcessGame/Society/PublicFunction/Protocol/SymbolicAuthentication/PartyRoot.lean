import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PartyCursor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PartyRoot
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction
open Repayment.Recovery (Good)
open WholePartyLift PartyCode PartyCursor
variable (source : OldMachine) (outside : Good → ℚ) (same : source.code.law = oldLaw)
  (original : source.side = .original)

include original in
theorem observed_report (here : OldCurrent) :
    (((machine source outside same).input.observedEmission?).get (by rfl)).generate (current here outside) =
      .original (current here outside) ((source.body here).map request) := by
  change ProgrammeSource.ProgrammeReport.original (current here outside) ((machine source outside same).body (current here outside)) = _
  rw [PartyCursor.body source outside same original]

include original in
theorem next (here : ProgrammeSource.Current OldCurrent) :
    ProgrammeSource.next (machine source outside same).input (WholePartySource.visit outside here) =
      WholePartySource.visit outside (ProgrammeSource.next source.input here) := by
  cases here with
  | bootstrap =>
      change ProgrammeSource.Current.running (newLaw.next (current source.code.initial outside) ([].map request)) _ = _
      rw [WholePartyExecution.next]
      simp only [ProgrammeSource.next,WholePartySource.visit,Machine.input,same,List.map_cons,List.map_nil]
      rfl
  | running here past =>
      change ProgrammeSource.Current.running
        (newLaw.next (current here outside) ((machine source outside same).body (current here outside)))
        ((past.map fun before => current before outside) ++ [current here outside]) =
        ProgrammeSource.Current.running (current (source.code.law.next here (source.body here)) outside)
          ((past ++ [here]).map fun before => current before outside)
      rw [PartyCursor.body source outside same original,WholePartyExecution.next,← same,List.map_append,List.map_singleton]

include original in
theorem every_root_visit (ordinal : Nat) :
    (ProgrammeHistory.visitAt (machine source outside same).input ordinal).current =
      WholePartySource.visit outside (ProgrammeHistory.visitAt source.input ordinal).current := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
      change ProgrammeSource.next (machine source outside same).input _ =
        WholePartySource.visit outside (ProgrammeSource.next source.input _)
      rw [ih,next source outside same original]

theorem raw_current (here : ProgrammeSource.Current OldCurrent) :
    ProgrammeSource.rawCurrent (machine source outside same).input (WholePartySource.visit outside here) =
      current (ProgrammeSource.rawCurrent source.input here) outside := by cases here <;> rfl

include original in
theorem raw_event (here : ProgrammeSource.Current OldCurrent) :
    ProgrammeSource.rawEvent (machine source outside same).input (WholePartySource.visit outside here) =
      (ProgrammeSource.rawEvent source.input here).map request := by
  cases here with
  | bootstrap => rfl
  | running here past => exact PartyCursor.body source outside same original here

include original in
theorem all_actual_words_items_and_next (ordinal : Nat) :
    let oldVisit := (ProgrammeHistory.visitAt source.input ordinal).current
    let newVisit := (ProgrammeHistory.visitAt (machine source outside same).input ordinal).current
    ProgrammeSource.rawEvent (machine source outside same).input newVisit =
        (ProgrammeSource.rawEvent source.input oldVisit).map request ∧
      newLaw.rawItems (ProgrammeSource.rawCurrent (machine source outside same).input newVisit)
        (ProgrammeSource.rawEvent (machine source outside same).input newVisit) =
        (oldLaw.rawItems (ProgrammeSource.rawCurrent source.input oldVisit) (ProgrammeSource.rawEvent source.input oldVisit)).map
          (WholePartyExecution.item outside) ∧
      newLaw.next (ProgrammeSource.rawCurrent (machine source outside same).input newVisit)
        (ProgrammeSource.rawEvent (machine source outside same).input newVisit) =
        current (oldLaw.next (ProgrammeSource.rawCurrent source.input oldVisit) (ProgrammeSource.rawEvent source.input oldVisit)) outside := by
  dsimp only
  rw [every_root_visit source outside same original,raw_event source outside same original,raw_current]
  exact ⟨rfl,congrArg ExecutionResult.items (WholePartyExecution.execute _ outside 0 _),WholePartyExecution.next _ outside _⟩

abbrev native (ordinal : Nat) := ProgrammeHistory.execution_face_shares_whole_ledger_and_next
  (machine source outside same).input ordinal
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PartyRoot
