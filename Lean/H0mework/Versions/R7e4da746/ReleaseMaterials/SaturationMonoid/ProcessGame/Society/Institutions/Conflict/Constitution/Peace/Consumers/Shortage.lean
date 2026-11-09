import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Peace.Shortage
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Consumers.NativeShortage

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Peace.Consumers

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Transition.Handoff.Consumers.Continuation (start)
open Civil.Persistence (FirstNativeShortage)
open Civil.Persistence.Consumers (unfundedPeriod the_native_first_shortage_keeps_its_named_unit_and_unadvanced_clock)
open Quantities.Execution (endAt)

noncomputable section

def TheShortageAtSixHasItsOriginalWrite : Prop :=
  ∃ missing : FirstNativeShortage start [unfundedPeriod],
    let consumed := missing.before ++ [missing.input]
    let written := shortageWrite (seed := start) (community := (id : Bool → Bool)) (past := []) missing
    (missing.issue.cell.1, missing.issue.cell.2.1, missing.issue.cell.2.2.1, missing.issue.amount) =
        (false, .necessity, true, 1) ∧
    (endAt start [unfundedPeriod]).raw.clock = 6 ∧
    Quantities.Recorded start consumed ∧ Evolving.Epoch.Current.ClosedAt (endAt start consumed) ∧
    written.next = Reparation.Actual.run start id consumed

theorem the_named_food_shortage_at_six_consumes_the_original_whole_ledger : TheShortageAtSixHasItsOriginalWrite := by
  obtain ⟨missing, _, _, named, clock, _⟩ := the_native_first_shortage_keeps_its_named_unit_and_unadvanced_clock
  have readback := the_named_native_shortage_keeps_its_original_whole_write (seed := start)
    (community := (id : Bool → Bool)) (past := []) missing
  exact ⟨missing, named, clock, readback.2.2.1, readback.2.2.2.1,
    Reparation.Actual.publication_consumes_the_retained_visit start id [] _⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Peace.Consumers
