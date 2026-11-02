import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross.GrantInventory
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed.Release.Actual

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross
open Institutions.Capitalism.Universal.Source.Program ResponsibilityLifecycle
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  (bound : BoundSource base scope)
  {inputs : List (RawEvent Party Good Port (State Party Technology) Instrument)}

abbrev GrantResident.releaseBefore (record : GrantResident bound inputs)
    (word : RawEvent Party Good Port (State Party Technology) Instrument) :=
  Lifecycle.Observed.through (base := base) (scope := scope)
    (currentAt := grantCurrent bound (nextInputs inputs word))
    (wordAt := grantWord bound (nextInputs inputs word))
    (birth := record.birth.val) (grant := transportGrant bound inputs word record.birth record.grant) inputs.length

abbrev GrantResident.ReleaseIndex (word : RawEvent Party Good Port (State Party Technology) Instrument) :=
  Fin (Lifecycle.Observed.Release.items (base := base) (scope := scope)
    (currentAt := grantCurrent bound (nextInputs inputs word))
    (wordAt := grantWord bound (nextInputs inputs word)) (inputs.length+1)).length

abbrev GrantResident.ReleaseReceipt (record : GrantResident bound inputs)
    (word : RawEvent Party Good Port (State Party Technology) Instrument) :=
  Sigma fun index : GrantResident.ReleaseIndex bound (inputs := inputs) word =>
    Lifecycle.Observed.Release.Receipt (record.releaseBefore bound word) (inputs.length+1) index

def GrantResident.releaseReceipts (record : GrantResident bound inputs)
    (word : RawEvent Party Good Port (State Party Technology) Instrument) :
    List (record.ReleaseReceipt bound word) :=
  (List.finRange _).filterMap fun index =>
    (Lifecycle.Observed.Release.read (record.releaseBefore bound word) (inputs.length+1) index).map (Sigma.mk index)

theorem GrantResident.release_before_is_the_same_original_cut (record : GrantResident bound inputs)
    (word : RawEvent Party Good Port (State Party Technology) Instrument) :
    (record.releaseBefore bound word).state = record.history.state := by
  rw [record.history_exact]
  exact transportGrant_entire_cut_state bound inputs word record.birth record.grant

theorem GrantResident.release_before_keeps_the_same_original_obligation (record : GrantResident bound inputs)
    (word : RawEvent Party Good Port (State Party Technology) Instrument) :
    (record.releaseBefore bound word).obligation = record.history.obligation :=
  Lifecycle.Observed.History.obligation_eq_of_state_eq _ _ (record.release_before_is_the_same_original_cut bound word)

theorem GrantResident.release_visit_is_the_actual_advance (record : GrantResident bound inputs)
    (word : RawEvent Party Good Port (State Party Technology) Instrument) :
    (record.releaseBefore bound word).visit (inputs.length+1) = (record.advance bound word).history := by
  simpa only [GrantResident.releaseBefore,GrantResident.advance,nextInputs,List.length_append,List.length_singleton] using
    (Lifecycle.Observed.through_succ (base := base) (scope := scope)
      (currentAt := grantCurrent bound (nextInputs inputs word))
      (wordAt := grantWord bound (nextInputs inputs word))
      (birth := record.birth.val) (grant := transportGrant bound inputs word record.birth record.grant) inputs.length)

theorem GrantResident.every_read_release_is_retained (record : GrantResident bound inputs)
    (word : RawEvent Party Good Port (State Party Technology) Instrument)
    (index : GrantResident.ReleaseIndex bound (inputs := inputs) word)
    (receipt : Lifecycle.Observed.Release.Receipt (record.releaseBefore bound word) (inputs.length+1) index)
    (found : Lifecycle.Observed.Release.read (record.releaseBefore bound word) (inputs.length+1) index = some receipt) :
    Sigma.mk index receipt ∈ record.releaseReceipts bound word :=
  List.mem_filterMap.mpr ⟨index,List.mem_finRange _,by rw [found]; rfl⟩

theorem GrantResident.release_is_in_the_original_advance (record : GrantResident bound inputs)
    (word : RawEvent Party Good Port (State Party Technology) Instrument)
    (receipt : record.ReleaseReceipt bound word) :
    ((Lifecycle.Observed.Release.before (record.releaseBefore bound word) (inputs.length+1) receipt.1).edge receipt.2.event).lifecycleEvent ∈
      (record.advance bound word).history.state.history ∧
    ((Lifecycle.Observed.Release.before (record.releaseBefore bound word) (inputs.length+1) receipt.1).edge receipt.2.event).lifecycleEvent.kind = .bearerRelease ∧
    (record.advance bound word).history.state.LiveAt 0 := by
  refine ⟨?_,receipt.2.native_kind, (record.advance bound word).history.responsibility_remains_live⟩
  rw [← record.release_visit_is_the_actual_advance bound word]
  exact receipt.2.is_recorded_in_the_actual_visit

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross
