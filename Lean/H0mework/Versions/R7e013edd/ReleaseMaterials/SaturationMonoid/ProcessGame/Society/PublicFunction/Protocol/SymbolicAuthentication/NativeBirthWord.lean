import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedInventoryBudget

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeBirthWord
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.ProgrammeFace Mandate.Challenge
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument} {scope : Mandate.Scope}
  {Index : Type} (bound : ProgrammeFamily base scope Index) (inputs : Index)

theorem actual_open_births_are_paid_by_original_trace_items (ordinal : Nat) :
    CompletedInventory.openBorn bound inputs ordinal ≤
      (Registered.traceItems (bound.inputAt inputs)
        (ProgrammeHistory.visitAt (bound.inputAt inputs) ordinal).current).length := by
  have live := List.length_filter_le (CompletedInventory.live bound inputs (ordinal + 1))
    (claimsAt bound inputs ordinal)
  have read := List.length_filterMap_le (read bound inputs) (positionsAt bound inputs ordinal)
  have positions : (positionsAt bound inputs ordinal).length =
      (Registered.traceItems (bound.inputAt inputs)
        (ProgrammeHistory.visitAt (bound.inputAt inputs) ordinal).current).length := by
    simp only [positionsAt, List.length_map, List.length_finRange]
  exact live.trans (read.trans_eq positions)

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (cursor : Cursor model.source.code) (stages : JointResponse.Stages model)

theorem every_actual_open_birth_is_funded_by_its_submitted_request_word
    (row : StageTrace.Record (code := model.source.code)) (inside : row ∈ StageTrace.records cursor stages) :
    CompletedInventory.openBorn (IncidentChallenge.family model cursor stages)
      (IncidentChallenge.sourceIndex model cursor stages) (EventStep.boundary row.cursor) ≤ row.submitted.length := by
  have budget := actual_open_births_are_paid_by_original_trace_items
    (IncidentChallenge.family model cursor stages) (IncidentChallenge.sourceIndex model cursor stages)
    (EventStep.boundary row.cursor)
  change CompletedInventory.openBorn _ _ _ ≤ (Registered.traceItems (EventHistory.execute cursor stages).source.input
    (ProgrammeHistory.visitAt (EventHistory.execute cursor stages).source.input (EventStep.boundary row.cursor)).current).length at budget
  rw [IncidentChallenge.actual_trace_items model cursor stages row inside] at budget
  have exactWord := congrArg List.length (StageTrace.audit_retains_every_request_and_its_actual_validity row).1
  simp only [StageTrace.audit, List.length_map] at exactWord
  exact budget.trans_eq exactWord

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeBirthWord
