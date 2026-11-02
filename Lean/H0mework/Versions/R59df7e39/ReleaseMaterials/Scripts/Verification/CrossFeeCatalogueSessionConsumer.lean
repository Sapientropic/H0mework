import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Forecast.Bank.Payment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.CatalogueSource
variable {A : Type} {input : Input A}
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case001 (made : Execution input) : made.rows = input.counts.flatMap (fun count => (wordRows input.menu input.depth).map (List.replicate count input.work++·)) := made.rows_exact
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case002 (made : Execution input) : made.units = required input.pendingLength made.rows := made.units_exact
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case003 (made : Execution input) : made.work.flatMap Event.rows = made.rows := made.emitted_rows
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case004 (made : Execution input) : 0 < made.units := made.units_positive
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case005 (a b : Execution input) : a = b := a.unique b
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case006 (session : Session input) : session.rank+session.work.length = (CatalogueSource.initial input).rank input := session.conservation
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case007 (session : Session input) : session.completed.isSome = true ↔ session.move = none := session.completed_iff_stopped
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case008 (before after : Session input) (event : Event A) (actual : before.move = some (event,after)) : after.work = before.work++[event] := Session.move_appends actual
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case009 (before after : Session input) (event : Event A) (actual : before.move = some (event,after)) : after.rank+1 = before.rank := Session.move_decreases actual
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case010 (session : Session input) (made : Execution input) (done : session.completed = some made) : made.work = session.work := Session.completed_work done
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.CatalogueSource
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {old : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {oldDepth : Nat} {word : List (Action old)}
  (cursor : Recovery.Cursor old oldDepth word) (actor : P) (original : List (Action old))
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case011 (made : CatalogueSource.Execution (CatalogueSource.source cursor actor original)) : made.rows = Search.repairs cursor.model cursor.before actor original := CatalogueSource.source_rows cursor actor original made
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case012 (made : CatalogueSource.Execution (CatalogueSource.source cursor actor original)) : made.units = comparisonUnits original made.rows := CatalogueSource.source_units cursor actor original made
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case013 (position : Nat) (made : Stage cursor position) : CatalogueEvidence made.result made.endpoint made.search := made.catalogue
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case014 (position : Nat) (made : Stage cursor position) : made.endpoint = made.result.finish := made.exact
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case015 (position : Nat) (made : Stage cursor position) : made = stage cursor position := made.eq_default
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case016 (position : Quoted.Fees (Action old)) (made : Quoted.Stage cursor position) : Quoted.CatalogueEvidence made.result made.endpoint made.search := made.catalogue
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case017 (position : Quoted.Fees (Action old)) (made : Quoted.Stage cursor position) : made.endpoint = made.result.finish := made.exact
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case018 (position : Quoted.Fees (Action old)) (made : Quoted.Stage cursor position) : made = Quoted.stage cursor position := made.eq_default
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.NativeProgram
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {old : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {R : Type} {depth : Nat} {code : Code (old := old) R depth}
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case019 (a b : Execution code) : a = b := a.unique b
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case020 (session : Session code) : History (.ready code) session.current session.current.work := session.history
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case021 (session : Session code) : session.rank+session.work.length = (execute code).work.length := session.conservation
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case022 (session : Session code) : session.work.length ≤ (execute code).work.length := session.covered
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case023 (session : Session code) : session.completed.isSome = true ↔ session.move = none := session.completed_iff_stopped
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case024 (session : Session code) : session.move = none ↔ session.rank = 0 := session.stopped_iff_zero
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case025 (a b : Session code) (event : Event old) (actual : a.move = some (event,b)) : b.work = a.work++[event] := Session.move_appends actual
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case026 (a b : Session code) (event : Event old) (actual : a.move = some (event,b)) : b.rank+1 = a.rank := Session.move_decreases actual
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case027 (session : Session code) (made : Execution code) (done : session.completed = some made) : made.work = session.work := Session.completed_work done
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case028 : (Session.initial code).rank = (execute code).work.length := Session.initial_rank
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case029 {input : CatalogueSource.Input (Action old)} (next : CatalogueSource.Execution input → Code (old := old) R depth)
    (session : CatalogueSource.Session input) : (Cursor.cataloguing (next := next) session).completed = none := rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case030 {input : CatalogueSource.Input (Action old)} (next : CatalogueSource.Execution input → Code (old := old) R depth)
    (session after : CatalogueSource.Session input) (event : CatalogueSource.Event (Action old))
    (pending : session.completed = none) (actual : session.move = some (event,after)) :
    (Cursor.cataloguing (next := next) session).move = some (.catalogue event,.cataloguing after) := by
  simp only [Cursor.move,pending,actual]
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case031 (input : CatalogueSource.Input (Action old)) :
    (execute (.catalogue input (fun made => .done made.units) : Code (old := old) Nat 1)).value = (CatalogueSource.execute input).units := by
  simp only [execute,Execution.value]
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case032 (input : CatalogueSource.Input (Action old)) :
    (execute (.catalogue input (fun made => .done made.units) : Code (old := old) Nat 1)).work =
    (CatalogueSource.execute input).work.map Event.catalogue++[.finish] := by
  simp only [execute,Execution.work]
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.NativeProgram

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.StageProgram
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {old : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {oldDepth : Nat} {word : List (Action old)}
  {R : Type} {code : Code (old := old) (oldDepth := oldDepth) (word := word) R}
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case033 (first second : Execution code) : first = second := first.unique second
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case034 (made : Execution code) : made.value = (execute code).value := congrArg Execution.value (made.unique _)
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case035 (made : Execution code) : made.work = (execute code).work := congrArg Execution.work (made.unique _)
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case036 (made : Execution code) : made.invoice.work = (NativeProgram.execute code).work := congrArg NativeProgram.Execution.work (made.invoice.unique _)
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case037 (session : Session code) : History (initial code) session.current session.work := session.history
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case038 (session : Session code) : session.rank+session.work.length = (execute code).work.length := session.conservation
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case039 (session : Session code) : session.work.length ≤ (execute code).work.length := session.covered
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case040 (session : Session code) : session.completed.isSome = true ↔ session.move = none := session.completed_iff_stopped
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case041 (session : Session code) : session.move = none ↔ session.rank = 0 := session.stopped_iff_zero
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case042 (first last : Session code) (event : Event (old := old)) (actual : first.move = some (event,last)) : last.rank+1 = first.rank := Session.move_decreases actual
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case043 (first last : Session code) (event : Event (old := old)) (actual : first.move = some (event,last)) : last.work = first.work++[event] := Session.move_appends actual
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case044 (session : Session code) (made : Execution code) (actual : session.completed = some made) : made.work = session.work := Session.completed_work actual
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case045 : (Session.initial code).rank = (execute code).work.length := Session.initial_rank
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case046 : (Session.initial code).work = [] := rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case047 (before after : Cursor code) (event : Event (old := old)) (actual : before.move = some (event,after)) : after.rank+1 = before.rank := Cursor.move_decreases actual
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case048 (before after : Cursor code) (event : Event (old := old)) (actual : before.move = some (event,after)) : after.work = before.work++[event] := Cursor.move_appends actual
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case049 (current : Cursor code) : current.completed.isSome = true ↔ current.move = none := current.completed_iff_stopped
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case050 (current : Cursor code) : current.move = none ↔ current.rank = 0 := current.stopped_iff_zero
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case051 (first : NativeProgram.Execution code) (tail : Tail R) (same : first.value = .search tail)
    (session : SearchPaid.Session tail.stage tail.catalogue) (pending : session.completed = none) :
    (Cursor.searching first tail same session).completed = none := by simp only [Cursor.completed,pending]
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case052 (first : NativeProgram.Execution code) (tail : Tail R) (same : first.value = .search tail)
    (before after : SearchPaid.Session tail.stage tail.catalogue) (event : SearchPaid.Event old) (actual : before.move = some (event,after)) :
    (Cursor.searching first tail same before).move = some (NativeProgram.Event.search event,.searching first tail same after) := by simp only [Cursor.move,actual]
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.StageProgram

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Forecast.Bank.Payment.Verification.Incremental
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {position ordinal : Nat}
  {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
  {reading : Reading prepared budget outerOverride position}
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case053 (decision : Decision reading ordinal) : decision.workAt 2 = decision.bankWork := rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case054 (decision : Decision reading ordinal) (index : Index prepared)
    (a b : Fin (decision.workAt 2)) (different : a ≠ b) : decision.phaseSlot index 2 a ≠ decision.phaseSlot index 2 b := by
  intro same
  have values := congrArg Fin.val same
  change decision.prefixAt 2+a.val = decision.prefixAt 2+b.val at values
  exact different (Fin.ext (Nat.add_left_cancel values))
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case055 (decision : Decision reading ordinal) (index : Index prepared) (other : Fin 6) (different : (2 : Fin 6) ≠ other)
    (a : Fin (decision.workAt 2)) (b : Fin (decision.workAt other)) : decision.phaseSlot index 2 a ≠ decision.phaseSlot index other b :=
  decision.phases_disjoint index 2 other different a b
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case056 (cache : Computation.Collection.Completed reading.opened.audit) (cached : reading.run.endpoint.completed = some cache)
    (harvest : Harvesting reading cache) (pending : harvest.run.endpoint.completed = none) :
    (Decision.bank cache cached harvest pending : Decision reading ordinal).bankWork = harvest.run.work.length := rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case057 (cache : Computation.Collection.Completed reading.opened.audit) (cached : reading.run.endpoint.completed = some cache)
    (harvest : Harvesting reading cache) (pending : harvest.run.endpoint.completed = none) (index : Index prepared)
    (event : Fin harvest.run.work.length) :
    Fin (((reading.opened.funding.resultAt index).invoice (reading.opened.paid index)).bill.units) :=
  (Decision.bank cache cached harvest pending : Decision reading ordinal).phaseSlot index 2 event
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSessionConsumer.case058 (decision : Decision reading ordinal) : decision.spent+decision.unused = budget.units := decision.conservation
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Forecast.Bank.Payment.Verification.Incremental
