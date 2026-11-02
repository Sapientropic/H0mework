import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Forecast.Bank.Payment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.CatalogueSource
variable {A : Type} {input : Input A}
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSourceConsumer.case001 (made : Execution input) : made.rows = input.counts.flatMap (fun count => (wordRows input.menu input.depth).map (List.replicate count input.work++·)) := made.rows_exact
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSourceConsumer.case002 (made : Execution input) : made.units = required input.pendingLength made.rows := made.units_exact
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSourceConsumer.case003 (made : Execution input) : made.work.flatMap Event.rows = made.rows := made.emitted_rows
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSourceConsumer.case004 (made : Execution input) : 0 < made.units := made.units_positive
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSourceConsumer.case005 (a b : Execution input) : a = b := a.unique b
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSourceConsumer.case006 (session : Session input) : session.rank+session.work.length = (CatalogueSource.initial input).rank input := session.conservation
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSourceConsumer.case007 (session : Session input) : session.completed.isSome = true ↔ session.move = none := session.completed_iff_stopped
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSourceConsumer.case008 (before after : Session input) (event : Event A) (actual : before.move = some (event,after)) : after.work = before.work++[event] := Session.move_appends actual
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSourceConsumer.case009 (before after : Session input) (event : Event A) (actual : before.move = some (event,after)) : after.rank+1 = before.rank := Session.move_decreases actual
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSourceConsumer.case010 (session : Session input) (made : Execution input) (done : session.completed = some made) : made.work = session.work := Session.completed_work done
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.CatalogueSource
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {old : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {oldDepth : Nat} {word : List (Action old)}
  (cursor : Recovery.Cursor old oldDepth word) (actor : P) (original : List (Action old))
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSourceConsumer.case011 (made : CatalogueSource.Execution (CatalogueSource.source cursor actor original)) : made.rows = Search.repairs cursor.model cursor.before actor original := CatalogueSource.source_rows cursor actor original made
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSourceConsumer.case012 (made : CatalogueSource.Execution (CatalogueSource.source cursor actor original)) : made.units = comparisonUnits original made.rows := CatalogueSource.source_units cursor actor original made
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSourceConsumer.case013 (position : Nat) (made : Stage cursor position) : CatalogueEvidence made.result made.endpoint made.search := made.catalogue
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSourceConsumer.case014 (position : Nat) (made : Stage cursor position) : made.endpoint = made.result.finish := made.exact
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSourceConsumer.case015 (position : Nat) (made : Stage cursor position) : made = stage cursor position := made.eq_default
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSourceConsumer.case016 (position : Quoted.Fees (Action old)) (made : Quoted.Stage cursor position) : Quoted.CatalogueEvidence made.result made.endpoint made.search := made.catalogue
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSourceConsumer.case017 (position : Quoted.Fees (Action old)) (made : Quoted.Stage cursor position) : made.endpoint = made.result.finish := made.exact
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.CrossFeeCatalogueSourceConsumer.case018 (position : Quoted.Fees (Action old)) (made : Quoted.Stage cursor position) : made = Quoted.stage cursor position := made.eq_default
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering
