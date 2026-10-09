import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Finite.Indexed
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Forecast.Source
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Operator

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
namespace Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.NativeWriter
namespace L
export Lower.SourceFamily.Foresight.Paid.Ledger (run run_contains writeEvent eventWord)
end L
namespace Paid
export Lower.SourceFamily.Foresight.Paid
 (writtenAt paidTrace complete_fee source_action_value sourceEnv expression)
end Paid
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat) (seed:Lower.SourceFamily.Seed W X s n)
variable (frame:M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s))
variable (origin:Lower.SourceFamily.Foresight.Installed.OccurrenceIndex n frame)
variable (point:GeneratedRelationResidualCoordinateAt (Indexed.face binding n seed frame origin))
variable (path:List PUnit.{u+1}) (k:Nat)
abbrev SourcePacket:=type_of% (nativeCalculation binding n seed frame origin point path k)
variable (packet:SourcePacket binding n seed frame origin point path k)
variable (same:packet=nativeCalculation binding n seed frame origin point path k)

def preimage:=actedWord binding n path point.relation

theorem native_preimage:
 nativeWord binding n seed frame path k point.relation=
 AlgebraicDependent.advance (F.action binding (state n seed frame) s) 0 k
  (preimage binding n seed frame origin point path):=rfl

include same in
theorem actual_packet_word:packet.1.1.expression=
 Coefficients.expression
  (AlgebraicDependent.advance (F.action binding (state n seed frame) s) 0 k
   (preimage binding n seed frame origin point path)):=by
 subst packet
 rfl

theorem source_action_commutes:
 nativeWord binding n seed frame path (k+1) point.relation=
 F.action binding (state n seed frame) s (0+k)
  (nativeWord binding n seed frame path k point.relation):=rfl

theorem actual_native_action:
 F.read binding (state n seed frame) s (0+(k+1))
  (nativeWord binding n seed frame path (k+1) point.relation)=
 updateInventory (R:=ℤ) (Lower.SourceFamily.Foresight.decoder binding (state n seed frame) (0+k))
  (Lower.SourceFamily.Foresight.increment binding (state n seed frame) (0+k))
  (nativeWord binding n seed frame path k point.relation):=
 Lower.SourceFamily.Foresight.actual_word binding (state n seed frame) s (0+k)
  (nativeWord binding n seed frame path k point.relation)

theorem full_native_source_step:
 Lower.SourceFamily.Foresight.next binding (state n seed frame) s (0+k)
  (Lower.SourceFamily.Foresight.sourceMap binding (state n seed frame) s (0+k)
   (nativeWord binding n seed frame path k point.relation))=
 Lower.SourceFamily.Foresight.sourceMap binding (state n seed frame) s (0+(k+1))
  (nativeWord binding n seed frame path (k+1) point.relation):=
 (Lower.SourceFamily.Foresight.next_source binding (state n seed frame) s (0+k)
  (nativeWord binding n seed frame path k point.relation)).trans
 (congrArg (Lower.SourceFamily.Foresight.sourceMap binding (state n seed frame) s (0+(k+1)))
  (source_action_commutes binding n seed frame origin point path k).symm)

theorem full_preimage_source_step:
 Lower.SourceFamily.Foresight.next binding (state n seed frame) s 0
  (Lower.SourceFamily.Foresight.sourceMap binding (state n seed frame) s 0
   (preimage binding n seed frame origin point path))=
 Lower.SourceFamily.Foresight.sourceMap binding (state n seed frame) s 1
  (liftMap (preimage binding n seed frame origin point path)):=
 Lower.SourceFamily.Foresight.next_source binding (state n seed frame) s 0
  (preimage binding n seed frame origin point path)

include same in
theorem lookup_fee:packet.1.2.1.2.length=
 Coefficients.cost (nativeWord binding n seed frame path k point.relation):=by
 subst packet
 exact InstalledQuery.exact_fee _ _ _ _

structure BackedWord (packet:SourcePacket binding n seed frame origin point path k) where
 word:Word (W:=W) (X:=X) (s:=s) n
 source_expression:packet.1.1.expression=Coefficients.expression
  (AlgebraicDependent.advance (F.action binding (state n seed frame) s) 0 k word)

include same in
def backedPreimage:BackedWord binding n seed frame origin point path k packet where
 word:=preimage binding n seed frame origin point path
 source_expression:=actual_packet_word binding n seed frame origin point path k packet same

omit path k packet same in
def sourceTree (word:Word (W:=W) (X:=X) (s:=s) n):=
 RootedAccountedUnfolding.zero
 (.generator (Coefficients.expression word):PresentedRelationEventAt (Expr (PairValue (Lower.Value W n)) X s))

omit path k packet same in
def written (word:Word (W:=W) (X:=X) (s:=s) n):=
 L.run (L.writeEvent binding n ⟨frame,seed⟩) (sourceTree n word)

omit path k packet same in
def completed (word:Word (W:=W) (X:=X) (s:=s) n):=SourceHistoryCommon.seed
 ((sourceTree n word).map T.liftEvent) (written binding n seed frame word)

omit binding seed frame origin point path k packet same in
def writerWord (word:Word (W:=W) (X:=X) (s:=s) n):=
 L.eventWord n (.generator (Coefficients.expression word))

omit path k packet same in
theorem writer_fee (word:Word (W:=W) (X:=X) (s:=s) n):
 (Paid.paidTrace binding n ⟨frame,seed⟩ s (writerWord n word)).length=
 remaining (Paid.expression (W:=W) (X:=X) n s (writerWord n word)):=Paid.complete_fee _ _ _ _ _

omit path k packet same in
theorem literal_writer_effect (word:Word (W:=W) (X:=X) (s:=s) n):
 (Lower.SourceFamily.Foresight.Paid.result binding n ⟨frame,seed⟩ s (writerWord n word)).2.2.1=
 updateInventory (R:=ℤ) (s:=s)
  (Lower.SourceFamily.Foresight.Update.decoder binding n seed frame
   (Lower.SourceFamily.Foresight.Paid.sourceScalar binding n ⟨frame,seed⟩)
   (Lower.SourceFamily.Foresight.Paid.sourcePair binding n ⟨frame,seed⟩))
  (Lower.SourceFamily.Foresight.Update.increment binding n seed frame
   (Lower.SourceFamily.Foresight.Paid.sourceScalar binding n ⟨frame,seed⟩)
   (Lower.SourceFamily.Foresight.Paid.sourcePair binding n ⟨frame,seed⟩)) (writerWord n word):=
 Paid.source_action_value _ _ _ _ _

omit k packet same in
theorem full_literal_source_step:
 Lower.SourceFamily.Foresight.next binding (state n seed frame) s 0
  (Lower.SourceFamily.Foresight.sourceMap binding (state n seed frame) s 0
   (writerWord n (preimage binding n seed frame origin point path)))=
 Lower.SourceFamily.Foresight.sourceMap binding (state n seed frame) s 1
  (liftMap (preimage binding n seed frame origin point path)):=
 (congrArg (Lower.SourceFamily.Foresight.next binding (state n seed frame) s 0)
  (Lower.SourceFamily.Foresight.Contextual.Forecast.Rendering.rendered_source
   binding (state n seed frame) s 0 (preimage binding n seed frame origin point path))).trans
 (full_preimage_source_step binding n seed frame origin point path)

omit path k packet same in
theorem generator_in_completed (word:Word (W:=W) (X:=X) (s:=s) n):
 T.liftEvent (.generator (Coefficients.expression word):
  PresentedRelationEventAt (Expr (PairValue (Lower.Value W n)) X s))∈
 (completed binding n seed frame word).trace:=by
 apply (SourceHistoryCommon.parallel_left _ _ _).1
 rw [T.mapped_trace]
 exact List.mem_map_of_mem List.mem_cons_self

omit path k packet same in
theorem actual_paid_in_completed (word:Word (W:=W) (X:=X) (s:=s) n) (event)
 (present:event∈(L.writeEvent binding n ⟨frame,seed⟩ (.generator (Coefficients.expression word))).trace):
 event∈(completed binding n seed frame word).trace:=by
 apply (SourceHistoryCommon.parallel_right _ _ _).1
 exact L.run_contains (L.writeEvent binding n ⟨frame,seed⟩) (sourceTree n word)
  (.generator (Coefficients.expression word)) List.mem_cons_self event present

end Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.NativeWriter
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
