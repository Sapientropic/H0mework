import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Common.RootConsumer.Semantics
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Activation.QueryStock

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCofinalCommonAction.ConfiguredStock
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace SA
export ActualCofinalSourceAction
 (nativePacket sourceBorn bornStock born_inventory selected paid_prefix_stocks actual_next_packet packetTransport wordTransport)
end SA
namespace RM
export ActualCofinalResidualModelSplice (packetWordTransport packetLanguageWord)
end RM
namespace QS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource.QueryStock (scalar_query_stock)
end QS
variable {Sorts:Type u} {W X:Sorts→Type u} [∀ target,AddCommGroup (W target)] {s:Sorts}
local instance stockGroups (grade:Nat) (target:Sorts) : AddCommGroup (T.Value W grade target) := T.groups W grade target

private abbrev Event (packet:A.AdmissionPacket (W:=W) (X:=X) (s:=s)) :=
 PresentedRelationEventAt (Expr (T.Value W packet.1) X s)
private def packetEvent
 {first second:A.AdmissionPacket (W:=W) (X:=X) (s:=s)} (same:first=second) :
 Event first→Event second := by cases same; exact id
private def languageEvent {Y Z:Sorts→Type u} (same:Y=Z)
 (packet:A.AdmissionPacket (W:=W) (X:=Y) (s:=s)) :
 PresentedRelationEventAt (Expr (T.Value W packet.1) Y s)→Event (SA.packetTransport same packet) := by
 cases same
 exact id

variable (factory:T.Factory W X s) (initial:T.Frame (Value:=W) (Var:=X) (sort:=s))
variable (cfg:T.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s)) (language:cfg.LowVar=X)

def nextEvent (ordinal:Nat)
 (event:PresentedRelationEventAt (Expr (PairValue (T.NativeValue factory initial cfg language ordinal)) X s)) :
 Event (site factory initial cfg language (ordinal+1)) :=
 packetEvent (SA.actual_next_packet factory initial cfg language ordinal).symm
  (languageEvent (site factory initial cfg language ordinal).2.2.2.down
   (SA.sourceBorn factory (site factory initial cfg language ordinal))
   ((site factory initial cfg language ordinal).2.2.2.down.symm ▸ event :
    PresentedRelationEventAt (Expr (PairValue (T.NativeValue factory initial cfg language ordinal))
     (site factory initial cfg language ordinal).2.2.1.LowVar s)))

def nextWord (ordinal:Nat) :
 Formal ℤ (PairValue (T.NativeValue factory initial cfg language ordinal)) X s →ₗ[ℤ]
 T.Words factory initial cfg language (ordinal+1) :=
 (RM.packetWordTransport (SA.actual_next_packet factory initial cfg language ordinal).symm).toLinearMap.comp
  ((RM.packetLanguageWord (site factory initial cfg language ordinal).2.2.2.down
    (SA.sourceBorn factory (site factory initial cfg language ordinal))).toLinearMap.comp
   (SA.wordTransport (site factory initial cfg language ordinal).2.2.2.down.symm).toLinearMap)

private theorem packet_relation
 {first second:A.AdmissionPacket (W:=W) (X:=X) (s:=s)} (same:first=second)
 (word:Formal ℤ (T.Value W first.1) X s) :
 packetEvent same (.relation word)=.relation (RM.packetWordTransport same word) := by cases same; rfl
private theorem language_relation {Y Z:Sorts→Type u} (same:Y=Z)
 (packet:A.AdmissionPacket (W:=W) (X:=Y) (s:=s))
 (word:Formal ℤ (T.Value W packet.1) Y s) :
 languageEvent same packet (.relation word)=.relation (RM.packetLanguageWord same packet word) := by cases same; rfl
private theorem cast_relation {Value:Sorts→Type u} [∀ target,AddCommGroup (Value target)]
 {Y Z:Sorts→Type u} (same:Y=Z) (word:Formal ℤ Value Y s) :
 (same ▸ (.relation word:PresentedRelationEventAt (Expr Value Y s)))=.relation (SA.wordTransport same word) := by
 cases same
 rfl

private theorem packet_members {I:Type u}
 {first second:A.AdmissionPacket (W:=W) (X:=X) (s:=s)} (same:first=second)
 (events:I→Event first) (present:I→Prop)
 (member:∃ stock,first.2.1.1.inventory=some stock ∧∀ index,present index→events index∈stock.trace) :
 ∃ stock,second.2.1.1.inventory=some stock ∧∀ index,present index→packetEvent same (events index)∈stock.trace := by
 cases same
 exact member
private theorem language_members {I:Type u} {Y Z:Sorts→Type u} (same:Y=Z)
 (packet:A.AdmissionPacket (W:=W) (X:=Y) (s:=s))
 (events:I→PresentedRelationEventAt (Expr (T.Value W packet.1) Y s)) (present:I→Prop)
 (member:∃ stock,packet.2.1.1.inventory=some stock ∧∀ index,present index→events index∈stock.trace) :
 ∃ stock,(SA.packetTransport same packet).2.1.1.inventory=some stock ∧
  ∀ index,present index→languageEvent same packet (events index)∈stock.trace := by
 cases same
 exact member

/-- Every actual configured query event enters one original next inventory; relation words retain the same linear transport. -/
theorem source_inventory (ordinal:Nat)
 (stock:RootedAccountedUnfolding (PresentedRelationEventAt
  (Expr (PairValue (T.NativeValue factory initial cfg language ordinal)) X s)))
 (written:(site factory initial cfg language ordinal).2.2.1.nextPairInventory
  (site factory initial cfg language ordinal).2.1.1=some stock) :
 (∃ targetStock,(site factory initial cfg language (ordinal+1)).2.1.1.inventory=some targetStock ∧
  ∀ event∈stock.trace,nextEvent factory initial cfg language ordinal event∈targetStock.trace) ∧
 (∀ word,.relation word∈stock.trace→
  WordInInventory (site factory initial cfg language (ordinal+1))
   (nextWord factory initial cfg language ordinal word)) := by
 have atBorn : ∃ targetStock,
   (SA.sourceBorn factory (site factory initial cfg language ordinal)).2.1.1.inventory=some targetStock ∧
   ∀ event∈stock.trace,((site factory initial cfg language ordinal).2.2.2.down.symm ▸ event :
    PresentedRelationEventAt (Expr (PairValue (T.NativeValue factory initial cfg language ordinal))
     (site factory initial cfg language ordinal).2.2.1.LowVar s))∈targetStock.trace := by
  refine ⟨SA.bornStock factory _,SA.born_inventory factory _,?_⟩
  intro event belongs
  have atScalar:=QS.scalar_query_stock factory (site factory initial cfg language ordinal).1
   (site factory initial cfg language ordinal).2.1 (site factory initial cfg language ordinal).2.2.1
   (site factory initial cfg language ordinal).2.2.2.down stock written event belongs
  apply SourceInventoryExecutionFeed.original_preserved
  change _∈(ActualCofinalSourceAction.T.preserve (SA.selected factory (site factory initial cfg language ordinal)).inventory _).trace
  rw [(SA.paid_prefix_stocks factory (site factory initial cfg language ordinal) _ (Nat.le_refl _)).1]
  exact (SourceHistoryCommon.parallel_left _ _ _).1 _ atScalar
 have traceMember : ∃ targetStock,
   (site factory initial cfg language (ordinal+1)).2.1.1.inventory=some targetStock ∧
   ∀ event∈stock.trace,nextEvent factory initial cfg language ordinal event∈targetStock.trace :=
  packet_members (SA.actual_next_packet factory initial cfg language ordinal).symm _ _
   (language_members (site factory initial cfg language ordinal).2.2.2.down
    (SA.sourceBorn factory (site factory initial cfg language ordinal)) _ _ atBorn)
 refine ⟨traceMember,?_⟩
 intro word belongs
 rcases traceMember with ⟨target,present,member⟩
 refine ⟨target,present,?_⟩
 have relation:=member (.relation word) belongs
 dsimp only [nextEvent] at relation
 rw [cast_relation] at relation
 erw [language_relation (W:=W) (s:=s) (site factory initial cfg language ordinal).2.2.2.down
   (SA.sourceBorn factory (site factory initial cfg language ordinal))
   ((SA.wordTransport (site factory initial cfg language ordinal).2.2.2.down.symm) word)] at relation
 erw [packet_relation (W:=W) (s:=s) (SA.actual_next_packet factory initial cfg language ordinal).symm] at relation
 exact relation

end ActualCofinalCommonAction.ConfiguredStock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
