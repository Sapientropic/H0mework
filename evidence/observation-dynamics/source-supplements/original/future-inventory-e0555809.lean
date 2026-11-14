import SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Read
import SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Outgoing.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Future.Written
namespace O
export SourceOperationInquiry.Context.Outgoing (deltaWord deltaTerm pairTerm deltaPairTrace pairStock pairValue pairEnvironment pair_old_effect pair_fee pair_boundary)
end O
namespace J
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual (priorPairInventory pairInventory liftedInventory)
namespace Joint
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint (history disposition queryReader queryResult)
end Joint
end J
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence query)
end Q
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
variable (frame : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable (cfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (sameVar : cfg.LowVar=X)

theorem carried_pair (prior : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue W) X s)))
 (present : frame.pairInventory=some prior) (event : PresentedRelationEventAt (Expr (PairValue W) X s)) (belongs : event ∈ prior.trace) :
 (sameVar.symm ▸ (T.liftEvent (W:=PairValue W) (X:=X) (s:=s) event)) ∈ (Lower.Stock.pair frame cfg sameVar).trace := by
 have mapped : T.liftEvent (W:=PairValue W) (X:=X) (s:=s) event ∈
  (prior.map (T.liftEvent (W:=PairValue W) (X:=X) (s:=s))).trace := by
  rw [T.mapped_trace]
  exact List.mem_map_of_mem belongs
 have carried := (Lower.Stock.cast_mem (W:=PairValue W) sameVar.symm _ _).mpr mapped
 unfold Lower.Stock.pair T.pairPrior
 rw [present]
 change (sameVar.symm ▸ T.liftEvent event) ∈
  (T.preserve (sameVar.symm ▸ some (prior.map T.liftEvent)) (C.lowPairWritten frame cfg)).trace
 rw [Lower.Stock.cast_some (W:=PairValue W)]
 exact (SourceHistoryCommon.parallel_left _ _ _).1 _ carried

theorem outgoing_written (event : PresentedRelationEventAt (Expr (PairValue (PairValue W)) cfg.LowVar s))
 (present : event ∈ (O.pairStock frame cfg).trace) : event ∈ (Lower.Stock.pair frame cfg sameVar).trace := by
 have actual := SourceGeneratedInquiryReceiptAction.Configured.pair_event_preserved frame cfg event present
 unfold Lower.Stock.pair T.preserve
 cases sameVar.symm ▸ T.pairPrior frame with
 | none => exact actual
 | some prior => exact (SourceHistoryCommon.parallel_right _ _ _).1 _ actual

theorem delta_generator_written : PresentedRelationEventAt.generator (O.pairTerm frame cfg) ∈
 (Lower.Stock.pair frame cfg sameVar).trace :=
 outgoing_written frame cfg sameVar _ (RootedAccountedUnfolding.root_mem_trace (O.pairStock frame cfg))

theorem delta_relations_written (word : Formal ℤ (PairValue (PairValue W)) cfg.LowVar s)
 (paid : word ∈ SourceOperationPaidRelations.words (O.deltaPairTrace frame cfg)) :
 PresentedRelationEventAt.relation word ∈ (Lower.Stock.pair frame cfg sameVar).trace := by
 apply outgoing_written frame cfg sameVar
 change PresentedRelationEventAt.relation word ∈ PresentedRelationEventAt.generator (O.pairTerm frame cfg)::
  RootedAccountedUnfolding.traceBranches (SourceOperationPaidRelations.events (O.deltaPairTrace frame cfg))
 apply List.mem_cons_of_mem
 rw [SourceOperationPaidRelations.events_trace]
 exact List.mem_map_of_mem paid

theorem delta_pair_source : O.pairValue frame cfg=
 ((O.deltaTerm frame cfg).eval (Q.query frame cfg).raw.environment,
  (O.deltaTerm frame cfg).effect (Q.query frame cfg).raw.environment
   (SourceGeneratedInquiryReceiptAction.afterEnvironment frame cfg-(Q.query frame cfg).raw.environment)) := O.pair_old_effect frame cfg

theorem delta_pair_cost : type_of% (O.pair_fee frame cfg) := O.pair_fee frame cfg

def receiver := Lower.Stock.receiver frame cfg sameVar
def nativeSeed := Lower.Stock.seed frame cfg sameVar
def supplied := Q.actualOccurrence (receiver frame cfg sameVar)
def jointInventory := J.pairInventory (nativeSeed frame cfg sameVar)
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (receiver frame cfg sameVar)) (supplied frame cfg sameVar)
def jointDisposition := J.Joint.disposition (nativeSeed frame cfg sameVar)
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (receiver frame cfg sameVar)) (supplied frame cfg sameVar)

theorem actual_joint_consumes (event : PresentedRelationEventAt (Expr (PairValue (PairValue W)) cfg.LowVar s))
 (written : event ∈ (Lower.Stock.pair frame cfg sameVar).trace) : event ∈ (jointInventory frame cfg sameVar).trace := by
 apply (SourceHistoryCommon.parallel_left _ _ _).1
 unfold J.priorPairInventory
 change event ∈ (SourceHistoryCommon.seed (Lower.Stock.pair frame cfg sameVar)
  (J.liftedInventory (nativeSeed frame cfg sameVar)
   (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (receiver frame cfg sameVar)) (supplied frame cfg sameVar))).trace
 exact (SourceHistoryCommon.parallel_left _ _ _).1 _ written

theorem delta_joint_generator : PresentedRelationEventAt.generator (O.pairTerm frame cfg) ∈ (jointInventory frame cfg sameVar).trace :=
 actual_joint_consumes frame cfg sameVar _ (delta_generator_written frame cfg sameVar)

theorem delta_joint_relations (word : Formal ℤ (PairValue (PairValue W)) cfg.LowVar s)
 (paid : word ∈ SourceOperationPaidRelations.words (O.deltaPairTrace frame cfg)) :
 PresentedRelationEventAt.relation word ∈ (jointInventory frame cfg sameVar).trace :=
 actual_joint_consumes frame cfg sameVar _ (delta_relations_written frame cfg sameVar word paid)

-- The same inventory feeds the actual four-branch Joint query inside R, without a chosen branch.
theorem actual_native_reader : (Q.query (receiver frame cfg sameVar) (Lower.Stock.programme frame cfg sameVar)).raw.expression=
 Expr.add (J.Joint.queryReader (nativeSeed frame cfg sameVar)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (receiver frame cfg sameVar)) (supplied frame cfg sameVar)).expression
 (Expr.linear (-AddMonoidHom.id _) (J.Joint.queryResult (nativeSeed frame cfg sameVar)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (receiver frame cfg sameVar)) (supplied frame cfg sameVar)).2.1.1) := rfl

namespace Cast
variable {Y Z : S → Type u}
theorem pair_inventory (same : Y=Z) (data : Lower.Transport.Data (W:=W) (s:=s) Y) :
 (same ▸ data : Lower.Transport.Data (W:=W) (s:=s) Z).1.pairInventory=same ▸ data.1.pairInventory := by cases same; rfl
end Cast

local instance inventoryGroup (n : Nat) (t : S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t
variable (initial : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable (firstCfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (language : firstCfg.LowVar=X)

theorem actual_pair_inventory (n : Nat) :
 (Lower.frameAt initial firstCfg language (n+1)).pairInventory=
 Lower.languageAt initial firstCfg language n ▸ (some (Lower.pairAt initial firstCfg language n)) := by
 cases n with
 | zero => exact Cast.pair_inventory language ⟨Lower.Stock.receiver initial firstCfg language,Lower.Stock.seed initial firstCfg language⟩
 | succ n => rfl

def actualJointInventory (n : Nat) := J.pairInventory
 (Lower.tailData initial firstCfg language (n+1)).2
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (Lower.frameAt initial firstCfg language (n+2)))
 (Q.actualOccurrence (Lower.frameAt initial firstCfg language (n+2)))

theorem next_joint_inventory (n : Nat) : jointInventory
 (Lower.frameAt initial firstCfg language (n+1)) (Lower.cfgAt initial firstCfg language (n+1))
 (Lower.languageAt initial firstCfg language (n+1))=actualJointInventory initial firstCfg language n := rfl

theorem actual_next_reader (n : Nat) :
 (Q.query (Lower.frameAt initial firstCfg language (n+2)) (Lower.cfgAt initial firstCfg language (n+2))).raw.expression=
 Expr.add (J.Joint.queryReader (Lower.tailData initial firstCfg language (n+1)).2
  (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (Lower.frameAt initial firstCfg language (n+2)))
  (Q.actualOccurrence (Lower.frameAt initial firstCfg language (n+2)))).expression
 (Expr.linear (-AddMonoidHom.id _) (J.Joint.queryResult (Lower.tailData initial firstCfg language (n+1)).2
  (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (Lower.frameAt initial firstCfg language (n+2)))
  (Q.actualOccurrence (Lower.frameAt initial firstCfg language (n+2)))).2.1.1) := rfl

def deltaWord (n : Nat) : Future.Read.Word (W:=W) (X:=X) (s:=s) n :=
 O.deltaWord (Lower.frameAt initial firstCfg language (n+1)) (Lower.cfgAt initial firstCfg language (n+1))

theorem actual_delta_old_effect (n : Nat) : type_of% (Future.Read.actual_old_effect initial firstCfg language n
 (deltaWord initial firstCfg language n)) := Future.Read.actual_old_effect _ _ _ _ _

theorem actual_delta_whole_residual (n : Nat) : type_of% (Future.Read.actual_whole_residual initial firstCfg language n
 (deltaWord initial firstCfg language n)) := Future.Read.actual_whole_residual _ _ _ _ _

theorem actual_delta_generator (n : Nat) : type_of% (delta_joint_generator
 (Lower.frameAt initial firstCfg language (n+1)) (Lower.cfgAt initial firstCfg language (n+1)) (Lower.languageAt initial firstCfg language (n+1))) :=
 delta_joint_generator _ _ _

theorem actual_delta_relations (n : Nat) (word : Formal ℤ (PairValue (PairValue (Lower.Value W (n+1)))) X s)
 (paid : word ∈ SourceOperationPaidRelations.words (O.deltaPairTrace
  (Lower.frameAt initial firstCfg language (n+1)) (Lower.cfgAt initial firstCfg language (n+1)))) : type_of% (delta_joint_relations
 (Lower.frameAt initial firstCfg language (n+1)) (Lower.cfgAt initial firstCfg language (n+1)) (Lower.languageAt initial firstCfg language (n+1)) word paid) :=
 delta_joint_relations (W:=Lower.Value W (n+1)) (X:=X) (s:=s)
   (Lower.frameAt initial firstCfg language (n+1)) (Lower.cfgAt initial firstCfg language (n+1))
   (Lower.languageAt initial firstCfg language (n+1)) word paid
end Future.Written
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
