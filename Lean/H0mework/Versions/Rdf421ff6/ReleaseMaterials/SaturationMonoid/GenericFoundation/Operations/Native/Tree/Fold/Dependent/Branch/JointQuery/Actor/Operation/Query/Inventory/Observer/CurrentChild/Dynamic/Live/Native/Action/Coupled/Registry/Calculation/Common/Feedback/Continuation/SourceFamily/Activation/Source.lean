import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed
import H0mework.Versions.Rdf421ff6.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Factory
import H0mework.Versions.Rdf421ff6.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Admission
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Consumer
import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace SF
export Lower.SourceFamily (Factory Packet Seed cfg)
end SF
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (next nextBorn actualOccurrence)
end S
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (programme oldPaid nativeAt)
end WB
namespace T
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock (preserve preserves_length seed_length liftEvent)
end T
namespace IP
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme
 (writtenSeed)
end IP
namespace I
export SourceGeneratedInquiryReceiptAction.Inventory (programme)
end I
namespace B
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Bootstrap (initial)
end B
namespace SA
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockAdmission
 (presentation generatedAction successor_valid targetPresentation target_erasure target_full_root)
end SA
namespace ST
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockTarget
 (presentation successor_valid compiles_paid compiles_settled)
end ST
namespace SO
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockObservation (current root current_observation)
end SO
variable {Sorts : Type u} {Value Var : Sorts → Type u}
 [∀ target, AddCommGroup (Value target)] {sort : Sorts}

def generatedStock (frame : M.Frame (Value := Value) (Var := Var) (sort := sort)) :
 RootedAccountedUnfolding (PresentedRelationEventAt (Expr Value Var sort)) :=
 IP.writtenSeed (RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator frame.registered.input.expression))
  (A.epoch frame) (S.actualOccurrence frame)
def generatedPairStock (frame : M.Frame (Value := Value) (Var := Var) (sort := sort)) :
 RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue Value) Var sort)) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.completeWrittenInventory
  (RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator frame.registered.input.expression))
  (A.epoch frame) (S.actualOccurrence frame)


/-- The complete same-occurrence query write retains the original pair inventory. -/
theorem generatedPairStock_preserves_original
 (frame : M.Frame (Value := Value) (Var := Var) (sort := sort)) :
 ∀ event ∈ (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.pairInventory
  (RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator frame.registered.input.expression))
  (A.epoch frame) (S.actualOccurrence frame)).trace,
 event ∈ (generatedPairStock frame).trace :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.complete_written_preserves
  (RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator frame.registered.input.expression))
  (A.epoch frame) (S.actualOccurrence frame)

private theorem inventory_blind
 (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
 (programme : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
 (scalar : type_of% programme.nextInventory) (pair : type_of% programme.nextPairInventory) :
 (S.nextBorn frame { programme with nextInventory := scalar, nextPairInventory := pair }).activeEnvironment =
 (S.nextBorn frame programme).activeEnvironment := by
 let changed := { programme with nextInventory := scalar, nextPairInventory := pair }
 have left := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame changed).toAuthoritativeRoot
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum frame changed).reader
  (S.actualOccurrence frame)
 have right := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame programme).toAuthoritativeRoot
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum frame programme).reader
  (S.actualOccurrence frame)
 have value : (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultFace frame changed).rootRead.2.2.1 =
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultFace frame programme).rootRead.2.2.1 :=
  left.trans right.symm
 cases actualAt : (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum frame programme).nextEnvironmentReadAt with
 | some read =>
  simp only [S.nextBorn,
   RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.activeEnvironment,
   RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.environmentAt,
   RootGeneratedDebtActivationJointSource.Successor.Inquiry.Source.environmentAt,
   SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum,actualAt]
  exact congrArg (read (S.actualOccurrence frame)) value
 | none =>
  cases actualRead : (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum frame programme).nextEnvironmentRead with
  | some read =>
   simp only [S.nextBorn,
    RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.activeEnvironment,
    RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.environmentAt,
    RootGeneratedDebtActivationJointSource.Successor.Inquiry.Source.environmentAt,
   SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum,actualAt,actualRead]
   exact congrArg read value
  | none =>
   simp only [S.nextBorn,
    RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.activeEnvironment,
    RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.environmentAt,
    RootGeneratedDebtActivationJointSource.Successor.Inquiry.Source.environmentAt,
   SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum,actualAt,actualRead]
   rfl

/-- The original source datum, before either output-stock callback is installed. -/
def stockSource (base : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort)) :
 A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort) :=
 { I.programme base with
   datum := fun frame => { (I.programme base).datum frame with
     calculationReader := some ((base.datum frame).calculationReader.getD (base.datum frame).reader) } }

def stockScalar
 (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
 (base : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort)) :
 RootedAccountedUnfolding (PresentedRelationEventAt (Expr Value Var sort)) :=
 T.preserve frame.inventory (T.preserve (base.nextInventory frame) (generatedStock frame))

/-- Read the actual decoder without consulting the new output-stock callbacks. -/
def stockDecodedEnvironment
 (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
 (base : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort)) : Env Value Var :=
 (S.nextBorn frame (stockSource base)).activeEnvironment

def stockCfg (base : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort)) :
 A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort) :=
 { stockSource base with
   nextInventory := fun frame => some (SourceInventoryExecutionFeed.written
     (stockDecodedEnvironment frame base) (stockScalar frame base))
   nextPairInventory := fun frame => some (T.preserve frame.pairInventory
     (T.preserve (base.nextPairInventory frame) (generatedPairStock frame))) }

theorem stock_born_environment
 (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
 (base : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort)) :
 (S.nextBorn frame (stockCfg base)).activeEnvironment = stockDecodedEnvironment frame base :=
 inventory_blind frame (stockSource base) _ _


theorem stock_action_reader (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
 (base : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current := current)) :
 SourceGeneratedInquiryReceiptAction.actionReader frame (stockCfg base) supplied =
 SourceGeneratedInquiryReceiptAction.actionReader frame base supplied := rfl

theorem stock_query_reader (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
 (base : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current := current)) :
 ((stockCfg base).datum frame).reader supplied = ((I.programme base).datum frame).reader supplied := rfl

theorem birth_stock_grows (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
 (base : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort)) :
 Lower.Stock.size frame < Lower.Stock.size (S.nextBorn frame (stockCfg base)) := by
 have growth : Lower.Stock.size frame < (stockScalar frame base).trace.length := by
  unfold stockScalar Lower.Stock.size
  cases present : frame.inventory with
  | none => exact Lower.Stock.trace_nonempty _
  | some carried => exact T.preserves_length _ _
 change Lower.Stock.size frame < (SourceInventoryExecutionFeed.written
  (stockDecodedEnvironment frame base) (stockScalar frame base)).trace.length
 apply lt_of_lt_of_le growth
 rw [SourceInventoryExecutionFeed.written_trace,List.length_append]
 exact Nat.le_add_right _ _

variable (W : Sorts → Type u) [∀ target, AddCommGroup (W target)]
local instance levelGroups (n : Nat) (target : Sorts) : AddCommGroup (Lower.Value W n target) := Lower.groups W n target
variable {W} {X : Sorts → Type u} {s : Sorts}
variable (factory : SF.Factory W X s) (n : Nat) (data : SF.Packet (W := W) (X := X) (s := s) n)
variable (sourceCfg : A.Programme (PhysicalValue := Lower.Value W n) (PhysicalVar := X) (sort := s))
variable (language : sourceCfg.LowVar = X)

-- Both configured source inventories enter the admission's next-grade seed.
def scalar := T.preserve (language.symm ▸ sourceCfg.nextPairInventory data.1)
 (T.preserve (language.symm ▸ (sourceCfg.nextInventory data.1).map (fun stock => stock.map T.liftEvent))
  (T.preserve (language.symm ▸ factory.extraScalar n data.2 data.1)
   (Lower.Stock.scalar data.1 sourceCfg language)))
def pair := T.preserve (language.symm ▸ factory.extraPair n data.2 data.1)
 (Lower.Stock.pair data.1 sourceCfg language)
def receiver := B.initial data.1 sourceCfg (scalar factory n data sourceCfg language)
 (pair factory n data sourceCfg language)
def nextSeed := SourceHistoryCommon.seed (scalar factory n data sourceCfg language)
 (RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator
  (receiver factory n data sourceCfg language).registered.input.expression))
def template := SF.cfg (language.symm ▸ factory : SF.Factory W sourceCfg.LowVar s) (n+1)
 (nextSeed factory n data sourceCfg language)

def write (value : PairValue (Lower.Value W n) s) :
 Env (PairValue (Lower.Value W n)) sourceCfg.LowVar := by
 classical
 exact fun target name => if equal : target = s then equal.symm ▸ value
  else (receiver factory n data sourceCfg language).activeEnvironment target name

def nextBase := { template factory n data sourceCfg language with
 datum := fun frame => { (template factory n data sourceCfg language).datum frame with
  nextEnvironmentReadAt := ((WB.programme data.1 sourceCfg (write factory n data sourceCfg language)).datum frame).nextEnvironmentReadAt } }
def nextCfg := stockCfg (nextBase factory n data sourceCfg language)

theorem next_action_reader
 (currentFrame : M.Frame (Value := PairValue (Lower.Value W n)) (Var := sourceCfg.LowVar) (sort := s))
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current currentFrame.registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence currentFrame (current := current)) :
 SourceGeneratedInquiryReceiptAction.actionReader currentFrame (nextCfg factory n data sourceCfg language) supplied =
 SourceGeneratedInquiryReceiptAction.actionReader currentFrame (template factory n data sourceCfg language) supplied := rfl

theorem receiver_stock_grows : Lower.Stock.size data.1 <
 Lower.Stock.size (receiver factory n data sourceCfg language) := by
 have base := Lower.Stock.scalar_growth data.1 sourceCfg language
 change Lower.Stock.size data.1 < (scalar factory n data sourceCfg language).trace.length
 have preserved {α : Type u} (prior : Option (RootedAccountedUnfolding α))
  (stock : RootedAccountedUnfolding α) : stock.trace.length ≤ (T.preserve prior stock).trace.length := by
  cases prior with
  | none => exact Nat.le_refl _
  | some carried =>
   change _ ≤ (SourceHistoryCommon.seed carried stock).trace.length
   rw [T.seed_length]
   omega
 exact lt_of_lt_of_le base (le_trans (preserved _ _)
  (le_trans (preserved _ _) (preserved _ _)))

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
