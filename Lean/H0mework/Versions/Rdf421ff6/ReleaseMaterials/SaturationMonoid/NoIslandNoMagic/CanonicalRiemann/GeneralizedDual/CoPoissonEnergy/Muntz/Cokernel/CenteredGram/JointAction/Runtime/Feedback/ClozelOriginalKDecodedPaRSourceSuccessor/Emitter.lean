import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDecodedPaRSourceSuccessor.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRSourceSuccessor
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
namespace SF
export OriginalKWholePaNativeRankSourceUpdate.SourceFamily (Factory Packet)
end SF
namespace L
export OriginalKWholePaNativeRankSourceUpdate.SourceL (Value groups)
end L
namespace A
export OriginalKWholePaNativeRankSourceUpdate.SourceA (Programme)
end A
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource (write template stockCfg receiver nextSeed)
end AS
namespace CF
export OriginalKWholePaNativeRankSourceUpdate.SourceCF (codeAt)
end CF
namespace WB
export OriginalKWholePaNativeRankSourceUpdate.SourceWB (programme oldPaid nativeAt)
end WB
namespace AI
export OriginalKFullSourceRAction.AI (withActualInput)
end AI
namespace Stock
export OriginalKWholePaNativeRankSourceUpdate.ActorStock (preserve)
end Stock
namespace S
export OriginalKWholePaNativeRankSourceUpdate.ActorShared (actualOccurrence)
end S
local instance emitterSuccessorGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
variable (depth ordinal : Nat) (h H N : ℝ)

/-- The original variable R reader is installed before this new native admission. -/
def sourceRFactory (factory : SF.Factory (PairValue C.Value) C.Var ()) :=
 AI.withActualInput (FullR.sourceCode observation nontrivial half) factory

variable (factory : SF.Factory (PairValue C.Value) C.Var ()) (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var)

abbrev SourceFrame := RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PairValue (L.Value (PairValue C.Value) grade)) (Var:=sourceCfg.LowVar) (sort:=())

/-- The source actor executes on the original source-valued write in its actual graded carrier. -/
def sourceActorWrite (value : PairValue (L.Value (PairValue C.Value) grade) ()) :
 Env (PairValue (L.Value (PairValue C.Value) grade)) sourceCfg.LowVar := by
 let code : Expr (PairValue (L.Value (PairValue C.Value) grade)) sourceCfg.LowVar () :=
  language.symm ▸ CF.codeAt (sourceActorCode observation nontrivial half depth ordinal h H N) grade
 exact fun target _ => by
  cases target
  exact code.eval (AS.write factory grade data sourceCfg language value)

def sourceActorGradedRaw (frame : SourceFrame grade sourceCfg) :
 RootGeneratedDebtActivationJointSource.OwnerFree.Raw
  (Value:=PairValue (L.Value (PairValue C.Value) grade)) (Var:=sourceCfg.LowVar) (sort:=()) :=
 ⟨AS.write factory grade data sourceCfg language
   (WB.oldPaid data.1 sourceCfg+WB.nativeAt sourceCfg frame (S.actualOccurrence frame)),
  language.symm ▸ CF.codeAt (sourceActorCode observation nontrivial half depth ordinal h H N) grade⟩

def sourceActorGradedTrace (frame : SourceFrame grade sourceCfg) :
 Trace (sourceActorGradedRaw observation nontrivial half depth ordinal h H N factory grade data sourceCfg language frame).environment
  (sourceActorGradedRaw observation nontrivial half depth ordinal h H N factory grade data sourceCfg language frame).expression
  (.const ((sourceActorGradedRaw observation nontrivial half depth ordinal h H N factory grade data sourceCfg language frame).expression.eval
   (sourceActorGradedRaw observation nontrivial half depth ordinal h H N factory grade data sourceCfg language frame).environment)) := execution _ _

/-- The source R expression is executed before emission on the actual supplied source occurrence. -/
def sourceRBeforeRaw (frame : SourceFrame grade sourceCfg) :=
 SourceGeneratedInquiryReceiptAction.actionReader frame (AS.template factory grade data sourceCfg language) (S.actualOccurrence frame)

def sourceRBeforeTrace (frame : SourceFrame grade sourceCfg) :
 Trace (sourceRBeforeRaw factory grade data sourceCfg language frame).environment
  (sourceRBeforeRaw factory grade data sourceCfg language frame).expression
  (.const ((sourceRBeforeRaw factory grade data sourceCfg language frame).expression.eval
   (sourceRBeforeRaw factory grade data sourceCfg language frame).environment)) := execution _ _

def sourceEmitterBase :=
 { AS.template factory grade data sourceCfg language with
   datum := fun frame =>
    { (AS.template factory grade data sourceCfg language).datum frame with
      nextEnvironmentReadAt := ((WB.programme data.1 sourceCfg
       (sourceActorWrite observation nontrivial half depth ordinal h H N factory grade data sourceCfg language)).datum frame).nextEnvironmentReadAt },
   nextInventory := fun frame => some (Stock.preserve
    ((AS.template factory grade data sourceCfg language).nextInventory frame)
    (SourceOperationPaidRelations.exposure
     (sourceActorGradedTrace observation nontrivial half depth ordinal h H N factory grade data sourceCfg language frame))),
   nextPairInventory := fun frame => some (Stock.preserve
    ((AS.template factory grade data sourceCfg language).nextPairInventory frame)
    (SourceOperationPaidRelations.exposure (sourceRBeforeTrace factory grade data sourceCfg language frame))) }

theorem source_emitter_actual_decoder (frame : SourceFrame grade sourceCfg) :
 ((sourceEmitterBase observation nontrivial half depth ordinal h H N factory grade data sourceCfg language).datum frame).nextEnvironmentReadAt =
 some (fun {_current} supplied _paid =>
  sourceActorWrite observation nontrivial half depth ordinal h H N factory grade data sourceCfg language
   (WB.oldPaid data.1 sourceCfg+WB.nativeAt sourceCfg frame supplied)) := rfl

theorem source_emitter_full_trace_inventory (frame : SourceFrame grade sourceCfg) :
 (sourceEmitterBase observation nontrivial half depth ordinal h H N factory grade data sourceCfg language).nextInventory frame =
 some (Stock.preserve ((AS.template factory grade data sourceCfg language).nextInventory frame)
  (SourceOperationPaidRelations.exposure
   (sourceActorGradedTrace observation nontrivial half depth ordinal h H N factory grade data sourceCfg language frame))) := rfl

theorem source_emitter_R_trace_pair_inventory (frame : SourceFrame grade sourceCfg) :
 (sourceEmitterBase observation nontrivial half depth ordinal h H N factory grade data sourceCfg language).nextPairInventory frame =
 some (Stock.preserve ((AS.template factory grade data sourceCfg language).nextPairInventory frame)
  (SourceOperationPaidRelations.exposure (sourceRBeforeTrace factory grade data sourceCfg language frame))) := rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRSourceSuccessor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
