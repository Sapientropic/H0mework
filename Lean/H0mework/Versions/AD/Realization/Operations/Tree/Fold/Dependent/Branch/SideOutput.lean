import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Branch.SideConsumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.Side
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
variable (code : SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot)
variable (successor : StepLedgerSuccessorAt (step root recognition code))
abbrev historyOf (data : DataAt root recognition code (some successor)) := CofinalHistorySettlement.RootGeneratedCofinalHistoryAt.generate
  (rootOccurrence:=RootedAccountedUnfolding.zero data.1.receipt.1) (seedOccurrence:=data.1.seed) (continuationOccurrence:=data.1.continuation)
abbrev evaluationOf (data : DataAt root recognition code (some successor)) :=
  CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.generate (history:=historyOf root recognition code successor data)
    (evaluatorOccurrence:=data.2.1)
abbrev dispositionOf (data : DataAt root recognition code (some successor)) :=
  CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.settleWithResidual (evaluationOf root recognition code successor data)
abbrev sourceStatesOf (data : DataAt root recognition code (some successor)) := data.2.2.2.1.map (sourceState root recognition code)
abbrev targetStatesOf (data : DataAt root recognition code (some successor)) := data.2.2.2.2.map (targetState root recognition code successor)

def OutputAt (selected : Option (StepLedgerSuccessorAt (step root recognition code))) (data : DataAt root recognition code selected) : Type (u+2) :=
  match selected with
  | none => ULift.{u+2} (SourceTemporalMaterial.Action.Receipt root)
  | some successor =>
      (type_of% (historyOf root recognition code successor data)) ×
      (type_of% (dispositionOf root recognition code successor data)) ×
      (type_of% (sourceStatesOf root recognition code successor data)) ×
      (type_of% (targetStatesOf root recognition code successor data))
def eliminate (selected : Option (StepLedgerSuccessorAt (step root recognition code))) (data : DataAt root recognition code selected) :
    OutputAt root recognition code selected data :=
  match selected with
  | none => ⟨data⟩
  | some successor => ⟨historyOf root recognition code successor data,dispositionOf root recognition code successor data,
      sourceStatesOf root recognition code successor data,targetStatesOf root recognition code successor data⟩
def packetOutput (packet : Packet root recognition) := eliminate root recognition packet.1
  (stepSuccessor? (step root recognition packet.1)) packet.2
end SourceOperationNative.Tree.Fold.Dependent.Branch.Side
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
