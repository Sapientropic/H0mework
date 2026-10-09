import H0mework.Realization.Perfectification.Occurrence.Temporal.History.Common.Closure
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Source
import H0mework.Versions.PR.Realization.Perfectification.Occurrence.Temporal.Consumer
import H0mework.Versions.AD.Realization.Perfectification.Occurrence.Temporal.Action.Source
import H0mework.Realization.Operations.BinaryInputs
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceHistoryCommon.Root
open SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
abbrev step := recognition.generateStepAt visit
variable (successor : StepLedgerSuccessorAt (step root visit recognition))
abbrev law := recognition.material.parent.commonLaw.historyLaw
abbrev sourceRaw := (law root recognition).rawAt (step root visit recognition).sourceOccurrence
abbrev targetRaw := (law root recognition).rawAt successor.targetOccurrence
abbrev sourceHistory := StepSourceHistory (step root visit recognition)
abbrev targetHistory := StepTargetHistory (step root visit recognition) successor
abbrev G := (law root recognition).Generator
abbrev SourceRaw := type_of% (sourceRaw root visit recognition)
abbrev TargetRaw := type_of% (targetRaw root visit recognition successor)
structure Raw : Type u where
  receipt : SourceTemporalMaterial.Action.Receipt root
  source : SourceRaw root visit recognition
  target : TargetRaw root visit recognition successor
  seed : RootedAccountedUnfolding (PresentedRelationEventAt (G root recognition))
  continuation : RootedAccountedUnfolding
    (PresentedRelationEventAt (G root recognition) → RootedAccountedUnfolding (PresentedRelationEventAt (G root recognition)))
def combine (source : SourceRaw root visit recognition) (target : TargetRaw root visit recognition successor) : Raw root visit recognition successor :=
  ⟨SourceTemporalMaterial.Action.receipt root (SourceTemporalMaterial.encode root.toAuthoritativeRoot.toLedgerRoot visit),
    source, target, SourceHistoryCommon.seed source.seed target.seed,
    RootedAccountedUnfolding.zero (SourceHistoryCommon.continuation source.continuation.root target.continuation.root)⟩
def actualRaw := combine root visit recognition successor (sourceRaw root visit recognition) (targetRaw root visit recognition successor)
abbrev common := SourceHistoryCommon.history (sourceHistory root visit recognition) (targetHistory root visit recognition successor)
  (RootedAccountedUnfolding.zero (SourceTemporalMaterial.encode root.toAuthoritativeRoot.toLedgerRoot visit))
abbrev left := SourceHistoryCommon.leftTransition (sourceHistory root visit recognition) (targetHistory root visit recognition successor)
  (RootedAccountedUnfolding.zero (SourceTemporalMaterial.encode root.toAuthoritativeRoot.toLedgerRoot visit))
abbrev right := SourceHistoryCommon.rightTransition (sourceHistory root visit recognition) (targetHistory root visit recognition successor)
  (RootedAccountedUnfolding.zero (SourceTemporalMaterial.encode root.toAuthoritativeRoot.toLedgerRoot visit))
abbrev Slot := ULift.{u} SourceNativeBinary.BinarySort
abbrev Value : Slot.{u} → Type u := fun slot =>
  SourceNativeBinary.Value (SourceRaw root visit recognition) (TargetRaw root visit recognition successor)
    (Raw root visit recognition successor) slot.down
abbrev Variables : Slot.{u} → Type u := fun slot =>
  SourceNativeBinary.Var (SourceRaw root visit recognition) (TargetRaw root visit recognition successor)
    (Raw root visit recognition successor) slot.down
instance : (slot : Slot.{u}) → AddCommGroup (Value root visit recognition successor slot) :=
  fun slot => SourceNativeBinary.instAddCommGroupValue slot.down

def environment : Env (Value root visit recognition successor) (Variables root visit recognition successor) :=
  fun slot value => SourceNativeBinary.environment slot.down value

def expression : Expr (Value root visit recognition successor) (Variables root visit recognition successor) (ULift.up .result) :=
  .bilinear (s:=ULift.up .left) (t:=ULift.up .right) (SourceNativeBinary.lift (combine root visit recognition successor))
    (.var (sourceRaw root visit recognition)) (.var (targetRaw root visit recognition successor))
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=Value root visit recognition successor)
    (Var:=Variables root visit recognition successor) (sort:=ULift.up .result) :=
  ⟨environment root visit recognition successor, expression root visit recognition successor⟩
def reader (_ : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt visit.current) := raw root visit recognition successor
end SourceHistoryCommon.Root
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
