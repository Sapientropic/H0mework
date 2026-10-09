import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Source
import H0mework.Versions.PR.Realization.Perfectification.Occurrence.Temporal.History.Common.RootSource
import H0mework.Realization.Operations.Action
import H0mework.Realization.Operations.ObservationModel
import Mathlib.Analysis.InnerProductSpace.ProdL2
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceHistoryCommon.Root.Action
open RootLawDependentJointStateController RootLawDependentJointTransition
open CofinalHistoryTransition SourceGeneratedObservationAction SourceGeneratedActionObservationHistory
namespace R
export SourceHistoryCommon.Root (step sourceHistory targetHistory common left right)
end R
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (successor : StepLedgerSuccessorAt (R.step root visit recognition))
abbrev sourceExposure := stepSourceExposure (R.step root visit recognition)
abbrev targetExposure := stepTargetExposure (R.step root visit recognition) successor
abbrev Source := (R.sourceHistory root visit recognition).CompletionCarrier
abbrev Target := (R.targetHistory root visit recognition successor).CompletionCarrier
abbrev Joint := Source root visit recognition × Target root visit recognition successor
abbrev Observation := (R.common root visit recognition successor).CompletionCarrier
def action : Joint root visit recognition successor →ₗ[ℤ] Joint root visit recognition successor :=
  (sourceExposure root visit recognition).sourceAction.carrierAction.prodMap
    (targetExposure root visit recognition successor).sourceAction.carrierAction
def observation : Joint root visit recognition successor →ₗ[ℤ] Observation root visit recognition successor :=
  (GeneratedTransition.completionMap (R.sourceHistory root visit recognition) (R.common root visit recognition successor)
    (R.left root visit recognition successor)).coprod
  (GeneratedTransition.completionMap (R.targetHistory root visit recognition successor) (R.common root visit recognition successor)
    (R.right root visit recognition successor))
abbrev defect := actionDefect (action root visit recognition successor) (observation root visit recognition successor)
abbrev model := Model (action root visit recognition successor) (observation root visit recognition successor)
abbrev modelAction := SourceGeneratedActionObservationHistory.modelAction (action root visit recognition successor) (observation root visit recognition successor)
theorem common_model_square : type_of% (SourceGeneratedActionObservationHistory.modelAction_source
    (action root visit recognition successor) (observation root visit recognition successor)) :=
  SourceGeneratedActionObservationHistory.modelAction_source (action root visit recognition successor) (observation root visit recognition successor)
def pairing : Joint root visit recognition successor →ₗ[ℤ] Module.Dual ℤ (Joint root visit recognition successor) :=
  ((stepSourcePairing (R.step root visit recognition)).comp (LinearMap.fst ℤ _ _)).compl₂ (LinearMap.fst ℤ _ _) +
    ((stepTargetPairing (R.step root visit recognition) successor).comp (LinearMap.snd ℤ _ _)).compl₂ (LinearMap.snd ℤ _ _)
def dualAction : Joint root visit recognition successor →ₗ[ℤ] Joint root visit recognition successor :=
  (sourceExposure root visit recognition).sourceAction.dualCarrierAction.prodMap
    (targetExposure root visit recognition successor).sourceAction.dualCarrierAction

def actionData : SourceGeneratedScalarEquivariantPerfectAction.ActionData (pairing root visit recognition successor) where
  carrierAction := action root visit recognition successor
  dualCarrierAction := dualAction root visit recognition successor
  evaluation_commutes := by
    apply LinearMap.ext
    intro value
    apply LinearMap.ext
    intro dual
    have source := congrArg (fun functional => functional dual.1)
      (LinearMap.congr_fun (sourceExposure root visit recognition).sourceAction.evaluation_commutes value.1)
    have target := congrArg (fun functional => functional dual.2)
      (LinearMap.congr_fun (targetExposure root visit recognition successor).sourceAction.evaluation_commutes value.2)
    exact congrArg₂ (· + ·) source target

abbrev Measured (H : Type u) := WithLp 2 (H × H)
def measurement : Joint root visit recognition successor →ₗ[ℤ] Measured H :=
  (WithLp.linearEquiv 2 ℤ (H × H)).symm.toLinearMap.comp
    ((sourceExposure root visit recognition).measurement.prodMap (targetExposure root visit recognition successor).measurement)
def evolution : Measured H →ₗᵢ[ℂ] Measured H :=
  (sourceExposure root visit recognition).hilbertEvolution.withLpProdMap 2
    (targetExposure root visit recognition successor).hilbertEvolution

def jointData : SourceGeneratedIntegralEquivariantPerfectRealization.JointActionData (H:=Measured H)
    (pairing root visit recognition successor) where
  sourceAction := actionData root visit recognition successor
  coherentEvolution := evolution root visit recognition successor
abbrev realization := SourceGeneratedIntegralEquivariantPerfectRealization.generate
  (pairing root visit recognition successor) (measurement root visit recognition successor) (jointData root visit recognition successor)
abbrev SourceRaw := type_of% (sourceExposure root visit recognition)
abbrev TargetRaw := type_of% (targetExposure root visit recognition successor)
abbrev SourcePairing := type_of% (stepSourcePairing (R.step root visit recognition))
abbrev TargetPairing := type_of% (stepTargetPairing (R.step root visit recognition) successor)
structure Plan : Type u where
  source : SourceRaw root visit recognition
  target : TargetRaw root visit recognition successor
  sourcePairing : SourcePairing root visit recognition
  targetPairing : TargetPairing root visit recognition successor

def combine (first : SourceRaw root visit recognition) (second : TargetRaw root visit recognition successor) : Plan root visit recognition successor :=
  ⟨first,second,stepSourcePairing (R.step root visit recognition),stepTargetPairing (R.step root visit recognition) successor⟩
def actualPlan := combine root visit recognition successor (sourceExposure root visit recognition) (targetExposure root visit recognition successor)

abbrev Slot := ULift.{u} SourceNativeBinary.BinarySort
abbrev Value : Slot.{u} → Type u := fun slot => SourceNativeBinary.Value
  (SourceRaw root visit recognition) (TargetRaw root visit recognition successor) (Plan root visit recognition successor) slot.down
abbrev Variables : Slot.{u} → Type u := fun slot => SourceNativeBinary.Var
  (SourceRaw root visit recognition) (TargetRaw root visit recognition successor) (Plan root visit recognition successor) slot.down
instance : (slot : Slot.{u}) → AddCommGroup (Value root visit recognition successor slot) :=
  fun slot => SourceNativeBinary.instAddCommGroupValue slot.down

def environment : SourceOperationEffects.Env (Value root visit recognition successor) (Variables root visit recognition successor) :=
  fun slot input => SourceNativeBinary.environment slot.down input

def expression : SourceOperationEffects.Expr (Value root visit recognition successor) (Variables root visit recognition successor) (ULift.up .result) :=
  .bilinear (s:=ULift.up .left) (t:=ULift.up .right) (SourceNativeBinary.lift (combine root visit recognition successor))
    (.var (sourceExposure root visit recognition)) (.var (targetExposure root visit recognition successor))
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=Value root visit recognition successor)
    (Var:=Variables root visit recognition successor) (sort:=ULift.up .result) :=
  ⟨environment root visit recognition successor,expression root visit recognition successor⟩
def reader (_ : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt visit.current) := raw root visit recognition successor
end SourceHistoryCommon.Root.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
