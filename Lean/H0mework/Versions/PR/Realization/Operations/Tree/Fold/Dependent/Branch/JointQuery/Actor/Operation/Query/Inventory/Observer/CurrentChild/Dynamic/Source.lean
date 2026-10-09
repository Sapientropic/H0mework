import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.Source

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (base actualOccurrence)
end Shared
end E
namespace C
export SourceOperationInquiry.Context.Installation (Occurrence materialAt)
end C
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
abbrev Frame := RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=CurrentChild.Value root visit recognition) (Var:=CurrentChild.Variable root visit recognition)
 (sort:=CurrentChild.resultSlot root recognition)
def binding : ∀ slot, CurrentChild.Variable root visit recognition slot →
 Expr (CurrentChild.Value root visit recognition) (CurrentChild.Variable root visit recognition) slot
 | .inl slot, name => CurrentChild.embed root visit recognition (Observer.Action.binding root visit recognition slot name)
 | .inr _, absent => PEmpty.elim absent
abbrev Read (frame : Frame root visit recognition) :=
 ∀ {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered},
 C.Occurrence frame (current:=current) → Env (CurrentChild.Value root visit recognition) (CurrentChild.Variable root visit recognition)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor : Nat)
variable (frame : Frame root visit recognition)
abbrev currentRead : Read root visit recognition frame := fun {_current} supplied => frame.environment
 (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.originalOccurrence frame.registered frame.packetAt supplied)
abbrev nextRead : Read root visit recognition frame := fun {_current} supplied =>
 SourceOperationScalarPresentation.SourceSubstitution.sourceEnvironment (binding root visit recognition)
  (currentRead root visit recognition frame supplied)
variable (read : Read root visit recognition frame)
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : C.Occurrence frame (current:=current))

def actorRawFor : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=CurrentChild.Value root visit recognition) (Var:=CurrentChild.Variable root visit recognition)
 (sort:=CurrentChild.resultSlot root recognition) :=
 ⟨read supplied,CurrentChild.actorTerm root visit recognition⟩
def actorPaidFor := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (E.Shared.base frame).root.toAuthoritativeRoot
 (fun {_current} occurrence => actorRawFor root visit recognition frame read occurrence) supplied
def actorWordFor := (actorPaidFor root visit recognition frame read supplied).2.2.1.2.1.2.1 +
 (actorPaidFor root visit recognition frame read supplied).2.2.1.2.1.2.2
def supportFor := (actorWordFor root visit recognition frame read supplied).support.toList

def childTerm (source : CurrentChild.SourceActor root recognition) := CurrentChild.oldOutputEmbed root visit recognition
 (Observer.oldOutputEmbed root visit recognition (Inventory.childExpressionAtCode root visit recognition source.1.1))
def childrenFor := (supportFor root visit recognition frame read supplied).map (childTerm root visit recognition)
def indicesFor := (supportFor root visit recognition frame read supplied).flatMap (CurrentChild.indices root recognition)
def samplesFor := (supportFor root visit recognition frame read supplied).flatMap (CurrentChild.samples root recognition)
def observationsFor := ((indicesFor root visit recognition frame read supplied).map
 (fun index => List.ofFn (fun kind : Fin 4 => CurrentChild.observationOutput root visit recognition index kind))).flatten
def gramsFor := (samplesFor root visit recognition frame read supplied).flatMap
 (fun first => (samplesFor root visit recognition frame read supplied).map
  (fun second => CurrentChild.gramOutput root visit recognition first second))
def termsFor := CurrentChild.oldTerm root visit recognition U7 calculus anchor ::
 CurrentChild.actorTerm root visit recognition ::
 (childrenFor root visit recognition frame read supplied ++ observationsFor root visit recognition frame read supplied ++
  gramsFor root visit recognition frame read supplied)
def expressionFor := CurrentChild.programme root visit recognition
 (termsFor root visit recognition U7 calculus anchor frame read supplied)
def rawFor : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=CurrentChild.Value root visit recognition) (Var:=CurrentChild.Variable root visit recognition)
 (sort:=CurrentChild.resultSlot root recognition) :=
 ⟨read supplied,expressionFor root visit recognition U7 calculus anchor frame read supplied⟩
def paidFor := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (E.Shared.base frame).root.toAuthoritativeRoot
 (fun {_current} occurrence => rawFor root visit recognition U7 calculus anchor frame read occurrence) supplied
def traceFor := execution (rawFor root visit recognition U7 calculus anchor frame read supplied).environment
 (rawFor root visit recognition U7 calculus anchor frame read supplied).expression
abbrev RowMaterial (source : CurrentChild.SourceActor root recognition) :=
 (position : Fin (CurrentChild.rowsAtActor root recognition source).length) →
 let row := CurrentChild.rowAt root recognition ⟨source,position⟩
 Observer.sourceRawType root recognition row × Observer.targetRawType root recognition row
abbrev ActorMaterial := Σ source : CurrentChild.SourceActor root recognition,
 (type_of% (Operation.sourceOperationAtCode root source.1.1 recognition)) × RowMaterial root recognition source
def actorMaterial (source : CurrentChild.SourceActor root recognition) : ActorMaterial root recognition :=
 ⟨source,Operation.sourceOperationAtCode root source.1.1 recognition,
  fun position =>
   let row := CurrentChild.rowAt root recognition ⟨source,position⟩
   (Observer.sourceExposure root recognition row,Observer.targetExposure root recognition row)⟩
def materialFor := (C.materialAt frame supplied,actorRawFor root visit recognition frame read supplied,
 actorPaidFor root visit recognition frame read supplied,actorWordFor root visit recognition frame read supplied,
 supportFor root visit recognition frame read supplied,
 (supportFor root visit recognition frame read supplied).map (actorMaterial root recognition),
 rawFor root visit recognition U7 calculus anchor frame read supplied,
 paidFor root visit recognition U7 calculus anchor frame read supplied,
 traceFor root visit recognition U7 calculus anchor frame read supplied)
abbrev environmentAt := currentRead root visit recognition frame supplied
abbrev generatedEnvironmentAt := nextRead root visit recognition frame supplied
abbrev actorPaidAt := actorPaidFor root visit recognition frame (currentRead root visit recognition frame) supplied
abbrev actorWordAt := actorWordFor root visit recognition frame (currentRead root visit recognition frame) supplied
abbrev supportAt := supportFor root visit recognition frame (currentRead root visit recognition frame) supplied
abbrev rawAt := rawFor root visit recognition U7 calculus anchor frame (currentRead root visit recognition frame) supplied
abbrev paidAt := paidFor root visit recognition U7 calculus anchor frame (currentRead root visit recognition frame) supplied
abbrev traceAt := traceFor root visit recognition U7 calculus anchor frame (currentRead root visit recognition frame) supplied
abbrev materialAt := materialFor root visit recognition U7 calculus anchor frame (currentRead root visit recognition frame) supplied
variable (sourceStage : Nat)
abbrev initial := CurrentChild.Installation.initial root visit recognition U7 calculus anchor sourceStage
abbrev sourceSeed := CurrentChild.Installation.seed root visit recognition U7 calculus anchor sourceStage
abbrev sourceRaw := rawAt root visit recognition U7 calculus anchor (initial root visit recognition U7 calculus anchor sourceStage)
 (E.Shared.actualOccurrence (initial root visit recognition U7 calculus anchor sourceStage))
abbrev sourceMaterial := materialAt root visit recognition U7 calculus anchor (initial root visit recognition U7 calculus anchor sourceStage)
 (E.Shared.actualOccurrence (initial root visit recognition U7 calculus anchor sourceStage))

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
