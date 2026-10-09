import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Source
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Source

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects
namespace Lower
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ slot, AddCommGroup (Value slot)] {sort : Sorts}
variable {N' : WorldRelationNetwork.{u}} {V' : Vocabulary.{u}}
variable (actualRoot : SourceNativeLivingRootClosure N' V')
variable (actualVisit : SourceNativeTemporalVisitAt actualRoot.toAuthoritativeRoot.toLedgerRoot)
variable (face : SourceNativeRootSemanticFaceAt actualRoot actualVisit)
variable (raw : SourceOperationInquiry.Context.Raw (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=sort))
variable (same : HEq face.rootRead raw)
private def restrictionOfFace : SourceOperationInquiry.Context.RawRestrictionAt
 (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=sort)
 (⟨N',⟨V',actualRoot.toAuthoritativeRoot,actualVisit⟩⟩ : AnyAuthoritativeRootCurrent.{u}) where
 projection := face.projection
 active := face.active
 classifier_eq := face.classifier_eq
 payload_eq := type_eq_of_heq same
private def readRestriction (actual : AnyAuthoritativeRootCurrent.{u})
 (restriction : SourceOperationInquiry.Context.RawRestrictionAt (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=sort) actual) :
 SourceOperationInquiry.Context.Raw (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=sort) :=
 Eq.mp restriction.payload_eq (actual.current.root.source.projectionLaw.project restriction.projection
  (actual.current.root.emitted actual.current.visit.current) restriction.active)
private theorem restriction_read : readRestriction _ (restrictionOfFace actualRoot actualVisit face raw same)=raw := by
 have cast : HEq (readRestriction _ (restrictionOfFace actualRoot actualVisit face raw same)) face.rootRead :=
  eqRec_heq_iff.mpr HEq.rfl
 exact eq_of_heq (cast.trans same)
end Lower
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage : Nat)
abbrev Value := SourceOperationScalarInventoryLift.PairValue (CurrentChild.Value root visit recognition)
abbrev Variable := JointLow.Variable (X:=CurrentChild.Variable root visit recognition)
abbrev sort := CurrentChild.resultSlot root recognition
abbrev engine := runtime root visit recognition U7 calculus anchor sourceStage
abbrev mainAt (count : Nat) := Live.rawAt root visit recognition U7 calculus anchor
 (E.epoch (frameAt root visit recognition U7 calculus anchor sourceStage count))
 (sourceSeed root visit recognition U7 calculus anchor sourceStage)
 (E.Shared.actualOccurrence (frameAt root visit recognition U7 calculus anchor sourceStage count))
private def restriction (frame : Dynamic.Frame root visit recognition) := Lower.restrictionOfFace
 (E.Shared.root frame (programme root visit recognition U7 calculus anchor sourceStage))
 (E.Shared.visit frame (programme root visit recognition U7 calculus anchor sourceStage))
 (mainRawFace root visit recognition U7 calculus anchor frame (sourceSeed root visit recognition U7 calculus anchor sourceStage))
 (Live.rawAt root visit recognition U7 calculus anchor (E.epoch frame)
  (sourceSeed root visit recognition U7 calculus anchor sourceStage) (E.Shared.actualOccurrence frame))
 (heq_of_eq (main_raw root visit recognition U7 calculus anchor frame (sourceSeed root visit recognition U7 calculus anchor sourceStage)))
private theorem restriction_read (frame : Dynamic.Frame root visit recognition) :
 Lower.readRestriction _ (restriction root visit recognition U7 calculus anchor sourceStage frame)=
 Live.rawAt root visit recognition U7 calculus anchor (E.epoch frame)
  (sourceSeed root visit recognition U7 calculus anchor sourceStage) (E.Shared.actualOccurrence frame) :=
 Lower.restriction_read _ _ _ _ _

def rawSource (state : (engine root visit recognition U7 calculus anchor sourceStage).State) :
 SourceOperationInquiry.Context.RawAt (PhysicalValue:=Value root visit recognition)
 (PhysicalVar:=Variable root visit recognition) (sort:=sort root recognition)
 (engine root visit recognition U7 calculus anchor sourceStage) state := by
 rcases state with ⟨⟨count⟩, activation⟩
 exact restriction root visit recognition U7 calculus anchor sourceStage
  (frameAt root visit recognition U7 calculus anchor sourceStage count.down)
private def index (actual : Engine (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.process
 (initial root visit recognition U7 calculus anchor sourceStage) (programme root visit recognition U7 calculus anchor sourceStage))) : Nat := by
 rcases actual with ⟨count⟩
 exact count.down
private theorem raw_state (state : (engine root visit recognition U7 calculus anchor sourceStage).State) :
 SourceOperationInquiry.Context.raw (engine root visit recognition U7 calculus anchor sourceStage)
  (rawSource root visit recognition U7 calculus anchor sourceStage) state =
 mainAt root visit recognition U7 calculus anchor sourceStage
  (index root visit recognition U7 calculus anchor sourceStage state.engine) := by
 rcases state with ⟨⟨count⟩, activation⟩
 exact restriction_read root visit recognition U7 calculus anchor sourceStage _

theorem raw_actual (count : Nat) : SourceOperationInquiry.Context.raw
 (engine root visit recognition U7 calculus anchor sourceStage) (rawSource root visit recognition U7 calculus anchor sourceStage)
 ((engine root visit recognition U7 calculus anchor sourceStage).stateAt count) =
 mainAt root visit recognition U7 calculus anchor sourceStage count := by
 have indexEq : index root visit recognition U7 calculus anchor sourceStage
  ((engine root visit recognition U7 calculus anchor sourceStage).stateAt count).engine=count := by
  have same := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_node
   (initial root visit recognition U7 calculus anchor sourceStage) (programme root visit recognition U7 calculus anchor sourceStage) count
  generalize engineEq : ((engine root visit recognition U7 calculus anchor sourceStage).stateAt count).engine=actual at same ⊢
  rcases actual with ⟨hidden⟩
  have hiddenEq : hidden=ULift.up count :=
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.process
    (initial root visit recognition U7 calculus anchor sourceStage) (programme root visit recognition U7 calculus anchor sourceStage)).erase_injective rfl rfl
    (congrArg RootInquiryProcessNode.erase same)
  subst hidden
  rfl
 exact (raw_state root visit recognition U7 calculus anchor sourceStage _).trans
  (congrArg (mainAt root visit recognition U7 calculus anchor sourceStage) indexEq)

theorem environment_actual (count : Nat) : SourceOperationInquiry.Context.readEnv
 (engine root visit recognition U7 calculus anchor sourceStage) (rawSource root visit recognition U7 calculus anchor sourceStage)
 ((engine root visit recognition U7 calculus anchor sourceStage).stateAt count) =
 (mainAt root visit recognition U7 calculus anchor sourceStage count).environment :=
 congrArg (fun raw => raw.environment) (raw_actual root visit recognition U7 calculus anchor sourceStage count)
theorem syntax_actual (count : Nat) : (SourceOperationInquiry.Context.raw
 (engine root visit recognition U7 calculus anchor sourceStage) (rawSource root visit recognition U7 calculus anchor sourceStage)
 ((engine root visit recognition U7 calculus anchor sourceStage).stateAt count)).expression =
 (mainAt root visit recognition U7 calculus anchor sourceStage count).expression :=
 congrArg (fun raw => raw.expression) (raw_actual root visit recognition U7 calculus anchor sourceStage count)
theorem increment_actual (count : Nat) : SourceOperationInquiry.Context.increment
 (engine root visit recognition U7 calculus anchor sourceStage) (rawSource root visit recognition U7 calculus anchor sourceStage)
 ((engine root visit recognition U7 calculus anchor sourceStage).stateAt count) =
 (mainAt root visit recognition U7 calculus anchor sourceStage (count+1)).environment-
 (mainAt root visit recognition U7 calculus anchor sourceStage count).environment := by
 change SourceOperationInquiry.Context.readEnv _ _ ((engine root visit recognition U7 calculus anchor sourceStage).stateAt (count+1))-
  SourceOperationInquiry.Context.readEnv _ _ ((engine root visit recognition U7 calculus anchor sourceStage).stateAt count)=_
 rw [environment_actual,environment_actual]
 rfl

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
