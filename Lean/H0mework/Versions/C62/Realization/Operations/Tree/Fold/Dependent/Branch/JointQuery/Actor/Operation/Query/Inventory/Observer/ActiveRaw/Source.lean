import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Action.Source
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Source

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects
namespace Context
export SourceOperationInquiry.Context (Raw RawRestrictionAt)
end Context
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor : Nat)
variable (frame : Observer.Action.Frame root visit recognition)
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : Observer.Action.C.Occurrence frame (current:=current))

def rawAt : Context.Raw (PhysicalValue:=Observer.Value root visit recognition)
    (PhysicalVar:=Observer.Variable root visit recognition) (sort:=Observer.resultSlot root recognition) :=
  ⟨Observer.Action.environmentAt root visit recognition frame supplied,
    Observer.Action.observerSyntax root visit recognition U7 calculus anchor⟩
def component : SourceNativeProjectionLaw (Observer.Action.E.Shared.base frame).root.source.base.restructuringSource.toLedgerSource where
  Projection := PUnit.{u+1}
  ActiveAt := fun _ {_current} _ => PUnit.{u+1}
  InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} _ _ => Context.Raw (PhysicalValue:=Observer.Value root visit recognition)
    (PhysicalVar:=Observer.Variable root visit recognition) (sort:=Observer.resultSlot root recognition)
  project := fun _ {_current} occurrence _ => rawAt root visit recognition U7 calculus anchor frame occurrence

namespace Lower
variable {N' : WorldRelationNetwork.{u}} {V' : Vocabulary.{u}}
variable (actualRoot : SourceNativeLivingRootClosure N' V')
variable (actualVisit : SourceNativeTemporalVisitAt actualRoot.toAuthoritativeRoot.toLedgerRoot)
variable (face : SourceNativeRootSemanticFaceAt actualRoot actualVisit)
variable (raw : Context.Raw (PhysicalValue:=Observer.Value root visit recognition)
  (PhysicalVar:=Observer.Variable root visit recognition) (sort:=Observer.resultSlot root recognition))
variable (same : HEq face.rootRead raw)
def restrictionOfFace : Context.RawRestrictionAt (PhysicalValue:=Observer.Value root visit recognition)
    (PhysicalVar:=Observer.Variable root visit recognition) (sort:=Observer.resultSlot root recognition)
    (⟨N',⟨V',actualRoot.toAuthoritativeRoot,actualVisit⟩⟩ : AnyAuthoritativeRootCurrent.{u}) where
  projection := face.projection
  active := face.active
  classifier_eq := face.classifier_eq
  payload_eq := type_eq_of_heq same

def readRestriction (actual : AnyAuthoritativeRootCurrent.{u})
    (restriction : Context.RawRestrictionAt (PhysicalValue:=Observer.Value root visit recognition)
      (PhysicalVar:=Observer.Variable root visit recognition) (sort:=Observer.resultSlot root recognition) actual) :
    Context.Raw (PhysicalValue:=Observer.Value root visit recognition)
      (PhysicalVar:=Observer.Variable root visit recognition) (sort:=Observer.resultSlot root recognition) :=
  Eq.mp restriction.payload_eq (actual.current.root.source.projectionLaw.project restriction.projection
    (actual.current.root.emitted actual.current.visit.current) restriction.active)
theorem restriction_read : readRestriction root visit recognition _
    (restrictionOfFace root visit recognition actualRoot actualVisit face raw same) = raw := by
  have cast : HEq (readRestriction root visit recognition _
      (restrictionOfFace root visit recognition actualRoot actualVisit face raw same)) face.rootRead :=
    eqRec_heq_iff.mpr HEq.rfl
  exact eq_of_heq (cast.trans same)
end Lower
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
