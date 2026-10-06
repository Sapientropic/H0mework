import H0mework.Versions.AD.Realization.Perfectification.Occurrence.Temporal.Source
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source
/-! The complete temporal material is installed before calculation. The
existing mathematical source inherits this exact parent visit at every step. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceTemporalMaterial.Calculation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw baseInstallation)
end O
namespace M
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
  (root visit runtime)
end M
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (parent : SourceNativeLivingRootClosure N V)
variable (origin : SourceNativeTemporalVisitAt parent.toAuthoritativeRoot.toLedgerRoot)

def component : SourceNativeProjectionLaw parent.source.base.restructuringSource.toLedgerSource where
  Projection := PUnit.{u+1}
  ActiveAt := fun _ {_current} _ => PUnit.{u+1}
  InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} _ _ => Code parent.toAuthoritativeRoot.toLedgerRoot
  project := fun _ {_current} _ _ => encode parent.toAuthoritativeRoot.toLedgerRoot origin

abbrev sourceRoot := parent.withProjectionCoface (component parent origin)
abbrev sourceVisit : SourceNativeTemporalVisitAt (sourceRoot parent origin).toAuthoritativeRoot.toLedgerRoot := origin
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : parent.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin.current →
  O.Raw (Value:=Value) (Var:=Var) (sort:=sort))

abbrev runtime := M.runtime (sourceRoot parent origin) (sourceVisit parent origin) U7 calculus reader

def face (count : Nat) : SourceNativeRootSemanticFaceAt
    (M.root (sourceRoot parent origin) (sourceVisit parent origin) U7 calculus reader count)
    (M.visit (sourceRoot parent origin) (sourceVisit parent origin) reader count) where
  projection := .inherited (.inherited (.inherited
    ((O.baseInstallation (sourceRoot parent origin).toAuthoritativeRoot origin.current reader).embed
      (.inl (.component PUnit.unit)))))
  active := PUnit.unit
  classifier_eq := rfl

theorem readback (count : Nat) : decode parent.toAuthoritativeRoot.toLedgerRoot
    (face parent origin U7 calculus reader count).rootRead = origin :=
  decode_encode parent.toAuthoritativeRoot.toLedgerRoot origin

theorem same_ledger : (sourceRoot parent origin).toAuthoritativeRoot.toLedgerRoot =
    parent.toAuthoritativeRoot.toLedgerRoot := rfl

end SourceTemporalMaterial.Calculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
