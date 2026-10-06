import H0mework.Realization.Operations.Tree.Fold.Source
import H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Installation.Inquiry

/-! The installed source tree supplies the original inquiry executor. Its
whole original material and actual charged history remain in the result. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold
open SourceOperationEffects SourceOperationExecution
namespace Installation
open RootInquiryCompletion
namespace I
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry
  (query state root visit resultFace result_value result_history compiles answered_next)
end I
variable {Root Carrier : Type u}
variable (atOccurrence : Root → List Carrier → Carrier)
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
abbrev Occurrence (current : V.Current) :=
  old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current
structure TreeReadAt {current : V.Current} (occurrence : Occurrence old current) : Type u where
  projection : old.root.source.base.projectionLaw.Projection
  active : old.root.source.base.projectionLaw.ActiveAt projection occurrence
  classifier_eq : old.root.source.base.projectionLaw.classify projection occurrence = .inl active
  payload_eq : old.root.source.base.projectionLaw.PayloadAt projection occurrence active = RootedAccountedUnfolding Root
variable (source : {current : V.Current} → (occurrence : Occurrence old current) → TreeReadAt (Root:=Root) old occurrence)
def treeAt {current : V.Current} (occurrence : Occurrence old current) : RootedAccountedUnfolding Root :=
  Eq.mp (source occurrence).payload_eq (old.root.source.base.projectionLaw.project
    (source occurrence).projection occurrence (source occurrence).active)
def reader {current : V.Current} (occurrence : Occurrence old current) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=Value Root Carrier) (Var:=Var Root) (sort:=.result) :=
  ⟨environment, program atOccurrence (treeAt old source occurrence)⟩
theorem actual_value : (I.resultFace old (reader atOccurrence old source)).rootRead.2.2.1 =
    Finsupp.single ((treeAt old source (old.root.emitted old.visit.current)).fold atOccurrence) 1 :=
  (I.result_value old (reader atOccurrence old source)).trans (program_value _ _)
theorem actual_trace : (I.resultFace old (reader atOccurrence old source)).rootRead.2.1.2.length =
    remaining (program atOccurrence (treeAt old source (old.root.emitted old.visit.current))) :=
  I.result_history old (reader atOccurrence old source)
theorem answer_next (incidence : old.Query) : type_of% (I.answered_next old (reader atOccurrence old source)
    (I.query old (reader atOccurrence old source) incidence)) :=
  I.answered_next old (reader atOccurrence old source) (I.query old (reader atOccurrence old source) incidence)
end Installation

end SourceOperationNative.Tree.Fold
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
