import H0mework.Versions.R2.Foundation.Inquiry.Protocol

/-! A registered inquiry input is an installed restriction of the current
root occurrence. The query is read from its payload; no caller query enters
this receipt. The low-universe coordinates retain proof-relevant input data. -/

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion

structure SourceNativeRootInquiryInputAt {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (Query : Type u) : Type u where
  projection : root.toAuthoritativeRoot.source.projectionLaw.Projection
  active : root.toAuthoritativeRoot.source.projectionLaw.ActiveAt projection (root.emitted visit.current)
  classifier_eq : root.toAuthoritativeRoot.source.projectionLaw.classify projection (root.emitted visit.current) = .inl active
  queryType_eq : root.toAuthoritativeRoot.source.projectionLaw.PayloadAt projection (root.emitted visit.current) active = Query

namespace SourceNativeRootInquiryInputAt

def face {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot} {Query : Type u}
    (input : SourceNativeRootInquiryInputAt root visit Query) : SourceNativeRootSemanticFaceAt root visit :=
  ⟨input.projection, input.active, input.classifier_eq⟩

def query {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot} {Query : Type u}
    (input : SourceNativeRootInquiryInputAt root visit Query) : Query :=
  Eq.mp input.queryType_eq input.face.rootRead

end SourceNativeRootInquiryInputAt

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
