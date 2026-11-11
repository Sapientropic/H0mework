import H0mework.Foundation.Inquiry.MinimalCoface
import H0mework.Foundation.Authority.OperationalInstallation

/-!
# Operational and U8-failure coordinates share one root coface

This is a derived commuting theorem, not another authority layer.  An
operational coordinate and an expressibility-failure face are both read from
one fixed temporal root occurrence.  Revision selection is deliberately
absent: it happens only after the rooted failure opens its minimal coface.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

open ObstructionGeneratedMinimalCoface

universe u

/-- The operational outcome and the exact failure payload are dependent faces
of one temporal root occurrence.  The payload remains related by `HEq`; it is
not cast into the root projection fibre and cannot hide projection loss. -/
theorem SourceNativeAuthoritativeTemporalEvolutionAt.operationalU8JointFaces_heq_sourceOutcomes
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (authority : SourceNativeAuthoritativeTemporalEvolutionAt
      root.toAuthoritativeRoot visit)
    (operational : SourceNativeOperationalSearchRecognitionAt root)
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    (face : SourceNativeRootExpressibilityFailureFaceAt
      root.toAuthoritativeRoot visit (U7 := U7) failure) :
    (HEq
          (authority.toLedgerReadout.jointFaceReadout
            operational.rootOperationalProjection face.projection).1
          (operational.operationalLaw.toProjectionLaw.outcomeAt
            PUnit.unit (root.emitted visit.current)) ∧
        HEq
          (authority.toLedgerReadout.jointFaceReadout
            operational.rootOperationalProjection face.projection).2
          (root.toAuthoritativeRoot.projectionOutcomeAt
            face.projection visit.current)) ∧
      HEq
        (root.toAuthoritativeRoot.source.projectionLaw.project
          face.projection (root.emitted visit.current) face.active)
        (SourceNativeRootExpressibilityFailureTokenAt.canonical
          (failure := failure) (calculus := face.calculus)
          (event := face.u7Event)) := by
  refine ⟨?_, face.project_heq⟩
  constructor
  · exact
      (authority.toLedgerReadout.projectionOutcome_heq_sourceOutcome
        operational.rootOperationalProjection).trans
        (operational.installation.outcome_heq
          (root.emitted visit.current) PUnit.unit)
  · exact authority.toLedgerReadout.projectionOutcome_heq_sourceOutcome
      face.projection

/-- Once the occurrence support is the failure support, both faces also share
the complete root account.  No selected revision or sibling U8 source enters
this statement. -/
theorem SourceNativeAuthoritativeTemporalEvolutionAt.operationalU8JointCoface_sameRootAccount
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (authority : SourceNativeAuthoritativeTemporalEvolutionAt
      root.toAuthoritativeRoot visit)
    (operational : SourceNativeOperationalSearchRecognitionAt root)
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    (face : SourceNativeRootExpressibilityFailureFaceAt
      root.toAuthoritativeRoot visit (U7 := U7) failure)
    (rootSupport_eq :
      root.toAuthoritativeRoot.toRoot.supportAt visit.current = support) :
    ((HEq
            (authority.toLedgerReadout.jointFaceReadout
              operational.rootOperationalProjection face.projection).1
            (operational.operationalLaw.toProjectionLaw.outcomeAt
              PUnit.unit (root.emitted visit.current)) ∧
          HEq
            (authority.toLedgerReadout.jointFaceReadout
              operational.rootOperationalProjection face.projection).2
            (root.toAuthoritativeRoot.projectionOutcomeAt
              face.projection visit.current)) ∧
        HEq
          (root.toAuthoritativeRoot.source.projectionLaw.project
            face.projection (root.emitted visit.current) face.active)
          (SourceNativeRootExpressibilityFailureTokenAt.canonical
            (failure := failure) (calculus := face.calculus)
            (event := face.u7Event))) ∧
      (operational.operationalLaw.positionAt
        (root.emitted visit.current)).searchCurrent.frontier = support ∧
      root.toAuthoritativeRoot.toRoot.account.anchorKey
          (V.anchorAt visit.current) = N.anchorAt support ∧
      root.toAuthoritativeRoot.toRoot.account.incidenceKey
          (V.incidenceAt visit.current) = N.incidenceAt support ∧
      root.toAuthoritativeRoot.toRoot.account.lineageKey
          (V.lineageAt visit.current) = N.lineageAt support := by
  have faces := authority.operationalU8JointFaces_heq_sourceOutcomes
    operational face
  exact ⟨faces,
    (operational.operationalFrontier_eq_rootSupport visit).trans rootSupport_eq,
    (root.toAuthoritativeRoot.toRoot.anchor_commutes visit.current).trans
      (congrArg N.anchorAt rootSupport_eq),
    (root.toAuthoritativeRoot.toRoot.incidence_commutes visit.current).trans
      (congrArg N.incidenceAt rootSupport_eq),
    (root.toAuthoritativeRoot.toRoot.lineage_commutes visit.current).trans
      (congrArg N.lineageAt rootSupport_eq)⟩

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
