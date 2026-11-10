import H0mework.Physics.Admission.SU7A6DirectionsStandingAudit

/-!
# Source-backed physical standing contract for the SU7/A6 seven-facet audit

The seven semantic atoms are an audit view of this contract; they do not
define it.  The contract is first assembled as a proof-relevant admission
credential from the concrete source graph, authority, derivation-path,
gauge-field, affine-repair, section-gluing, and temporal data carried by the
native presentation.  Its invariance is then derived from the native physical
operations.  Only afterwards do we prove that the seven Boolean observations
are sound and complete for the selected family of predicates extensionally
equal to this contract.

Exact lineage is deliberately absent from the credential.  It remains in the
relation and reference-relative residual exported by
`SU7A6SevenDirectionStandingAudit`, where distinct admitted states can still be
separated.
-/

namespace SaturationMonoid
namespace PhysicsCore
namespace SU7A6PhysicalStandingContract

open StandardModelConstraint

noncomputable section

abbrev State (scale : RawAffineScaleValidity) :=
  SU7A6SevenDirectionStandingAudit.State scale

/-! ## Contract and physical admission credential -/

/-- A proof-relevant physical admission credential assembled from native
domain data.  None of its fields mentions `SemanticAtom`, `CSafe`, Boolean
queries, or audit expressibility. -/
structure PhysicalAdmissionCredential
    (scale : RawAffineScaleValidity) (state : State scale) : Prop where
  sourcePath : state.six.base.sourceReachable
  authorizedTransport : state.six.authority.StandingAuthorized
  derivationPathsJoin : state.six.base.sourceConfluent
  gaugeTraceExact : ColorLoopTraceExact state.six.base.field
  affineRepairAtTarget : state.six.scaleValue = scale.target
  localSectionsCompatible : state.gluing.Consistent
  temporalWindowOpen : state.six.temporal.StandingFresh

/-- The physical standing contract is the existence of the concrete native
credential above.  It is defined before, and independently of, the seven audit
semantics. -/
def PhysicalStandingContract
    (scale : RawAffineScaleValidity) (state : State scale) : Prop :=
  PhysicalAdmissionCredential scale state

/-- The contract is preserved by the equivalence generated from successful
native physical operations. -/
theorem physicalStandingContract_standingInvariant
    (scale : RawAffineScaleValidity) (hvalid : scale.ScaleValid) :
    StandingInvariant (SU7A6SevenDirectionStandingAudit.identity scale)
      (PhysicalStandingContract scale) := by
  intro source result hstanding
  have hsource :=
    SU7A6SevenDirectionStandingAudit.sourceReachable_standingInvariant
      scale hstanding
  have hauthority :=
    SU7A6SevenDirectionStandingAudit.authorized_standingInvariant
      scale hstanding
  have hpaths :=
    SU7A6SevenDirectionStandingAudit.sourceConfluent_standingInvariant
      scale hstanding
  have hgauge :=
    SU7A6SevenDirectionStandingAudit.traceExact_standingInvariant
      scale hstanding
  have haffine :=
    SU7A6SevenDirectionStandingAudit.contraction_standingInvariant
      scale hvalid hstanding
  have hsections :=
    SU7A6SevenDirectionStandingAudit.gluing_standingInvariant
      scale hstanding
  have htemporal :=
    SU7A6SevenDirectionStandingAudit.freshness_standingInvariant
      scale hstanding
  constructor
  · intro credential
    exact
      { sourcePath := hsource.mp credential.sourcePath
        authorizedTransport :=
          hauthority.mp credential.authorizedTransport
        derivationPathsJoin := hpaths.mp credential.derivationPathsJoin
        gaugeTraceExact := hgauge.mp credential.gaugeTraceExact
        affineRepairAtTarget :=
          haffine.mp credential.affineRepairAtTarget
        localSectionsCompatible :=
          hsections.mp credential.localSectionsCompatible
        temporalWindowOpen := htemporal.mp credential.temporalWindowOpen }
  · intro credential
    exact
      { sourcePath := hsource.mpr credential.sourcePath
        authorizedTransport :=
          hauthority.mpr credential.authorizedTransport
        derivationPathsJoin := hpaths.mpr credential.derivationPathsJoin
        gaugeTraceExact := hgauge.mpr credential.gaugeTraceExact
        affineRepairAtTarget :=
          haffine.mpr credential.affineRepairAtTarget
        localSectionsCompatible :=
          hsections.mpr credential.localSectionsCompatible
        temporalWindowOpen := htemporal.mpr credential.temporalWindowOpen }

/-- Direct native-operation form of contract preservation.  This is the
producer-side theorem used before any audit vocabulary is consulted. -/
theorem physicalStandingContract_nativeMoveInvariant
    (scale : RawAffineScaleValidity) (hvalid : scale.ScaleValid) :
    NativeMoveInvariant
      (SU7A6SevenDirectionStandingAudit.nativeOperations scale)
      (PhysicalStandingContract scale) := by
  intro move source result happlies
  apply physicalStandingContract_standingInvariant scale hvalid
  exact GeneratedStandingEquiv.step move happlies

/-- Standing relevance is generated from the independently defined physical
contract, not from Boolean-query expressibility or from the seven atoms. -/
def physicalStandingRelevance
    (scale : RawAffineScaleValidity) (hvalid : scale.ScaleValid) :
    StandingRelevance
      (SU7A6SevenDirectionStandingAudit.identity scale) where
  relevant := fun target =>
    ∀ state, target state ↔ PhysicalStandingContract scale state
  invariant := by
    intro target htarget source result hstanding
    calc
      target source ↔ PhysicalStandingContract scale source := htarget source
      _ ↔ PhysicalStandingContract scale result :=
        physicalStandingContract_standingInvariant scale hvalid hstanding
      _ ↔ target result := (htarget result).symm

/-! ## Audit view proved after contract generation -/

/-- The independently generated credential has exactly the truth conditions
read by the current seven-facet audit.  This bridge is a theorem, not the
definition of the contract or of relevance. -/
theorem physicalStandingContract_iff_sevenStandingSafe
    (scale : RawAffineScaleValidity) (state : State scale) :
    PhysicalStandingContract scale state ↔
      SU7A6SevenDirectionStandingAudit.SevenStandingSafe scale state := by
  constructor
  · intro credential
    exact
      ⟨credential.sourcePath,
        credential.authorizedTransport,
        credential.derivationPathsJoin,
        credential.gaugeTraceExact,
        credential.affineRepairAtTarget,
        credential.localSectionsCompatible,
        credential.temporalWindowOpen⟩
  · rintro ⟨hsource, hauthority, hpaths, hgauge, haffine,
      hsections, htemporal⟩
    exact
      { sourcePath := hsource
        authorizedTransport := hauthority
        derivationPathsJoin := hpaths
        gaugeTraceExact := hgauge
        affineRepairAtTarget := haffine
        localSectionsCompatible := hsections
        temporalWindowOpen := htemporal }

theorem physicalStandingContract_iff_csafe
    (scale : RawAffineScaleValidity) (state : State scale) :
    PhysicalStandingContract scale state ↔
      CSafe (SU7A6SevenDirectionStandingAudit.predicates scale) state :=
  (physicalStandingContract_iff_sevenStandingSafe scale state).trans
    (SU7A6SevenDirectionStandingAudit.sevenStandingSafe_iff_csafe
      scale state)

/-- The already established seven observations are sound for the native
standing identity used by the physical contract. -/
theorem sevenFacetSound
    (scale : RawAffineScaleValidity) (hvalid : scale.ScaleValid) :
    StandingAuditSound
      (SU7A6SevenDirectionStandingAudit.identity scale)
      (SU7A6SevenDirectionStandingAudit.semantics scale) :=
  SU7A6SevenDirectionStandingAudit.auditSound scale hvalid

/-- Agreement on the seven audit observations preserves every predicate in
the independently generated physical-standing relevance family. -/
theorem sevenFacetCoverage
    (scale : RawAffineScaleValidity) (hvalid : scale.ScaleValid) :
    AtomCoverageCertificate
      (SU7A6SevenDirectionStandingAudit.semantics scale)
      (physicalStandingRelevance scale hvalid).relevant where
  invariant := by
    intro target htarget source result hatoms
    have hsource := hatoms SemanticAtom.sourceReachability
    have hauthority := hatoms SemanticAtom.authorityMonotonicity
    have hpaths := hatoms SemanticAtom.graphConfluence
    have hgauge := hatoms SemanticAtom.gaugeInvariance
    have haffine := hatoms SemanticAtom.contractionCertification
    have hsections := hatoms SemanticAtom.omegaGluing
    have htemporal := hatoms SemanticAtom.freshnessValidity
    have hsafe :
        SU7A6SevenDirectionStandingAudit.SevenStandingSafe scale source ↔
          SU7A6SevenDirectionStandingAudit.SevenStandingSafe
            scale result := by
      constructor
      · rintro ⟨hs, ha, hp, hg, hx, hl, ht⟩
        exact ⟨hsource.mp hs, hauthority.mp ha, hpaths.mp hp,
          hgauge.mp hg, haffine.mp hx, hsections.mp hl,
          htemporal.mp ht⟩
      · rintro ⟨hs, ha, hp, hg, hx, hl, ht⟩
        exact ⟨hsource.mpr hs, hauthority.mpr ha, hpaths.mpr hp,
          hgauge.mpr hg, haffine.mpr hx, hsections.mpr hl,
          htemporal.mpr ht⟩
    have hcontract :
        PhysicalStandingContract scale source ↔
          PhysicalStandingContract scale result :=
      (physicalStandingContract_iff_sevenStandingSafe scale source).trans
        (hsafe.trans
          (physicalStandingContract_iff_sevenStandingSafe
            scale result).symm)
    exact (htarget source).trans (hcontract.trans (htarget result).symm)

theorem finiteCompleteForPhysicalStandingRelevance
    (scale : RawAffineScaleValidity) (hvalid : scale.ScaleValid) :
    FiniteFacetCompleteFor
      (SU7A6SevenDirectionStandingAudit.semantics scale)
      (physicalStandingRelevance scale hvalid).relevant := by
  classical
  exact
    (finiteFacetCompleteFor_standingRelevance_iff_atomCoverage
      (SU7A6SevenDirectionStandingAudit.identity scale)
      (physicalStandingRelevance scale hvalid)
      (SU7A6SevenDirectionStandingAudit.semantics scale)).mpr
        (sevenFacetCoverage scale hvalid)

/-- The physical credential is the downstream admission object.  Mathematics
may consume it without receiving a lineage-erasing endpoint-realization or
atomhood certificate. -/
theorem auditSafe_of_physicalAdmissionCredential
    (scale : RawAffineScaleValidity) {state : State scale}
    (credential : PhysicalAdmissionCredential scale state) :
    CSafe (SU7A6SevenDirectionStandingAudit.predicates scale) state :=
  (physicalStandingContract_iff_csafe scale state).mp credential

theorem physicalAdmissionCredential_of_auditSafe
    (scale : RawAffineScaleValidity) {state : State scale}
    (hsafe :
      CSafe (SU7A6SevenDirectionStandingAudit.predicates scale) state) :
    PhysicalAdmissionCredential scale state :=
  (physicalStandingContract_iff_csafe scale state).mpr hsafe

end
end SU7A6PhysicalStandingContract
end PhysicsCore
end SaturationMonoid
