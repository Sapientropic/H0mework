import H0mework.Arithmetic.SourceAdmission.A6P506CanonicalLineageReference
import H0mework.Arithmetic.ProjectionDefect.GeneratedObservedDefectEntryGate

/-!
# Observable P506/L0 physical-admission core

This is the dependency-light admission seam for the actual nonzero-phase
`(5,7,E=8)` source.  Unlike the older canonical residual tower, it does not
replace the source by a fixed-left zero-phase family.  Source evidence is the
gauge-invariant observable P506/L0 lineage itself, together with the positivity
needed to derive its left-anchor endpoint through the existing A6 grammar.

An external physical producer may choose any credential Type, but every
exported credential must read back to the exact canonical observable lineage.
The resulting `GeneratedObservedSourceAdmission` is at shell seven and retains
the source cochain, sigma tag, producer lineage, and generated endpoint.

This module imports no FactorHolonomy object and contains no endpoint atomhood,
Boolean atomicity, primitive law, arithmetic missing shadow, or self-admission
owner.  Endpoint `11` is a derived readout of exact lineage, not an admission
field.
-/

namespace RepresentationArithmeticAtomProjectionDefect
namespace BorromeanPreRealization

open A6CrystalObservedSourceTrace
open NativeTraceHardDoor
open SaturationMonoid.StandardModelConstraint

noncomputable section

/-- Exact observable lineage plus the source-height fact needed by the
left-anchor grammar. -/
structure P506ObservableSourceEvidence where
  lineage : P506SourceAffineL0ObservableLineageReference
  height_pos : 0 < su7A6SignedHeight lineage.sourceLabel

@[ext] theorem P506ObservableSourceEvidence.ext
    (left right : P506ObservableSourceEvidence)
    (lineage : left.lineage = right.lineage) :
    left = right := by
  cases left
  cases right
  simp_all

namespace P506ObservableSourceEvidence

/-- The endpoint target is generated from the evidence's source label by the
existing left-anchor grammar. -/
def endpointTarget (evidence : P506ObservableSourceEvidence) :
    SU7A6WeightLabel :=
  evidence.lineage.leftAnchorTarget evidence.height_pos

/-- Raw endpoint pair derived from that generated target. -/
def endpointCodePair (evidence : P506ObservableSourceEvidence) :
    EndpointCodePair 10 where
  leftCode :=
    su7A6ConcreteEndpointSourceGrammar.leftCodeOf evidence.endpointTarget
  rightCode :=
    su7A6ConcreteEndpointSourceGrammar.rightCodeOf evidence.endpointTarget

/-- Distinguished evidence owned by the actual P506 source trace. -/
def canonical : P506ObservableSourceEvidence where
  lineage := canonicalP506SourceAffineL0ObservableLineageReference
  height_pos :=
    canonicalP506SourceAffineL0ObservableLineageReference_height_pos

@[simp] theorem canonical_lineage :
    canonical.lineage =
      canonicalP506SourceAffineL0ObservableLineageReference :=
  rfl

theorem canonical_endpointTarget :
    canonical.endpointTarget = canonicalP506SourceAffineL0Target := by
  unfold endpointTarget canonical canonicalP506SourceAffineL0Target
    P506SourceAffineL0ObservableLineageReference.leftAnchorTarget
  change
    su7A6EndpointLeftAnchorCompletionTarget
        su7A6FiveSevenSourceLabel _ =
      su7A6EndpointLeftAnchorCompletionTarget
        su7A6FiveSevenSourceLabel _
  rfl

@[simp] theorem canonical_endpointCodePair_left :
    canonical.endpointCodePair.leftCode = 2 := by
  rw [endpointCodePair, canonical_endpointTarget,
    canonicalP506SourceAffineL0Target_eq]
  norm_num [su7A6FiveSevenCompletedRepairLabel,
    su7A6ConcreteEndpointSourceGrammar,
    su7A6EndpointSourceLabel_leftCode]

@[simp] theorem canonical_endpointCodePair_right :
    canonical.endpointCodePair.rightCode = 11 := by
  rw [endpointCodePair, canonical_endpointTarget]
  exact canonicalP506SourceAffineSelectedEndpoint_eq_eleven

@[simp] theorem canonical_endpointCodePair_energy :
    EndpointCodePair.energy canonical.endpointCodePair = 7 := by
  norm_num [EndpointCodePair.energy, EndpointCodePair.residual]

/-- Local residual category for the exact observed source snapshot.  This
admission core claims no residual-lowering edge; descent remains a separate
source-family responsibility. -/
def residualTransport :
    AdditiveResidualTransportCategory P506ObservableSourceEvidence where
  residualEnergy := fun evidence =>
    EndpointCodePair.energy evidence.endpointCodePair
  step := fun _source _target => False
  step_decreases_one := by
    intro _source _target impossible
    exact impossible.elim

/-- Exact-lineage feasibility.  A same-endpoint lookalike with a different
phase cochain is not feasible in this jurisdiction. -/
def representationCategory :
    RepresentationFeasibleCategory P506ObservableSourceEvidence where
  feasible := fun evidence => evidence.lineage = canonical.lineage
  path := Eq
  path_preserves_feasible := by
    intro source target path sourceFeasible
    subst target
    exact sourceFeasible

@[simp] theorem canonical_feasible :
    representationCategory.feasible canonical :=
  rfl

/-- Endpoint-eleven control with the canonical source label but erased phase
cochain. -/
def zeroPhaseLookalike : P506ObservableSourceEvidence where
  lineage := p506EndpointElevenZeroPhaseLineageLookalike
  height_pos := p506EndpointElevenZeroPhaseLineageLookalike_height_pos

@[simp] theorem zeroPhaseLookalike_endpointCodePair_right :
    zeroPhaseLookalike.endpointCodePair.rightCode = 11 := by
  change
    p506EndpointElevenZeroPhaseLineageLookalike.selectedEndpoint
        p506EndpointElevenZeroPhaseLineageLookalike_height_pos = 11
  exact p506EndpointElevenZeroPhaseLineageLookalike_selectedEndpoint

theorem zeroPhaseLookalike_ne_canonical :
    zeroPhaseLookalike ≠ canonical := by
  intro equality
  exact p506EndpointElevenZeroPhaseLineageLookalike_ne_canonical
    (congrArg P506ObservableSourceEvidence.lineage equality)

theorem zeroPhaseLookalike_not_feasible :
    ¬ representationCategory.feasible zeroPhaseLookalike := by
  exact p506EndpointElevenZeroPhaseLineageLookalike_ne_canonical

end P506ObservableSourceEvidence

/-- Source path retaining the exact evidence and its canonical-lineage
identity. -/
structure P506ObservableL0SourcePath where
  evidence : P506ObservableSourceEvidence
  exact_lineage : evidence.lineage =
    canonicalP506SourceAffineL0ObservableLineageReference

/-- Generated-sector identity for the same source evidence. -/
structure P506ObservableGeneratedSector where
  evidence : P506ObservableSourceEvidence
  exact_lineage : evidence.lineage =
    canonicalP506SourceAffineL0ObservableLineageReference

/-- External physical owner.  The credential Type remains opaque to math;
only its exact observable-lineage readout is required here. -/
structure P506ObservablePhysicalAdmissionOwner where
  Credential : Type
  evidence : Credential -> P506ObservableSourceEvidence
  admits_canonical :
    forall credential, evidence credential = P506ObservableSourceEvidence.canonical

namespace P506ObservablePhysicalAdmissionOwner

/-- Build the math-side owner from any external credential family carrying an
exact canonical observable-lineage equality. -/
def ofExactLineage
    (Credential : Type)
    (lineageOf : Credential ->
      P506SourceAffineL0ObservableLineageReference)
    (exact_lineage : forall credential,
      lineageOf credential =
        canonicalP506SourceAffineL0ObservableLineageReference) :
    P506ObservablePhysicalAdmissionOwner where
  Credential := Credential
  evidence := fun credential => {
    lineage := lineageOf credential
    height_pos := by
      rw [exact_lineage credential]
      exact
        canonicalP506SourceAffineL0ObservableLineageReference_height_pos
  }
  admits_canonical := by
    intro credential
    apply P506ObservableSourceEvidence.ext
    exact exact_lineage credential

/-- Any actual credential must expose the canonical `(5,7)` source label.
This is a fieldwise consequence of exact lineage, not a Factor premise. -/
theorem credential_sourceLabel
    (owner : P506ObservablePhysicalAdmissionOwner)
    (credential : owner.Credential) :
    (owner.evidence credential).lineage.sourceLabel =
      su7A6FiveSevenSourceLabel := by
  rw [owner.admits_canonical credential]
  exact canonicalP506SourceAffineL0ObservableLineageReference_sourceLabel

/-- Any actual credential must expose the canonical nonzero phase coefficient
on the selected left-ring edge. -/
theorem credential_phaseCoefficient
    (owner : P506ObservablePhysicalAdmissionOwner)
    (credential : owner.Credential) :
    (owner.evidence credential).lineage.phaseCochain
        (Sum.inl .t0) (Sum.inl .t1) = 1 := by
  rw [owner.admits_canonical credential]
  exact canonicalP506SourceAffineL0ObservableLineageReference_phaseCoefficient

/-- A candidate exporter whose every source label misses `(5,7)` cannot
inhabit the exact-lineage credential Type. -/
theorem no_credential_of_sourceLabel_mismatch
    (owner : P506ObservablePhysicalAdmissionOwner)
    (mismatch : ∀ credential : owner.Credential,
      (owner.evidence credential).lineage.sourceLabel ≠
        su7A6FiveSevenSourceLabel) :
    ¬ Nonempty owner.Credential := by
  rintro ⟨credential⟩
  exact mismatch credential (owner.credential_sourceLabel credential)

/-- Likewise a uniform mismatch on the canonical phase edge makes the
credential Type empty. -/
theorem no_credential_of_phaseCoefficient_mismatch
    (owner : P506ObservablePhysicalAdmissionOwner)
    (mismatch : ∀ credential : owner.Credential,
      (owner.evidence credential).lineage.phaseCochain
          (Sum.inl .t0) (Sum.inl .t1) ≠ 1) :
    ¬ Nonempty owner.Credential := by
  rintro ⟨credential⟩
  exact mismatch credential (owner.credential_phaseCoefficient credential)

/-- Exact-lineage admission rejects the endpoint-eleven zero-phase lookalike.
The result requires an actual credential and is not made true by an empty
credential Type. -/
theorem no_credential_maps_to_zeroPhaseLookalike
    (owner : P506ObservablePhysicalAdmissionOwner) :
    ¬ exists credential : owner.Credential,
      owner.evidence credential =
        P506ObservableSourceEvidence.zeroPhaseLookalike := by
  rintro ⟨credential, lookalike⟩
  apply P506ObservableSourceEvidence.zeroPhaseLookalike_ne_canonical
  exact lookalike.symm.trans (owner.admits_canonical credential)

end P506ObservablePhysicalAdmissionOwner

/-- Jurisdiction tying source path, generated sector, and external credential
to one exact observable source evidence. -/
def p506ObservableSourceAdmissionJurisdiction
    (owner : P506ObservablePhysicalAdmissionOwner) :
    GeneratedSourceAdmissionJurisdiction
      P506ObservableL0SourcePath P506ObservableSourceEvidence where
  GeneratedSector := P506ObservableGeneratedSector
  PhysicalAdmission := owner.Credential
  pathEvidence := P506ObservableL0SourcePath.evidence
  generatedEvidence := P506ObservableGeneratedSector.evidence
  admittedEvidence := owner.evidence

abbrev P506ObservablePhaseTrace :=
  P506SourceAffineL0PhaseNode -> P506SourceAffineL0PhaseNode -> Int

/-- Canonical path through the actual observable source reference. -/
def canonicalP506ObservableL0SourcePath : P506ObservableL0SourcePath where
  evidence := P506ObservableSourceEvidence.canonical
  exact_lineage := rfl

/-- Canonical generated-sector witness before physical admission. -/
def canonicalP506ObservableGeneratedSector :
    P506ObservableGeneratedSector where
  evidence := P506ObservableSourceEvidence.canonical
  exact_lineage := rfl

/-- Positive exact-lineage admission at shell seven.  It can be constructed
only after an external owner exports an actual credential. -/
def p506GeneratedObservedSourceAdmissionOfPhysicalAdmission
    (owner : P506ObservablePhysicalAdmissionOwner)
    (credential : owner.Credential) :
    GeneratedObservedSourceAdmission
      P506ObservableL0SourcePath P506ObservablePhaseTrace Real
      P506SourceAffineL0ObservableLineageReference
      P506ObservableSourceEvidence
      P506ObservableSourceEvidence.residualTransport
      P506ObservableSourceEvidence.representationCategory
      (p506ObservableSourceAdmissionJurisdiction owner)
      10 7 where
  observedDemand := {
    demand := {
      demand := {
        evidence := P506ObservableSourceEvidence.canonical
        residual_eq :=
          P506ObservableSourceEvidence.canonical_endpointCodePair_energy
      }
      feasible := P506ObservableSourceEvidence.canonical_feasible
    }
    trace := {
      sourcePath := canonicalP506ObservableL0SourcePath
      phaseTrace :=
        canonicalP506SourceAffineL0ObservableLineageReference.phaseCochain
      sigmaTag :=
        canonicalP506SourceAffineL0ObservableLineageReference.sigmaTag
      producerTrace :=
        canonicalP506SourceAffineL0ObservableLineageReference
    }
  }
  generatedSector := canonicalP506ObservableGeneratedSector
  physicalAdmission := credential
  sourcePathEvidence_eq := rfl
  generatedEvidence_eq := rfl
  admittedEvidence_eq := owner.admits_canonical credential

/-- The admission preserves exact source/phase/lineage responsibilities and
derives endpoint eleven from that lineage. -/
theorem p506GeneratedObservedSourceAdmission_exact_checkpoint
    (owner : P506ObservablePhysicalAdmissionOwner)
    (credential : owner.Credential) :
    let admission :=
      p506GeneratedObservedSourceAdmissionOfPhysicalAdmission owner credential
    admission.sourceEvidence = P506ObservableSourceEvidence.canonical ∧
      admission.observedDemand.trace.sourcePath.evidence =
        P506ObservableSourceEvidence.canonical ∧
      admission.observedDemand.trace.phaseTrace =
        canonicalP506SourceAffineL0ObservableLineageReference.phaseCochain ∧
      admission.observedDemand.trace.sigmaTag = (1 / 2 : Real) ∧
      admission.observedDemand.trace.producerTrace =
        canonicalP506SourceAffineL0ObservableLineageReference ∧
      admission.generatedSector.evidence =
        P506ObservableSourceEvidence.canonical ∧
      owner.evidence credential = P506ObservableSourceEvidence.canonical ∧
      P506ObservableSourceEvidence.residualTransport.residualEnergy
        admission.sourceEvidence = 7 ∧
      admission.sourceEvidence.endpointCodePair.rightCode = 11 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl,
    owner.admits_canonical credential,
    P506ObservableSourceEvidence.canonical_endpointCodePair_energy,
    P506ObservableSourceEvidence.canonical_endpointCodePair_right⟩

end

end BorromeanPreRealization
end RepresentationArithmeticAtomProjectionDefect
