import H0mework.Arithmetic.SourceAtoms.A6FiveSevenObservedTraceCore
import H0mework.Arithmetic.ShellSources.RepresentationRepair

/-!
# Dependency-light canonical P506/L0 lineage references

The gauge-fixed full `(5,7,E=8)` A6/L0 trace remains available for internal
math proofs.  A physical adapter, however, should not compare absolute phase
potentials: only their cochain is observable, and a constant gauge shift must
not change lineage.  This file therefore also supplies a fieldwise observable
reference containing the A6 root/current move multiset, current label,
producer depth, branch/incidence, current phase cochain, and sigma tag.

The selected endpoint is read from the trace-owned current A6 label through
the existing left-anchor grammar and proved equal to `11`.  No P506 carrier,
Factor import, atomhood theorem, physical credential, arithmetic missing
shadow, or unbounded-family claim occurs in this dependency-light layer.
-/

namespace RepresentationArithmeticAtomProjectionDefect
namespace BorromeanPreRealization

open A6CrystalObservedSourceTrace
open SaturationMonoid.StandardModelConstraint

noncomputable section

/-- Gauge-fixed math trace retained for internal source/grammar proofs.

This is stronger than the recommended physical equality because it compares
the absolute phase potential as well as its observable cochain. -/
abbrev P506SourceAffineL0LineageReference :=
  A6CrystalObservedSourceTrace Real (1 / 2 : Real) 10

/-- Distinguished reference used by the fixed source-affine P506 proof. -/
def canonicalP506SourceAffineL0LineageReference :
    P506SourceAffineL0LineageReference :=
  n10FiveSevenObservedTrace

/-! ## Observable exact-lineage reference -/

abbrev P506SourceAffineL0PhaseNode :=
  Sum PreRealizationThreeCycleTime PreRealizationThreeCycleTime

/-- Gauge-invariant current-state receipt suitable for a physical exact-lineage
readout.  It deliberately contains no selected endpoint field: that number is
derived from `sourceLabel` by the existing grammar. -/
structure P506SourceAffineL0ObservableLineageReference where
  rootLabel : SU7A6WeightLabel
  rootMoves : Multiset (Fin 6)
  producerDepth : Nat
  rootMoves_card : rootMoves.card = producerDepth
  sourceLabel : SU7A6WeightLabel
  branch : PreRealizationSU3Branch
  incidence : PreRealizationSU7Incidence
  phaseCochain :
    P506SourceAffineL0PhaseNode -> P506SourceAffineL0PhaseNode -> Int
  sigmaTag : Real

@[ext] theorem P506SourceAffineL0ObservableLineageReference.ext
    (left right : P506SourceAffineL0ObservableLineageReference)
    (rootLabel : left.rootLabel = right.rootLabel)
    (rootMoves : left.rootMoves = right.rootMoves)
    (sourceLabel : left.sourceLabel = right.sourceLabel)
    (producerDepth : left.producerDepth = right.producerDepth)
    (branch : left.branch = right.branch)
    (incidence : left.incidence = right.incidence)
    (phaseCochain : left.phaseCochain = right.phaseCochain)
    (sigmaTag : left.sigmaTag = right.sigmaTag) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Read only current observable fields from a gauge-fixed trace. -/
noncomputable def p506SourceAffineL0ObservableLineageReferenceOfTrace
    (trace : P506SourceAffineL0LineageReference) :
    P506SourceAffineL0ObservableLineageReference where
  rootLabel := trace.rootLabel
  rootMoves :=
    Multiset.ofList
      (List.ofFn fun index : Fin trace.currentDepth =>
        trace.rootAt index)
  producerDepth := trace.currentDepth
  rootMoves_card := by simp
  sourceLabel := trace.labelAt trace.currentDepth
  branch := trace.branch
  incidence := trace.incidence
  phaseCochain := trace.phaseCochainAt trace.currentDepth
  sigmaTag := 1 / 2

/-- Depthwise constant gauge shift of the absolute potential. -/
noncomputable def p506SourceAffineL0GaugeShiftTrace
    (trace : P506SourceAffineL0LineageReference)
    (shift : Nat -> Int) : P506SourceAffineL0LineageReference where
  sigma_pos := trace.sigma_pos
  sigma_lt_one := trace.sigma_lt_one
  rootLabel := trace.rootLabel
  rootAt := trace.rootAt
  currentDepth := trace.currentDepth
  branch := trace.branch
  incidence := trace.incidence
  phasePotentialOf := fun depth node =>
    trace.phasePotentialOf depth node + shift depth

/-- The observable reference forgets absolute-potential gauge shifts while
retaining the exact current cochain. -/
theorem p506SourceAffineL0ObservableLineageReferenceOfGaugeShift_eq
    (trace : P506SourceAffineL0LineageReference)
    (shift : Nat -> Int) :
    p506SourceAffineL0ObservableLineageReferenceOfTrace
        (p506SourceAffineL0GaugeShiftTrace trace shift) =
      p506SourceAffineL0ObservableLineageReferenceOfTrace trace := by
  apply P506SourceAffineL0ObservableLineageReference.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · funext source target
    simp [p506SourceAffineL0ObservableLineageReferenceOfTrace,
      p506SourceAffineL0GaugeShiftTrace,
      A6CrystalObservedSourceTrace.phaseCochainAt]
  · rfl

/-- Authoritative observable reference for a future physical readout. -/
noncomputable def canonicalP506SourceAffineL0ObservableLineageReference :
    P506SourceAffineL0ObservableLineageReference :=
  p506SourceAffineL0ObservableLineageReferenceOfTrace
    canonicalP506SourceAffineL0LineageReference

namespace P506SourceAffineL0ObservableLineageReference

/-- Grammar target derived from the observable source label. -/
noncomputable def leftAnchorTarget
    (reference : P506SourceAffineL0ObservableLineageReference)
    (height_pos : 0 < su7A6SignedHeight reference.sourceLabel) :
    SU7A6WeightLabel :=
  su7A6EndpointLeftAnchorCompletionTarget
    reference.sourceLabel height_pos

/-- Endpoint readout derived from the observable source label. -/
noncomputable def selectedEndpoint
    (reference : P506SourceAffineL0ObservableLineageReference)
    (height_pos : 0 < su7A6SignedHeight reference.sourceLabel) : Nat :=
  su7A6ConcreteEndpointSourceGrammar.rightCodeOf
    (reference.leftAnchorTarget height_pos)

end P506SourceAffineL0ObservableLineageReference

@[simp] theorem canonicalP506SourceAffineL0ObservableLineageReference_sourceLabel :
    canonicalP506SourceAffineL0ObservableLineageReference.sourceLabel =
      su7A6FiveSevenSourceLabel := by
  rfl

@[simp] theorem canonicalP506SourceAffineL0ObservableLineageReference_rootLabel :
    canonicalP506SourceAffineL0ObservableLineageReference.rootLabel =
      su7A6FiveSevenSourceLabel := by
  rfl

@[simp] theorem canonicalP506SourceAffineL0ObservableLineageReference_rootMoves :
    canonicalP506SourceAffineL0ObservableLineageReference.rootMoves = 0 := by
  simp [canonicalP506SourceAffineL0ObservableLineageReference,
    p506SourceAffineL0ObservableLineageReferenceOfTrace,
    canonicalP506SourceAffineL0LineageReference,
    n10FiveSevenObservedTrace]

@[simp] theorem canonicalP506SourceAffineL0ObservableLineageReference_producerDepth :
    canonicalP506SourceAffineL0ObservableLineageReference.producerDepth = 0 := by
  rfl

@[simp] theorem canonicalP506SourceAffineL0ObservableLineageReference_phaseCoefficient :
    canonicalP506SourceAffineL0ObservableLineageReference.phaseCochain
        (Sum.inl .t0) (Sum.inl .t1) = 1 := by
  exact n10FiveSevenObservedTrace_phaseCochain_nonzero

/-- Fieldwise exact-lineage hard door: a source-label mismatch already rules
out the canonical observable reference, independently of endpoint readout. -/
theorem P506SourceAffineL0ObservableLineageReference.ne_canonical_of_sourceLabel_ne
    (reference : P506SourceAffineL0ObservableLineageReference)
    (sourceLabel_ne : reference.sourceLabel ≠ su7A6FiveSevenSourceLabel) :
    reference ≠ canonicalP506SourceAffineL0ObservableLineageReference := by
  intro equality
  apply sourceLabel_ne
  rw [equality]
  exact canonicalP506SourceAffineL0ObservableLineageReference_sourceLabel

/-- Fieldwise exact-lineage hard door at one canonical nonzero phase edge. -/
theorem P506SourceAffineL0ObservableLineageReference.ne_canonical_of_phaseCoefficient_ne
    (reference : P506SourceAffineL0ObservableLineageReference)
    (phaseCoefficient_ne :
      reference.phaseCochain (Sum.inl .t0) (Sum.inl .t1) ≠ 1) :
    reference ≠ canonicalP506SourceAffineL0ObservableLineageReference := by
  intro equality
  apply phaseCoefficient_ne
  rw [equality]
  exact canonicalP506SourceAffineL0ObservableLineageReference_phaseCoefficient

theorem canonicalP506SourceAffineL0ObservableLineageReference_height_pos :
    0 < su7A6SignedHeight
      canonicalP506SourceAffineL0ObservableLineageReference.sourceLabel := by
  rw [canonicalP506SourceAffineL0ObservableLineageReference_sourceLabel]
  norm_num [su7A6SignedHeight, su7A6FiveSevenSourceLabel,
    su7A6EndpointSourceLabel, su7A6EndpointSourceEnergyCorrection]

@[simp] theorem canonicalP506SourceAffineL0ObservableLineageReference_selectedEndpoint :
    canonicalP506SourceAffineL0ObservableLineageReference.selectedEndpoint
        canonicalP506SourceAffineL0ObservableLineageReference_height_pos = 11 := by
  norm_num [P506SourceAffineL0ObservableLineageReference.selectedEndpoint,
    P506SourceAffineL0ObservableLineageReference.leftAnchorTarget,
    canonicalP506SourceAffineL0ObservableLineageReference,
    p506SourceAffineL0ObservableLineageReferenceOfTrace,
    canonicalP506SourceAffineL0LineageReference,
    n10FiveSevenObservedTrace, A6CrystalObservedSourceTrace.labelAt,
    a6CrystalLabelAlongTrace, su7A6FiveSevenSourceLabel,
    su7A6EndpointLeftAnchorCompletionTarget,
    su7A6ConcreteEndpointSourceGrammar,
    su7A6EndpointSourceLabel_leftCode,
    su7A6EndpointSourceLabel_rightCode,
    su7A6EndpointSourceLabel_signedHeight]

/-- Endpoint-only lookalike: it has the same A6 label and therefore endpoint
`11`, but erases the nonzero phase cochain. -/
noncomputable def p506EndpointElevenZeroPhaseLineageLookalike :
    P506SourceAffineL0ObservableLineageReference :=
  { canonicalP506SourceAffineL0ObservableLineageReference with
    phaseCochain := fun _ _ => 0 }

theorem p506EndpointElevenZeroPhaseLineageLookalike_height_pos :
    0 < su7A6SignedHeight
      p506EndpointElevenZeroPhaseLineageLookalike.sourceLabel := by
  simpa [p506EndpointElevenZeroPhaseLineageLookalike] using
    canonicalP506SourceAffineL0ObservableLineageReference_height_pos

@[simp] theorem p506EndpointElevenZeroPhaseLineageLookalike_selectedEndpoint :
    p506EndpointElevenZeroPhaseLineageLookalike.selectedEndpoint
        p506EndpointElevenZeroPhaseLineageLookalike_height_pos = 11 := by
  change
    canonicalP506SourceAffineL0ObservableLineageReference.selectedEndpoint _ = 11
  exact canonicalP506SourceAffineL0ObservableLineageReference_selectedEndpoint

theorem p506EndpointElevenZeroPhaseLineageLookalike_ne_canonical :
    p506EndpointElevenZeroPhaseLineageLookalike ≠
      canonicalP506SourceAffineL0ObservableLineageReference := by
  apply
    p506EndpointElevenZeroPhaseLineageLookalike.ne_canonical_of_phaseCoefficient_ne
  norm_num [p506EndpointElevenZeroPhaseLineageLookalike]

@[simp] theorem canonicalP506SourceAffineL0LineageReference_currentEnergy :
    canonicalP506SourceAffineL0LineageReference.currentEnergy = 8 := by
  exact n10FiveSevenObservedTrace_currentEnergy

theorem canonicalP506SourceAffineL0LineageReference_energyFloor :
    2 ≤ canonicalP506SourceAffineL0LineageReference.currentEnergy := by
  rw [canonicalP506SourceAffineL0LineageReference_currentEnergy]
  norm_num

/-- Current A6 label read from the complete canonical trace. -/
def canonicalP506SourceAffineL0SourceLabel : SU7A6WeightLabel :=
  canonicalP506SourceAffineL0LineageReference.labelAt
    canonicalP506SourceAffineL0LineageReference.currentDepth

@[simp] theorem canonicalP506SourceAffineL0SourceLabel_eq :
    canonicalP506SourceAffineL0SourceLabel =
      su7A6FiveSevenSourceLabel := by
  rfl

theorem canonicalP506SourceAffineL0SourceLabel_signedHeight_pos :
    0 < su7A6SignedHeight canonicalP506SourceAffineL0SourceLabel := by
  rw [canonicalP506SourceAffineL0SourceLabel_eq]
  norm_num [su7A6SignedHeight, su7A6FiveSevenSourceLabel,
    su7A6EndpointSourceLabel, su7A6EndpointSourceEnergyCorrection]

/-- Left-anchor grammar target selected from the canonical trace-owned source
label. -/
def canonicalP506SourceAffineL0Target : SU7A6WeightLabel :=
  su7A6EndpointLeftAnchorCompletionTarget
    canonicalP506SourceAffineL0SourceLabel
    canonicalP506SourceAffineL0SourceLabel_signedHeight_pos

theorem canonicalP506SourceAffineL0Target_eq :
    canonicalP506SourceAffineL0Target =
      su7A6FiveSevenCompletedRepairLabel := by
  unfold canonicalP506SourceAffineL0Target
  change
    su7A6EndpointLeftAnchorCompletionTarget
        su7A6FiveSevenSourceLabel _ =
      su7A6FiveSevenCompletedRepairLabel
  exact
    su7A6FiveSevenEndpointLeftAnchorCompletionTarget_eq_completedRepairLabel
      canonicalP506SourceAffineL0SourceLabel_signedHeight_pos

/-- Endpoint readout owned by the canonical source trace. -/
def canonicalP506SourceAffineSelectedEndpoint : Nat :=
  su7A6ConcreteEndpointSourceGrammar.rightCodeOf
    canonicalP506SourceAffineL0Target

@[simp] theorem canonicalP506SourceAffineSelectedEndpoint_eq_eleven :
    canonicalP506SourceAffineSelectedEndpoint = 11 := by
  rw [canonicalP506SourceAffineSelectedEndpoint,
    canonicalP506SourceAffineL0Target_eq]
  norm_num [su7A6FiveSevenCompletedRepairLabel,
    su7A6ConcreteEndpointSourceGrammar,
    su7A6EndpointSourceLabel_rightCode]

/-- Positive-only lineage receipt available to physical adapters. -/
theorem canonicalP506SourceAffineL0LineageReference_sourceCheckpoint :
    canonicalP506SourceAffineL0LineageReference =
        n10FiveSevenObservedTrace ∧
      canonicalP506SourceAffineL0SourceLabel =
        su7A6FiveSevenSourceLabel ∧
      canonicalP506SourceAffineL0Target =
        su7A6FiveSevenCompletedRepairLabel ∧
      canonicalP506SourceAffineSelectedEndpoint = 11 :=
  ⟨rfl, canonicalP506SourceAffineL0SourceLabel_eq,
    canonicalP506SourceAffineL0Target_eq,
    canonicalP506SourceAffineSelectedEndpoint_eq_eleven⟩

end

end BorromeanPreRealization
end RepresentationArithmeticAtomProjectionDefect
