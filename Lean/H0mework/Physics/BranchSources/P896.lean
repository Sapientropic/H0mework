import H0mework.Physics.RepresentationSources.P895
import H0mework.Physics.RepresentationSources.P790

/-!
# Proposition 896: SU(7) branching decompositions generate support slots

P895 lowered physical branch families to representation support spectra, but a
support slot still stored full physical atoms.  This file pushes one layer
lower: a branching-decomposition cell stores only

* an SU(7) block incidence from the `3+2+1+1` carrier;
* a Schubert branch label of the color orbit;
* two raw SU(7) weight codes.

It stores no `Nat.Prime`, no `PrimeExponent`, no Goldbach pair, and no physical
support slot.  The block incidence determines the color/weak/hypercharge
sectors through the no-free endpoint-signature schedule of P790; the raw
weight codes become SU(7) atoms; those atoms generate the P895 support slot.

Thus the producer spine is extended:

`SU(7) incidence branching decomposition -> representation support spectrum
 -> physical branch family -> zero residual cell -> prime-edge readout`.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Branching-decomposition cells below support slots -/

/-- Read the Standard-Model-facing sector of one SU(7) carrier block. -/
def sectorOfSU7CarrierBlock :
    SU7CarrierBlock -> ColorWeakHyperchargeSector
  | .color => .color
  | .weak => .weak
  | .positiveSinglet => .hypercharge
  | .negativeSinglet => .antiHypercharge

/-- A physical atom generated from a raw weight code and a carrier-block
endpoint.  No primality proof is stored here. -/
def su7AtomOfBranchingEndpoint
    (code : ℕ) (block : SU7CarrierBlock) : SU7Atom where
  weight := { code := code }
  irreducible := trivial
  sector := sectorOfSU7CarrierBlock block

/-- A generated branching-decomposition cell over an even fiber.

The cell does not store physical atoms, color loops, prime exponents, or prime
proofs.  It stores only incidence / branch / raw weight-code data. -/
structure SU7BranchingDecompositionCell (n : ℕ) where
  branch : SU3FlagSchubertCell
  incidence : SU7BlockIncidence
  leftWeightCode : ℕ
  rightWeightCode : ℕ
  deriving DecidableEq

/-- The generated matter/Higgs slot of a branching-decomposition cell. -/
def generatedSlotOfBranchingDecompositionCell
    {n : ℕ} (c : SU7BranchingDecompositionCell n) :
    SU7GeneratedCarrierSlot :=
  generatedSlotOfIncidence c.incidence

/-- THEOREM 1: the generated slot of a decomposition cell has exactly the
endpoint signature of its incidence.  This is the no-free SU(7) schedule
entering the branch producer. -/
theorem branchingDecompositionCell_endpointSignature
    {n : ℕ} (c : SU7BranchingDecompositionCell n) :
    generatedSlotEndpointSignature
        (generatedSlotOfBranchingDecompositionCell c) =
      SU7BlockIncidence.endpoints c.incidence := by
  exact generatedSlotOfIncidence_endpointSignature c.incidence

/-- Left atom generated from the left endpoint of the incidence. -/
def leftAtomOfBranchingDecompositionCell
    {n : ℕ} (c : SU7BranchingDecompositionCell n) : SU7Atom :=
  su7AtomOfBranchingEndpoint
    c.leftWeightCode (SU7BlockIncidence.endpoints c.incidence).1

/-- Right atom generated from the right endpoint of the incidence. -/
def rightAtomOfBranchingDecompositionCell
    {n : ℕ} (c : SU7BranchingDecompositionCell n) : SU7Atom :=
  su7AtomOfBranchingEndpoint
    c.rightWeightCode (SU7BlockIncidence.endpoints c.incidence).2

/-- Color loop generated from a branching-decomposition cell. -/
def colorLoopOfBranchingDecompositionCell
    {n : ℕ} (c : SU7BranchingDecompositionCell n) : SU7ColorLoop where
  fiber := n
  leftAtom := leftAtomOfBranchingDecompositionCell c
  rightAtom := rightAtomOfBranchingDecompositionCell c

/-- THEOREM 2: the generated color loop is gauge-allowed at the physical
wrapper level.  The concrete confinement law is imposed later as the
no-permanent-holonomy condition, not as a prime predicate. -/
theorem colorLoopOfBranchingDecompositionCell_allowed
    {n : ℕ} (c : SU7BranchingDecompositionCell n) :
    GaugeAllowed (colorLoopOfBranchingDecompositionCell c) := by
  trivial

/-- Representation support slot generated from a branching-decomposition
cell. -/
def representationSupportSlot_of_branchingDecompositionCell
    {n : ℕ} (c : SU7BranchingDecompositionCell n) :
    SU7PhysicalRepresentationSupportSlot n where
  branch := c.branch
  leftAtom := leftAtomOfBranchingDecompositionCell c
  rightAtom := rightAtomOfBranchingDecompositionCell c
  colorLoop := colorLoopOfBranchingDecompositionCell c
  allowed := colorLoopOfBranchingDecompositionCell_allowed c
  loop_fiber := rfl
  loop_left := rfl
  loop_right := rfl

/-- THEOREM 3: the generated support slot has the left atom computed from the
left incidence endpoint. -/
@[simp] theorem representationSupportSlot_of_branching_leftAtom
    {n : ℕ} (c : SU7BranchingDecompositionCell n) :
    (representationSupportSlot_of_branchingDecompositionCell c).leftAtom =
      leftAtomOfBranchingDecompositionCell c := rfl

/-- THEOREM 4: the generated support slot has the right atom computed from the
right incidence endpoint. -/
@[simp] theorem representationSupportSlot_of_branching_rightAtom
    {n : ℕ} (c : SU7BranchingDecompositionCell n) :
    (representationSupportSlot_of_branchingDecompositionCell c).rightAtom =
      rightAtomOfBranchingDecompositionCell c := rfl

/-- Physical branch-spectrum cell generated directly from a
branching-decomposition cell. -/
def physicalBranchingSpectrumCell_of_branchingDecompositionCell
    {n : ℕ} (c : SU7BranchingDecompositionCell n) :
    SU7PhysicalBranchingSpectrumCell n :=
  physicalBranchingSpectrumCell_of_representationSupportSlot
    (representationSupportSlot_of_branchingDecompositionCell c)

/-- Prime-edge branch cell projected from a branching-decomposition cell.

The input stores only incidence / branch / raw weight-code data.  Primality is
generated by the P892/P879 faithful atom readout. -/
def primeEdgeBranchCell_of_branchingDecompositionCell
    {n : ℕ} (c : SU7BranchingDecompositionCell n) :
    SU7PrimeEdgeBranchCell n :=
  primeEdgeBranchCell_of_physicalBranchingSpectrumCell
    (physicalBranchingSpectrumCell_of_branchingDecompositionCell c)

/-- THEOREM 5: the left projected edge of a decomposition cell is prime. -/
theorem branchingDecompositionCell_leftPrime_generated
    {n : ℕ} (c : SU7BranchingDecompositionCell n) :
    Nat.Prime
      (primeEdgeBranchCell_of_branchingDecompositionCell c).leftPrime.1 := by
  exact
    physicalBranchingSpectrumCell_leftPrime_generated
      (physicalBranchingSpectrumCell_of_branchingDecompositionCell c)

/-- THEOREM 6: the right projected edge of a decomposition cell is prime. -/
theorem branchingDecompositionCell_rightPrime_generated
    {n : ℕ} (c : SU7BranchingDecompositionCell n) :
    Nat.Prime
      (primeEdgeBranchCell_of_branchingDecompositionCell c).rightPrime.1 := by
  exact
    physicalBranchingSpectrumCell_rightPrime_generated
      (physicalBranchingSpectrumCell_of_branchingDecompositionCell c)

/-- THEOREM 7: direct prime-edge projection preserves the decomposition
residual. -/
theorem branchWeightResidual_branchingDecompositionProjection_eq
    {n : ℕ} (c : SU7BranchingDecompositionCell n) :
    branchWeightResidual
        (primeEdgeBranchCell_of_branchingDecompositionCell c) =
      physicalBranchingSpectrumResidual
        (physicalBranchingSpectrumCell_of_branchingDecompositionCell c) := by
  exact branchWeightResidual_physicalProjection_eq
    (physicalBranchingSpectrumCell_of_branchingDecompositionCell c)

/-- A finite SU(7) branching-decomposition spectrum over one even fiber. -/
structure SU7BranchingDecompositionSpectrum (n : ℕ) where
  cells : List (SU7BranchingDecompositionCell n)

/-- The P895 representation support spectrum generated by a decomposition
spectrum. -/
def representationSupportSpectrum_of_branchingDecompositionSpectrum
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n) :
    SU7PhysicalRepresentationSupportSpectrum n where
  slots :=
    S.cells.map representationSupportSlot_of_branchingDecompositionCell

/-- THEOREM 5: every decomposition cell maps to a support slot in the generated
support spectrum. -/
theorem branchingDecompositionCell_mem_generatedSupportSpectrum
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    {c : SU7BranchingDecompositionCell n}
    (hc : c ∈ S.cells) :
    representationSupportSlot_of_branchingDecompositionCell c ∈
      (representationSupportSpectrum_of_branchingDecompositionSpectrum
        S).slots := by
  exact List.mem_map.mpr ⟨c, hc, rfl⟩

/-! ## Decomposition-level permanent holonomy -/

/-- Residual of a decomposition cell after its generated support slot is read
through P895/P884. -/
def branchingDecompositionResidual
    {n : ℕ} (c : SU7BranchingDecompositionCell n) : ℤ :=
  physicalBranchingSpectrumResidual
    (physicalBranchingSpectrumCell_of_representationSupportSlot
      (representationSupportSlot_of_branchingDecompositionCell c))

/-- Residual energy of a decomposition cell. -/
def branchingDecompositionResidualEnergy
    {n : ℕ} (c : SU7BranchingDecompositionCell n) : ℕ :=
  Int.natAbs (branchingDecompositionResidual c)

/-- Permanent holonomy at the branching-decomposition level. -/
def SU7BranchingDecompositionPermanentHolonomyCell
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    (c : SU7BranchingDecompositionCell n) : Prop :=
  c ∈ S.cells ∧
    branchingDecompositionResidual c ≠ 0 ∧
      ∀ next : SU7BranchingDecompositionCell n,
        next ∈ S.cells ->
          ¬ branchingDecompositionResidualEnergy next <
            branchingDecompositionResidualEnergy c

/-- A decomposition spectrum forbids permanent decomposition holonomy. -/
def SU7BranchingDecompositionSpectrumForbidsPermanentHolonomy
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n) : Prop :=
  ∀ c : SU7BranchingDecompositionCell n,
    ¬ SU7BranchingDecompositionPermanentHolonomyCell S c

/-- THEOREM 6: decomposition-level no-permanent-holonomy implies P895
support-slot no-permanent-holonomy for the generated support spectrum. -/
theorem representationSupportForbidsPermanentHolonomy_of_branchingDecomposition
    {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
    (H : SU7BranchingDecompositionSpectrumForbidsPermanentHolonomy S) :
    SU7RepresentationSupportSpectrumForbidsPermanentHolonomy
      (representationSupportSpectrum_of_branchingDecompositionSpectrum S) := by
  intro s hslot
  rcases hslot with ⟨hmem, hnonzero, hterminal⟩
  rcases List.mem_map.mp hmem with ⟨c, hc_mem, hc_eq⟩
  have hcell_nonzero :
      branchingDecompositionResidual c ≠ 0 := by
    simpa [branchingDecompositionResidual, hc_eq] using hnonzero
  have hcell_terminal :
      ∀ next : SU7BranchingDecompositionCell n,
        next ∈ S.cells ->
          ¬ branchingDecompositionResidualEnergy next <
            branchingDecompositionResidualEnergy c := by
    intro next hnext_mem hlt
    have hnext_support :
        representationSupportSlot_of_branchingDecompositionCell next ∈
          (representationSupportSpectrum_of_branchingDecompositionSpectrum
            S).slots :=
      branchingDecompositionCell_mem_generatedSupportSpectrum S hnext_mem
    have hlt_support :
        physicalBranchingSpectrumResidualEnergy
            (physicalBranchingSpectrumCell_of_representationSupportSlot
              (representationSupportSlot_of_branchingDecompositionCell
                next)) <
          physicalBranchingSpectrumResidualEnergy
            (physicalBranchingSpectrumCell_of_representationSupportSlot
              s) := by
      simpa [branchingDecompositionResidualEnergy,
        branchingDecompositionResidual,
        physicalBranchingSpectrumResidualEnergy, hc_eq] using hlt
    exact hterminal
      (representationSupportSlot_of_branchingDecompositionCell next)
      hnext_support hlt_support
  exact H c ⟨hc_mem, hcell_nonzero, hcell_terminal⟩

/-! ## Generated support rules from branching decompositions -/

/-- A branching-decomposition spectrum together with a start cell and
decomposition-level confinement. -/
structure SU7BranchingDecompositionHolonomyConfinementRule (n : ℕ) where
  spectrum : SU7BranchingDecompositionSpectrum n
  startCell : SU7BranchingDecompositionCell n
  start_mem : startCell ∈ spectrum.cells
  forbids_permanent_decomposition_holonomy :
    SU7BranchingDecompositionSpectrumForbidsPermanentHolonomy spectrum

/-- THEOREM 7: a branching-decomposition rule generates P895's representation
support holonomy rule. -/
def representationSupportRule_of_branchingDecompositionRule
    {n : ℕ} (R : SU7BranchingDecompositionHolonomyConfinementRule n) :
    SU7RepresentationSupportHolonomyConfinementRule n where
  spectrum :=
    representationSupportSpectrum_of_branchingDecompositionSpectrum R.spectrum
  startSlot :=
    representationSupportSlot_of_branchingDecompositionCell R.startCell
  start_mem :=
    branchingDecompositionCell_mem_generatedSupportSpectrum
      R.spectrum R.start_mem
  forbids_permanent_slot_holonomy :=
    representationSupportForbidsPermanentHolonomy_of_branchingDecomposition
      R.spectrum R.forbids_permanent_decomposition_holonomy

/-- THEOREM 8: a branching-decomposition rule computes a trace-zero
prime-edge loop through the P896 -> P895 -> P894 -> P893 -> P884 -> P892
projection spine. -/
def traceZeroPrimeEdgeLoop_of_branchingDecompositionRule
    {n : ℕ} (R : SU7BranchingDecompositionHolonomyConfinementRule n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_representationSupportRule
    (representationSupportRule_of_branchingDecompositionRule R)

/-- THEOREM 9: a branching-decomposition rule produces a zero physical
residual cell after the generated support/family projections. -/
theorem exists_zeroCell_of_branchingDecompositionRule
    {n : ℕ} (R : SU7BranchingDecompositionHolonomyConfinementRule n) :
    ∃ Z : SU7PhysicalBranchingSpectrumCell n,
      Z ∈
          (physicalBranchingSpectrumFamily_of_representationSupportSpectrum
            (representationSupportSpectrum_of_branchingDecompositionSpectrum
              R.spectrum)).spectrumCells ∧
        0 <
          (physicalBranchingSpectrumFamily_of_representationSupportSpectrum
            (representationSupportSpectrum_of_branchingDecompositionSpectrum
              R.spectrum)).representationWeight Z ∧
          physicalBranchingSpectrumResidual Z = 0 := by
  exact exists_zeroCell_of_representationSupportRule
    (representationSupportRule_of_branchingDecompositionRule R)

/-! ## Fiberwise branching-decomposition confinement -/

/-- Every even fiber carries a branching-decomposition confinement rule. -/
def SU7BranchingDecompositionHolonomyConfinementRuleEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7BranchingDecompositionHolonomyConfinementRule n)

/-- THEOREM 10: fiberwise branching-decomposition rules generate P895
representation support rules on every even fiber. -/
theorem representationSupportRulesEveryEvenFiber_of_branchingDecompositionRules
    (H : SU7BranchingDecompositionHolonomyConfinementRuleEveryEvenFiber) :
    SU7RepresentationSupportHolonomyConfinementRuleEveryEvenFiber := by
  intro n hn
  let R : SU7BranchingDecompositionHolonomyConfinementRule n :=
    Classical.choice (H n hn)
  exact ⟨representationSupportRule_of_branchingDecompositionRule R⟩

/-- Physical branching-decomposition confinement data.  This is the first
producer layer that mentions only the SU(7) block-incidence branching data and
the global confinement law; it still contains no prime pair data. -/
structure SU7PhysicalBranchingDecompositionConfinement where
  compact_gauge_orbit : SU7CompactGaugeOrbit
  lyapunov_residual_dissipation : SU7LyapunovResidualDissipation
  quantized_spectrum_no_escaping_boundary :
    SU7QuantizedSpectrumNoEscapingBoundary
  incidence_schedule_no_free :
    RunningSigmaBeta.SU7IncidenceScheduleNoFreeCertificate
  branching_decomposition_rules :
    SU7BranchingDecompositionHolonomyConfinementRuleEveryEvenFiber

/-- THEOREM 11: branching-decomposition confinement generates P895 physical
representation support confinement. -/
def representationSupportConfinement_of_branchingDecompositionConfinement
    (D : SU7PhysicalBranchingDecompositionConfinement) :
    SU7PhysicalRepresentationSupportConfinement where
  compact_gauge_orbit := D.compact_gauge_orbit
  lyapunov_residual_dissipation := D.lyapunov_residual_dissipation
  quantized_spectrum_no_escaping_boundary :=
    D.quantized_spectrum_no_escaping_boundary
  representation_support_rules :=
    representationSupportRulesEveryEvenFiber_of_branchingDecompositionRules
      D.branching_decomposition_rules

/-- THEOREM 12: branching-decomposition confinement computes trace-zero
prime-edge loops on every even fiber. -/
def traceZeroPrimeEdgeLoopEveryEvenFiber_of_branchingDecompositionConfinement
    (D : SU7PhysicalBranchingDecompositionConfinement) :
    ∀ n : ℕ, 2 ≤ n -> TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoopEveryEvenFiber_of_representationSupportConfinement
    (representationSupportConfinement_of_branchingDecompositionConfinement D)

/-- THEOREM 13: branching-decomposition confinement gives ordinary even
Goldbach through the non-storing projection chain. -/
theorem evenGoldbach_of_physicalBranchingDecompositionConfinement
    (D : SU7PhysicalBranchingDecompositionConfinement) :
    EvenGoldbachStatement :=
  evenGoldbach_of_physicalRepresentationSupportConfinement
    (representationSupportConfinement_of_branchingDecompositionConfinement D)

/-! ## Certificate -/

/-- P896 certificate: SU(7) block-incidence branching decompositions generate
the P895 support spectra and inherit the no-free incidence schedule. -/
structure SU7BranchingDecompositionProducerCertificate where
  block_to_sector :
    SU7CarrierBlock -> ColorWeakHyperchargeSector
  atom_of_endpoint :
    ℕ -> SU7CarrierBlock -> SU7Atom
  cell_endpoint_signature :
    ∀ {n : ℕ} (c : SU7BranchingDecompositionCell n),
      generatedSlotEndpointSignature
          (generatedSlotOfBranchingDecompositionCell c) =
        SU7BlockIncidence.endpoints c.incidence
  cell_to_support_slot :
    ∀ {n : ℕ}, SU7BranchingDecompositionCell n ->
      SU7PhysicalRepresentationSupportSlot n
  cell_to_physical_branch_cell :
    ∀ {n : ℕ}, SU7BranchingDecompositionCell n ->
      SU7PhysicalBranchingSpectrumCell n
  cell_to_prime_edge :
    ∀ {n : ℕ}, SU7BranchingDecompositionCell n ->
      SU7PrimeEdgeBranchCell n
  projected_left_prime :
    ∀ {n : ℕ} (c : SU7BranchingDecompositionCell n),
      Nat.Prime
        (primeEdgeBranchCell_of_branchingDecompositionCell c).leftPrime.1
  projected_right_prime :
    ∀ {n : ℕ} (c : SU7BranchingDecompositionCell n),
      Nat.Prime
        (primeEdgeBranchCell_of_branchingDecompositionCell c).rightPrime.1
  projection_preserves_residual :
    ∀ {n : ℕ} (c : SU7BranchingDecompositionCell n),
      branchWeightResidual
          (primeEdgeBranchCell_of_branchingDecompositionCell c) =
        physicalBranchingSpectrumResidual
          (physicalBranchingSpectrumCell_of_branchingDecompositionCell c)
  spectrum_to_support_spectrum :
    ∀ {n : ℕ}, SU7BranchingDecompositionSpectrum n ->
      SU7PhysicalRepresentationSupportSpectrum n
  cell_mem_generated_support :
    ∀ {n : ℕ} (S : SU7BranchingDecompositionSpectrum n)
      {c : SU7BranchingDecompositionCell n},
      c ∈ S.cells ->
        representationSupportSlot_of_branchingDecompositionCell c ∈
          (representationSupportSpectrum_of_branchingDecompositionSpectrum
            S).slots
  decomposition_no_holonomy_to_support_no_holonomy :
    ∀ {n : ℕ} (S : SU7BranchingDecompositionSpectrum n),
      SU7BranchingDecompositionSpectrumForbidsPermanentHolonomy S ->
        SU7RepresentationSupportSpectrumForbidsPermanentHolonomy
          (representationSupportSpectrum_of_branchingDecompositionSpectrum S)
  decomposition_rule_to_support_rule :
    ∀ {n : ℕ}, SU7BranchingDecompositionHolonomyConfinementRule n ->
      SU7RepresentationSupportHolonomyConfinementRule n
  decomposition_rule_to_trace_zero :
    ∀ {n : ℕ}, SU7BranchingDecompositionHolonomyConfinementRule n ->
      TraceZeroPrimeEdgeLoop n
  incidence_schedule_no_free :
    RunningSigmaBeta.SU7IncidenceScheduleNoFreeCertificate
  branching_confinement_to_goldbach :
    SU7PhysicalBranchingDecompositionConfinement -> EvenGoldbachStatement

def su7BranchingDecompositionProducerCertificate :
    SU7BranchingDecompositionProducerCertificate where
  block_to_sector := sectorOfSU7CarrierBlock
  atom_of_endpoint := su7AtomOfBranchingEndpoint
  cell_endpoint_signature := branchingDecompositionCell_endpointSignature
  cell_to_support_slot :=
    representationSupportSlot_of_branchingDecompositionCell
  cell_to_physical_branch_cell :=
    physicalBranchingSpectrumCell_of_branchingDecompositionCell
  cell_to_prime_edge :=
    primeEdgeBranchCell_of_branchingDecompositionCell
  projected_left_prime :=
    branchingDecompositionCell_leftPrime_generated
  projected_right_prime :=
    branchingDecompositionCell_rightPrime_generated
  projection_preserves_residual :=
    branchWeightResidual_branchingDecompositionProjection_eq
  spectrum_to_support_spectrum :=
    representationSupportSpectrum_of_branchingDecompositionSpectrum
  cell_mem_generated_support :=
    branchingDecompositionCell_mem_generatedSupportSpectrum
  decomposition_no_holonomy_to_support_no_holonomy :=
    representationSupportForbidsPermanentHolonomy_of_branchingDecomposition
  decomposition_rule_to_support_rule :=
    representationSupportRule_of_branchingDecompositionRule
  decomposition_rule_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_branchingDecompositionRule
  incidence_schedule_no_free :=
    RunningSigmaBeta.su7IncidenceScheduleNoFreeCertificate
  branching_confinement_to_goldbach :=
    evenGoldbach_of_physicalBranchingDecompositionConfinement


end
end StandardModelConstraint
end SaturationMonoid
