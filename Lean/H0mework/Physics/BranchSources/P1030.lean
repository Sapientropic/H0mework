import H0mework.Physics.ColorLoops.P997
import H0mework.Arithmetic.AtomicCodes.P1029

/-!
# Proposition 1030: full-orbit incidence normalizer supplies generated color cells

P1029 made the P710-to-P1028 bridge exact, but its carrier object still carried
the generated color-cell fields.  This file removes that part of the burden.

The full SU(7) incidence-normalizer producer from P993 already gives, for
every active fiber, a generated terminal color cell with zero computed color
residual.  P997 turns that into zero physical trace.  Therefore the remaining
P710-side producer data only has to provide:

* the directed-cycle family and terminal descent laws;
* one additive carrier code on directed cycles;
* a realization of primitive cycles as tensor-irreducible SU(7) atoms.

No endpoint arithmetic, prime-edge object, or Goldbach statement appears here.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open GrandUnification

set_option linter.checkUnivs false
set_option linter.defProp false

universe u v w z

/-! ## Generated cells from the full incidence orbit -/

/-- The generated color cell selected by the full-orbit incidence normalizer.

The selection is by `Classical.choice` from P993's existence theorem; the zero
readouts are still computed from the generated color-loop residual, not stored
inside the cell. -/
def fullOrbitIncidenceGeneratedCell (n : ℕ) :
    SU7GeneratedTerminalColorCell n :=
  Classical.choose (zeroGeneratedColorResidual_of_fullOrbitIncidenceNormalizer n)

theorem fullOrbitIncidenceGeneratedCell_mem (n : ℕ) :
    fullOrbitIncidenceGeneratedCell n ∈
      su7RepresentationFullTerminalColorOrbit n :=
  (Classical.choose_spec
    (zeroGeneratedColorResidual_of_fullOrbitIncidenceNormalizer n)).1

theorem fullOrbitIncidenceGeneratedCell_residual_zero (n : ℕ) :
    generatedTerminalColorResidual (fullOrbitIncidenceGeneratedCell n) = 0 :=
  (Classical.choose_spec
    (zeroGeneratedColorResidual_of_fullOrbitIncidenceNormalizer n)).2

/-- Every generated cell in the full SU(7) representation orbit is gauge
allowed, because the representation-slot generator sets `gaugeAllowed := True`.
-/
theorem sameCarrierGaugeAllowed_of_fullOrbit_mem
    {n : ℕ} {cell : SU7GeneratedTerminalColorCell n}
    (hmem : cell ∈ su7RepresentationFullTerminalColorOrbit n) :
    SameCarrierGaugeAllowed cell := by
  unfold SameCarrierGaugeAllowed
  unfold su7RepresentationFullTerminalColorOrbit
    su7RepresentationFullTerminalCells at hmem
  rcases List.mem_flatMap.mp hmem with ⟨branch, _hbranch, hmap⟩
  rcases List.mem_map.mp hmap with ⟨incidence, _hincidence, rfl⟩
  simp [generatedTerminalColorCellOfRepresentationSlot]

theorem fullOrbitIncidenceGeneratedCell_allowed (n : ℕ) :
    SameCarrierGaugeAllowed (fullOrbitIncidenceGeneratedCell n) :=
  sameCarrierGaugeAllowed_of_fullOrbit_mem
    (fullOrbitIncidenceGeneratedCell_mem n)

/-- The selected full-orbit generated cell has zero physical color trace. -/
theorem fullOrbitIncidenceGeneratedCell_trace_zero (n : ℕ) :
    physicalColorLoopTrace
        (terminalPhysicalCellOfGeneratedColorCell
          (fullOrbitIncidenceGeneratedCell n)) = 0 := by
  have hexact :
      GeneratedTerminalColorLoopExact (fullOrbitIncidenceGeneratedCell n) :=
    generatedColorLoop_exact_of_residual_zero
      (fullOrbitIncidenceGeneratedCell_residual_zero n)
  exact
    physicalColorLoopTrace_eq_zero_of_exact
      (physicalColorLoopExact_of_generated_exact hexact)

/-! ## P710 carrier data after generated-color production is removed -/

/-- P710 three-nail carrier data after the generated color-cell obligation has
been discharged by the full-orbit incidence normalizer.

The remaining fields are exactly the cycle/additive-code/tensor-atom producer
fields. -/
structure SU7ThreeNailCycleAtomCarrierData
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (Clause : Type v) (Var : Type w) [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    (C : SU7WeightTensorCoding)
    (S : DirectedCycleDescentSpace) where
  output : HamiltonianSATPhysicalProducerPair Clause Var
  output_surface :
    HamiltonianSATCoordinateSpineProducerNailSurface R output
  cycleOfFiber : (n : ℕ) -> 2 ≤ n -> DirectedCycle
  cycle_even :
    ∀ (n : ℕ) (hn : 2 ≤ n), Even (cycleOfFiber n hn).length
  cycle_closed :
    ∀ (n : ℕ) (hn : 2 ≤ n), (cycleOfFiber n hn).holonomy = 0
  cycle_terminal :
    ∀ (n : ℕ) (hn : 2 ≤ n),
      TerminalUnderDescent S (cycleOfFiber n hn)
  cycleCode : DirectedCycle -> ℕ
  cycleOfFiber_code :
    ∀ (n : ℕ) (hn : 2 ≤ n), cycleCode (cycleOfFiber n hn) = 2 * n
  glue_code_add :
    ∀ {A B : DirectedCycle},
      PrimitiveCycle A ->
        PrimitiveCycle B ->
          cycleCode (S.glue A B) = cycleCode A + cycleCode B
  primitiveAtom :
    (P : DirectedCycle) -> PrimitiveCycle P -> SU7TensorIrreducibleAtom C
  primitiveAtom_code :
    ∀ (P : DirectedCycle) (hP : PrimitiveCycle P),
      (primitiveAtom P hP).weight.code = cycleCode P

/-- Reattach the generated color-cell fields supplied by P993/P997, producing
the P1029 carrier data. -/
def threeNailDirectedCycleCarrier_of_cycleAtomCarrier
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    {R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E}
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : SU7ThreeNailCycleAtomCarrierData Clause Var R C S) :
    SU7ThreeNailDirectedCycleCarrierData Clause Var R C S where
  output := D.output
  output_surface := D.output_surface
  cycleOfFiber := D.cycleOfFiber
  cycle_even := D.cycle_even
  cycle_closed := D.cycle_closed
  cycle_terminal := D.cycle_terminal
  generated := fun n _hn => fullOrbitIncidenceGeneratedCell n
  generated_allowed := fun n _hn =>
    fullOrbitIncidenceGeneratedCell_allowed n
  generated_trace_zero := fun n _hn =>
    fullOrbitIncidenceGeneratedCell_trace_zero n
  cycleCode := D.cycleCode
  cycleOfFiber_code := D.cycleOfFiber_code
  glue_code_add := D.glue_code_add
  primitiveAtom := D.primitiveAtom
  primitiveAtom_code := D.primitiveAtom_code

/-- THEOREM 1: P993/P997 plus cycle/atom carrier data produce P1019
additive-code data. -/
def directedCycleAdditiveCodeData_of_cycleAtomCarrier
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    {R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E}
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : SU7ThreeNailCycleAtomCarrierData Clause Var R C S) :
    DirectedCycleAdditiveCodeData C S :=
  directedCycleAdditiveCodeData_of_threeNailCarrier
    (threeNailDirectedCycleCarrier_of_cycleAtomCarrier D)

/-- THEOREM 2: cycle/atom carrier data, with generated color cells supplied by
the full-orbit incidence normalizer, hit zero residual through P1028. -/
theorem branchTensorGeneratorOfCycleAtomCarrier_hits
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    {R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E}
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : SU7ThreeNailCycleAtomCarrierData Clause Var R C S) :
    ∀ n : ℕ, ∀ hn : 2 ≤ n,
      ∃ cand ∈
        (branchTensorGeneratorOfAdditiveCodeData
          (directedCycleAdditiveCodeData_of_cycleAtomCarrier D)).candidates
            n hn,
        cand.residual = (0, 0) := by
  exact
    branchTensorGeneratorOfAdditiveCodeData_hits
      (directedCycleAdditiveCodeData_of_cycleAtomCarrier D)

/-- THEOREM 3: the remaining cycle/atom carrier data are enough for the
SU(7) tensor-atom lift producer. -/
theorem su7TensorAtomLiftProducer_of_cycleAtomCarrier
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    {R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E}
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : SU7ThreeNailCycleAtomCarrierData Clause Var R C S) :
    SU7TensorAtomLiftProducer C :=
  su7TensorAtomLiftProducer_of_threeNailCarrier
    (threeNailDirectedCycleCarrier_of_cycleAtomCarrier D)

/-! ## Certificate -/

/-- P1030 certificate: P993/P997 discharge the generated color-cell portion of
the P1029 carrier. -/
structure ThreeNailCycleAtomCarrierProducerCertificate where
  full_orbit_generated_trace_zero :
    ∀ n : ℕ,
      physicalColorLoopTrace
        (terminalPhysicalCellOfGeneratedColorCell
          (fullOrbitIncidenceGeneratedCell n)) = 0
  cycle_atom_to_three_nail_carrier :
    ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      [CompleteSpace E]
      {Clause : Type v} {Var : Type w} [Fintype Clause]
      {R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
        E}
      {C : SU7WeightTensorCoding}
      {S : DirectedCycleDescentSpace},
      SU7ThreeNailCycleAtomCarrierData Clause Var R C S ->
        SU7ThreeNailDirectedCycleCarrierData Clause Var R C S
  lift_producer :
    ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      [CompleteSpace E]
      {Clause : Type v} {Var : Type w} [Fintype Clause]
      {R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
        E}
      {C : SU7WeightTensorCoding}
      {S : DirectedCycleDescentSpace},
      SU7ThreeNailCycleAtomCarrierData Clause Var R C S ->
        SU7TensorAtomLiftProducer C

def threeNailCycleAtomCarrierProducerCertificate :
    ThreeNailCycleAtomCarrierProducerCertificate where
  full_orbit_generated_trace_zero :=
    fullOrbitIncidenceGeneratedCell_trace_zero
  cycle_atom_to_three_nail_carrier :=
    threeNailDirectedCycleCarrier_of_cycleAtomCarrier
  lift_producer := su7TensorAtomLiftProducer_of_cycleAtomCarrier


end StandardModelConstraint
end SaturationMonoid
