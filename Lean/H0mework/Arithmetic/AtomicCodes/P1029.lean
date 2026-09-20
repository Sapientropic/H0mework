import H0mework.Physics.JointSources.P710
import H0mework.Physics.BranchSources.P1028

/-!
# Proposition 1029: P710 three-nail carrier data feeds the additive-code throat

P1028 removed the bare branch/tensor hit assumption once a
`DirectedCycleAdditiveCodeData` object is present.  This file pins the next
producer object: a P710 accepted three-nail surface together with the directed
cycle / additive-code carrier fields needed by P1019.

This file deliberately stays upstream of arithmetic projection.  It mentions
no prime-edge object and no Goldbach statement.  Its job is to make the
remaining producer exact:

```text
P710 accepted three-nail physical surface
+ cycle family / terminal descent / additive code / tensor-atom realization
-> DirectedCycleAdditiveCodeData
-> P1028 singleton branch/tensor generator hits zero residual
```
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open GrandUnification

set_option linter.checkUnivs false
set_option linter.defProp false

universe u v w z

/-! ## The P710 physical carrier fields still needed by P1019 -/

/-- A P710 accepted three-nail output, plus the actual directed-cycle carrier
fields required to construct `DirectedCycleAdditiveCodeData`.

The P710 surface pins the finite physical readout to the canonical three nails.
The remaining fields are not arithmetic receipts: they are the cycle family,
terminal descent, generated color cells, carrier code, and tensor-irreducible
realization that the physical SU(7) carrier still has to produce. -/
structure SU7ThreeNailDirectedCycleCarrierData
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
  generated :
    (n : ℕ) -> 2 ≤ n -> SU7GeneratedTerminalColorCell n
  generated_allowed :
    ∀ (n : ℕ) (hn : 2 ≤ n),
      SameCarrierGaugeAllowed (generated n hn)
  generated_trace_zero :
    ∀ (n : ℕ) (hn : 2 ≤ n),
      physicalColorLoopTrace
        (terminalPhysicalCellOfGeneratedColorCell (generated n hn)) = 0
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

/-! ## Reading the P710 nails from the carrier -/

/-- The accepted carrier's physical output is the canonical P710 output. -/
theorem threeNailDirectedCycleCarrier_output_eq_canonical
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    {R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E}
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : SU7ThreeNailDirectedCycleCarrierData Clause Var R C S) :
    D.output = canonicalHamiltonianSATPhysicalProducerPair Clause Var := by
  exact
    (hamiltonianSATCoordinateSpineProducerNailSurface_iff_canonical
      R D.output).1 D.output_surface

/-- The alpha-strong residual nail is forced by the accepted P710 surface. -/
theorem threeNailDirectedCycleCarrier_alphaInverseResidual
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    {R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E}
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : SU7ThreeNailDirectedCycleCarrierData Clause Var R C S) :
    D.output.2.2.alphaInverseResidual = -((89000 : ℚ) / 128511) := by
  exact D.output_surface.2.2.1

/-- The nine Yukawa-depth nail is forced by the accepted P710 surface. -/
theorem threeNailDirectedCycleCarrier_yukawaMassOrder
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    {R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E}
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : SU7ThreeNailDirectedCycleCarrierData Clause Var R C S) :
    D.output.2.2.yukawaMassOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] := by
  exact D.output_surface.2.2.2.1

/-- The CKM/Jarlskog depth-sum nail is forced by the accepted P710 surface. -/
theorem threeNailDirectedCycleCarrier_ckmDepthSum
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    {R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E}
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : SU7ThreeNailDirectedCycleCarrierData Clause Var R C S) :
    D.output.2.2.ckmDepthSum = (386 : ℚ) := by
  exact D.output_surface.2.2.2.2

/-! ## Lowering P710 carrier data to P1019/P1028 -/

/-- Forget only the P710 finite readout, keeping the directed-cycle carrier
fields as P1019 additive-code data. -/
def directedCycleAdditiveCodeData_of_threeNailCarrier
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    {R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E}
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : SU7ThreeNailDirectedCycleCarrierData Clause Var R C S) :
    DirectedCycleAdditiveCodeData C S where
  cycleOfFiber := D.cycleOfFiber
  cycle_even := D.cycle_even
  cycle_closed := D.cycle_closed
  cycle_terminal := D.cycle_terminal
  generated := D.generated
  generated_allowed := D.generated_allowed
  generated_trace_zero := D.generated_trace_zero
  cycleCode := D.cycleCode
  cycleOfFiber_code := D.cycleOfFiber_code
  glue_code_add := D.glue_code_add
  primitiveAtom := D.primitiveAtom
  primitiveAtom_code := D.primitiveAtom_code

/-- A P710 three-nail directed-cycle carrier supplies the explicit P1028
branch/tensor generator. -/
def branchTensorGeneratorOfThreeNailCarrier
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    {R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E}
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : SU7ThreeNailDirectedCycleCarrierData Clause Var R C S) :
    SU7BranchTensorGenerator C :=
  branchTensorGeneratorOfAdditiveCodeData
    (directedCycleAdditiveCodeData_of_threeNailCarrier D)

/-- THEOREM 1: the P710 three-nail directed-cycle carrier hits zero residual
on every active fiber through the P1028 singleton generator. -/
theorem branchTensorGeneratorOfThreeNailCarrier_hits
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    {R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E}
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : SU7ThreeNailDirectedCycleCarrierData Clause Var R C S) :
    ∀ n : ℕ, ∀ hn : 2 ≤ n,
      ∃ cand ∈ (branchTensorGeneratorOfThreeNailCarrier D).candidates n hn,
        cand.residual = (0, 0) := by
  exact
    branchTensorGeneratorOfAdditiveCodeData_hits
      (directedCycleAdditiveCodeData_of_threeNailCarrier D)

/-- THEOREM 2: a P710 three-nail directed-cycle carrier supplies the P1016
SU(7) tensor-atom lift producer. -/
theorem su7TensorAtomLiftProducer_of_threeNailCarrier
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {Clause : Type v} {Var : Type w} [Fintype Clause]
    {R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E}
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : SU7ThreeNailDirectedCycleCarrierData Clause Var R C S) :
    SU7TensorAtomLiftProducer C :=
  su7TensorAtomLiftProducer_of_additiveCodeBranchTensorGenerator
    (directedCycleAdditiveCodeData_of_threeNailCarrier D)

/-! ## Certificate -/

/-- P1029 certificate: once the P710 accepted physical surface carries the
directed-cycle additive-code fields, it automatically feeds P1028 and P1016. -/
structure ThreeNailDirectedCycleCarrierProducerCertificate where
  to_additive_code :
    ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      [CompleteSpace E]
      {Clause : Type v} {Var : Type w} [Fintype Clause]
      {R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
        E}
      {C : SU7WeightTensorCoding}
      {S : DirectedCycleDescentSpace},
      SU7ThreeNailDirectedCycleCarrierData Clause Var R C S ->
        DirectedCycleAdditiveCodeData C S
  generator_hits :
    ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      [CompleteSpace E]
      {Clause : Type v} {Var : Type w} [Fintype Clause]
      {R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
        E}
      {C : SU7WeightTensorCoding}
      {S : DirectedCycleDescentSpace}
      (D : SU7ThreeNailDirectedCycleCarrierData Clause Var R C S),
      ∀ n : ℕ, ∀ hn : 2 ≤ n,
        ∃ cand ∈ (branchTensorGeneratorOfThreeNailCarrier D).candidates n hn,
          cand.residual = (0, 0)
  lift_producer :
    ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      [CompleteSpace E]
      {Clause : Type v} {Var : Type w} [Fintype Clause]
      {R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
        E}
      {C : SU7WeightTensorCoding}
      {S : DirectedCycleDescentSpace},
      SU7ThreeNailDirectedCycleCarrierData Clause Var R C S ->
        SU7TensorAtomLiftProducer C

/-- Canonical P1029 certificate. -/
def threeNailDirectedCycleCarrierProducerCertificate :
    ThreeNailDirectedCycleCarrierProducerCertificate where
  to_additive_code := directedCycleAdditiveCodeData_of_threeNailCarrier
  generator_hits := branchTensorGeneratorOfThreeNailCarrier_hits
  lift_producer := su7TensorAtomLiftProducer_of_threeNailCarrier


end StandardModelConstraint
end SaturationMonoid
