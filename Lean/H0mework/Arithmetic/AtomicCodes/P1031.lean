import H0mework.Physics.BranchSources.P1030

/-!
# Proposition 1031: P710 is no longer a field of the remaining producer

P1030 removed the generated color-cell obligation by using the full-orbit
incidence normalizer.  This file removes one more false dependency: the P710
three-nail surface is already canonically inhabited by P710 itself, so it
should not remain part of the hard producer object.

The remaining upstream object is now exactly:

```text
directed-cycle family
+ additive code on cycles
+ primitive-cycle -> tensor-irreducible SU(7) atom realization
```

No generated color-cell field, endpoint arithmetic object, prime-edge object,
or Goldbach statement appears here.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open GrandUnification

set_option linter.checkUnivs false
set_option linter.defProp false

universe u v w z

/-! ## The reduced cycle/atom producer object -/

/-- The remaining hard carrier object after P993/P997 discharge generated
color cells and P710 discharges the three-nail readout.

This is the current exact producer throat: construct this from the finite
SU(7) representation/consolidation carrier, and P1028/P1030 give the
same-carrier tensor-atom zero producer. -/
structure SU7CycleAtomCarrierData
    (C : SU7WeightTensorCoding)
    (S : DirectedCycleDescentSpace) where
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

/-! ## Reattaching canonical P710 and full-orbit generated color cells -/

/-- Reattach the canonical P710 surface, then use P1030 to reattach generated
color cells from the full-orbit incidence normalizer. -/
def threeNailCycleAtomCarrier_of_cycleAtomData
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (Clause : Type v) (Var : Type w) [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : SU7CycleAtomCarrierData C S) :
    SU7ThreeNailCycleAtomCarrierData Clause Var R C S where
  output := canonicalHamiltonianSATPhysicalProducerPair Clause Var
  output_surface :=
    (hamiltonianSATCoordinateSpineProducerNailSurface_iff_canonical
      R (canonicalHamiltonianSATPhysicalProducerPair Clause Var)).2 rfl
  cycleOfFiber := D.cycleOfFiber
  cycle_even := D.cycle_even
  cycle_closed := D.cycle_closed
  cycle_terminal := D.cycle_terminal
  cycleCode := D.cycleCode
  cycleOfFiber_code := D.cycleOfFiber_code
  glue_code_add := D.glue_code_add
  primitiveAtom := D.primitiveAtom
  primitiveAtom_code := D.primitiveAtom_code

/-- The reduced cycle/atom data are enough to construct P1019 additive-code
data, with P710 and generated color cells supplied by earlier theorems. -/
def directedCycleAdditiveCodeData_of_cycleAtomData
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (Clause : Type v) (Var : Type w) [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : SU7CycleAtomCarrierData C S) :
    DirectedCycleAdditiveCodeData C S :=
  directedCycleAdditiveCodeData_of_cycleAtomCarrier
    (threeNailCycleAtomCarrier_of_cycleAtomData Clause Var R D)

/-- THEOREM 1: reduced cycle/atom data hit zero residual through the existing
P1028 branch/tensor generator. -/
theorem branchTensorGeneratorOfCycleAtomData_hits
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (Clause : Type v) (Var : Type w) [Fintype Clause]
    (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
      E)
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : SU7CycleAtomCarrierData C S) :
    ∀ n : ℕ, ∀ hn : 2 ≤ n,
      ∃ cand ∈
        (branchTensorGeneratorOfAdditiveCodeData
          (directedCycleAdditiveCodeData_of_cycleAtomData
            Clause Var R D)).candidates n hn,
        cand.residual = (0, 0) := by
  exact
    branchTensorGeneratorOfAdditiveCodeData_hits
      (directedCycleAdditiveCodeData_of_cycleAtomData Clause Var R D)

/-- THEOREM 2: reduced cycle/atom data supply the SU(7) tensor-atom lift
producer. -/
theorem su7TensorAtomLiftProducer_of_cycleAtomData
    {C : SU7WeightTensorCoding}
    {S : DirectedCycleDescentSpace}
    (D : SU7CycleAtomCarrierData C S) :
    SU7TensorAtomLiftProducer C := by
  intro n hn
  let E := ℂ
  let Clause := Unit
  let Var := Unit
  let R :
      HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{0, 0, 0, 0}
        E :=
    hamiltonianSATEnergySameCarrierUnifiedRootCertificate (E := E)
  exact
    (su7TensorAtomLiftProducer_of_cycleAtomCarrier
      (threeNailCycleAtomCarrier_of_cycleAtomData Clause Var R D)) n hn

/-! ## Certificate -/

/-- P1031 certificate: the exact remaining hard producer is the reduced
cycle/atom carrier data. -/
structure CycleAtomCarrierProducerCertificate where
  to_three_nail_cycle_atom :
    ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      [CompleteSpace E]
      (Clause : Type v) (Var : Type w) [Fintype Clause]
      (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
        E)
      {C : SU7WeightTensorCoding}
      {S : DirectedCycleDescentSpace},
      SU7CycleAtomCarrierData C S ->
        SU7ThreeNailCycleAtomCarrierData Clause Var R C S
  generator_hits :
    ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      [CompleteSpace E]
      (Clause : Type v) (Var : Type w) [Fintype Clause]
      (R : HamiltonianSATEnergySameCarrierUnifiedRootCertificate.{w, z, u, v}
        E)
      {C : SU7WeightTensorCoding}
      {S : DirectedCycleDescentSpace}
      (D : SU7CycleAtomCarrierData C S),
      ∀ n : ℕ, ∀ hn : 2 ≤ n,
        ∃ cand ∈
          (branchTensorGeneratorOfAdditiveCodeData
            (directedCycleAdditiveCodeData_of_cycleAtomData
              Clause Var R D)).candidates n hn,
          cand.residual = (0, 0)
  lift_producer :
    ∀ {C : SU7WeightTensorCoding} {S : DirectedCycleDescentSpace},
      SU7CycleAtomCarrierData C S -> SU7TensorAtomLiftProducer C

def cycleAtomCarrierProducerCertificate :
    CycleAtomCarrierProducerCertificate where
  to_three_nail_cycle_atom :=
    threeNailCycleAtomCarrier_of_cycleAtomData
  generator_hits := branchTensorGeneratorOfCycleAtomData_hits
  lift_producer := su7TensorAtomLiftProducer_of_cycleAtomData


end StandardModelConstraint
end SaturationMonoid
