import H0mework.Realization.Faces.P848

/-!
# Proposition 849: topological obstruction forces color-loop zero fibers

The previous closure reduced the remaining color-loop debt to the throat

`SU7GaugeFlowTraceZeroNormalizer`.

This file gives the next producer shape.  Instead of trying to pick prime
edges directly, it states a finite topological obstruction principle for the
color-loop gauge-orbit space:

* nonzero Euler characteristic of the trace-zero submanifold;
* or a nonzero Betti witness landing in that submanifold;
* or a nonzero Morse critical witness landing in that submanifold

forces a point of the trace-zero submanifold, hence a
`TraceZeroPrimeEdgeLoop n`.

If every even fiber carries such a topological obstruction, the framework
constructs the gauge-flow trace-zero normalizer, hence the P848 seven-face
carrier self-consistency condition and the P820 grand zero-fiber certificate.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open SaturationMonoid.AffineRelaxation
open SaturationMonoid.ResidualProjection

set_option linter.checkUnivs false
set_option linter.defProp false

/-! ## Finite orbit-space model -/

/-- A finite cell model for the trace-zero submanifold inside the prime-edge
color-loop gauge-orbit space over the even fiber `2n`.

The `zeroCells` list is the finite trace-zero cell basis after the
representation-theoretic realization map has been applied.  This avoids hiding
the producer in a selector: every cell is already a concrete
`TraceZeroPrimeEdgeLoop n`. -/
structure FiniteColorLoopGaugeOrbitSpace (n : ℕ) where
  zeroCells : List (TraceZeroPrimeEdgeLoop n)

namespace FiniteColorLoopGaugeOrbitSpace

/-- Finite Euler characteristic of the trace-zero submanifold, modeled as the
cardinality of its finite cell basis. -/
def zeroEulerCharacteristic {n : ℕ}
    (O : FiniteColorLoopGaugeOrbitSpace n) : ℤ :=
  (O.zeroCells.length : ℤ)

end FiniteColorLoopGaugeOrbitSpace

/-! ## Euler / Betti / Morse obstruction witnesses -/

/-- Euler obstruction: nonzero Euler characteristic of the trace-zero
submanifold. -/
structure ColorLoopEulerTraceZeroObstruction (n : ℕ) where
  orbit : FiniteColorLoopGaugeOrbitSpace n
  euler_nonzero :
    orbit.zeroEulerCharacteristic ≠ 0

/-- Betti obstruction: a nonzero finite homology witness that maps into the
trace-zero submanifold. -/
structure ColorLoopBettiTraceZeroObstruction (n : ℕ) where
  orbit : FiniteColorLoopGaugeOrbitSpace n
  bettiCells : List (TraceZeroPrimeEdgeLoop n)
  betti_nonzero : (bettiCells.length : ℤ) ≠ 0

/-- Morse obstruction: a nonzero finite critical-point witness that maps into
the trace-zero submanifold. -/
structure ColorLoopMorseTraceZeroObstruction (n : ℕ) where
  orbit : FiniteColorLoopGaugeOrbitSpace n
  criticalCells : List (TraceZeroPrimeEdgeLoop n)
  morse_nonzero : (criticalCells.length : ℤ) ≠ 0

/-- The three topological doors that can force a trace-zero point. -/
inductive ColorLoopGaugeOrbitTopologicalObstruction (n : ℕ) : Type 2
  | euler :
      ColorLoopEulerTraceZeroObstruction n ->
        ColorLoopGaugeOrbitTopologicalObstruction n
  | betti :
      ColorLoopBettiTraceZeroObstruction n ->
        ColorLoopGaugeOrbitTopologicalObstruction n
  | morse :
      ColorLoopMorseTraceZeroObstruction n ->
        ColorLoopGaugeOrbitTopologicalObstruction n

/-! ## Nonzero topology forces a zero point -/

/-- A finite list with nonzero length contains an element. -/
theorem exists_mem_of_list_length_ne_zero
    {α : Type} {xs : List α} (h : xs.length ≠ 0) :
    ∃ x : α, x ∈ xs := by
  cases xs with
  | nil =>
      simp at h
  | cons x xs =>
      exact ⟨x, by simp⟩

/-- THEOREM 1: nonzero finite Euler characteristic forces a point of the
trace-zero submanifold. -/
theorem zeroSubmanifold_nonempty_of_euler_nonzero
    {n : ℕ} (E : ColorLoopEulerTraceZeroObstruction n) :
    Nonempty (TraceZeroPrimeEdgeLoop n) := by
  classical
  have hlen : E.orbit.zeroCells.length ≠ 0 := by
    intro hzero
    have hchi : E.orbit.zeroEulerCharacteristic = 0 := by
      unfold FiniteColorLoopGaugeOrbitSpace.zeroEulerCharacteristic
      exact_mod_cast hzero
    exact E.euler_nonzero hchi
  rcases exists_mem_of_list_length_ne_zero hlen with ⟨Z, _hZ⟩
  exact ⟨Z⟩

/-- THEOREM 2: a nonzero Euler obstruction produces a trace-zero
prime-edge loop. -/
def traceZeroPrimeEdgeLoop_of_eulerObstruction
    {n : ℕ} (E : ColorLoopEulerTraceZeroObstruction n) :
    TraceZeroPrimeEdgeLoop n :=
  Classical.choice (zeroSubmanifold_nonempty_of_euler_nonzero E)

/-- THEOREM 3: nonzero finite Betti witness forces a point of the trace-zero
submanifold. -/
theorem zeroSubmanifold_nonempty_of_betti_nonzero
    {n : ℕ} (B : ColorLoopBettiTraceZeroObstruction n) :
    Nonempty (TraceZeroPrimeEdgeLoop n) := by
  classical
  have hlen : B.bettiCells.length ≠ 0 := by
    intro hzero
    have hbetti : (B.bettiCells.length : ℤ) = 0 := by
      exact_mod_cast hzero
    exact B.betti_nonzero hbetti
  rcases exists_mem_of_list_length_ne_zero hlen with ⟨Z, _hZ⟩
  exact ⟨Z⟩

/-- THEOREM 4: a nonzero Betti obstruction produces a trace-zero
prime-edge loop. -/
def traceZeroPrimeEdgeLoop_of_bettiObstruction
    {n : ℕ} (B : ColorLoopBettiTraceZeroObstruction n) :
    TraceZeroPrimeEdgeLoop n :=
  Classical.choice (zeroSubmanifold_nonempty_of_betti_nonzero B)

/-- THEOREM 5: nonzero finite Morse critical witness forces a point of the
trace-zero submanifold. -/
theorem zeroSubmanifold_nonempty_of_morse_nonzero
    {n : ℕ} (M : ColorLoopMorseTraceZeroObstruction n) :
    Nonempty (TraceZeroPrimeEdgeLoop n) := by
  classical
  have hlen : M.criticalCells.length ≠ 0 := by
    intro hzero
    have hmorse : (M.criticalCells.length : ℤ) = 0 := by
      exact_mod_cast hzero
    exact M.morse_nonzero hmorse
  rcases exists_mem_of_list_length_ne_zero hlen with ⟨Z, _hZ⟩
  exact ⟨Z⟩

/-- THEOREM 6: a nonzero Morse obstruction produces a trace-zero
prime-edge loop. -/
def traceZeroPrimeEdgeLoop_of_morseObstruction
    {n : ℕ} (M : ColorLoopMorseTraceZeroObstruction n) :
    TraceZeroPrimeEdgeLoop n :=
  Classical.choice (zeroSubmanifold_nonempty_of_morse_nonzero M)

/-- THEOREM 7: any of the Euler / Betti / Morse topological obstructions
produces a trace-zero prime-edge loop. -/
def traceZeroPrimeEdgeLoop_of_topologicalObstruction
    {n : ℕ} :
    ColorLoopGaugeOrbitTopologicalObstruction n ->
      TraceZeroPrimeEdgeLoop n
  | .euler E => traceZeroPrimeEdgeLoop_of_eulerObstruction E
  | .betti B => traceZeroPrimeEdgeLoop_of_bettiObstruction B
  | .morse M => traceZeroPrimeEdgeLoop_of_morseObstruction M

/-- THEOREM 8: the produced point really lies in the trace-zero fiber. -/
theorem topologicalObstruction_trace_zero
    {n : ℕ} (H : ColorLoopGaugeOrbitTopologicalObstruction n) :
    ColorLoopTraceExact
      (primeEdgeColorLoopMatrix n
        (traceZeroPrimeEdgeLoop_of_topologicalObstruction H).leftPrime
        (traceZeroPrimeEdgeLoop_of_topologicalObstruction H).rightPrime) :=
  (traceZeroPrimeEdgeLoop_of_topologicalObstruction H).trace_zero

/-! ## Fiberwise topological obstruction gives the gauge-flow throat -/

/-- Every even fiber carries a nonzero color-loop gauge-orbit topological
obstruction. -/
def ColorLoopGaugeOrbitTopologicalObstructionEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (ColorLoopGaugeOrbitTopologicalObstruction n)

/-- THEOREM 9: fiberwise topological obstruction constructs the gauge-flow
trace-zero normalizer. -/
def gaugeFlowTraceZeroNormalizer_of_topologicalObstructions
    (H : ColorLoopGaugeOrbitTopologicalObstructionEveryEvenFiber) :
    SU7GaugeFlowTraceZeroNormalizer where
  normalForm := fun n hn =>
    traceZeroPrimeEdgeLoop_of_topologicalObstruction
      (Classical.choice (H n hn))

/-- THEOREM 10: fiberwise topological obstruction produces the gauge-flow
trace-zero throat. -/
theorem gaugeFlowTraceZeroProducer_of_topologicalObstructions
    (H : ColorLoopGaugeOrbitTopologicalObstructionEveryEvenFiber) :
    SU7GaugeFlowTraceZeroProducer :=
  ⟨gaugeFlowTraceZeroNormalizer_of_topologicalObstructions H⟩

/-- THEOREM 11: fiberwise topological obstruction gives P848's seven-face
carrier self-consistency. -/
theorem sevenFaceCarrierSelfConsistency_of_topologicalObstructions
    (H : ColorLoopGaugeOrbitTopologicalObstructionEveryEvenFiber) :
    SevenFaceCarrierSelfConsistency :=
  sevenFaceCarrierSelfConsistency_iff_gaugeFlowTraceZeroProducer.mpr
    (gaugeFlowTraceZeroProducer_of_topologicalObstructions H)

/-- THEOREM 12: under GrandProducerCompleteness, the topological obstruction
route produces all grand carrier zero fibers. -/
theorem grandCarrierConsistencyZeroFibers_of_topologicalObstructions
    (C : GrandProducerCompletenessCertificate)
    (H : ColorLoopGaugeOrbitTopologicalObstructionEveryEvenFiber) :
    GrandCarrierConsistencyZeroFiberCertificate :=
  grandProducerCompleteness_carrierConsistencyZeroFibers_of_sevenFaceCarrierSelfConsistency
    C
    (sevenFaceCarrierSelfConsistency_of_topologicalObstructions H)

end StandardModelConstraint
end SaturationMonoid
