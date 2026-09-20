import H0mework.Physics.JointSources.P347

/-!
# Proposition 348: the color-loop trace observable

P347 proved that the naive fundamental fixed-vector color-singlet is too small:
no prime-edge color field is fixed by the fundamental `SU(3)` action.  The next
honest object is therefore not a fixed vector, but a closed-loop observable.

This file formalizes the first such object.  A color loop is a `3×3` complex
matrix, the color gauge group acts on it by conjugation

`M ↦ C M C⁻¹`,

and the trace is invariant under this action.  The prime-edge three-cycle is
embedded as the diagonal loop

`diag(p, q, -2n)`.

Its trace is exactly the Goldbach defect `p + q - 2n`; trace zero is therefore
equivalent to the P343 selected-edge exactness, and nonzero trace gives the
same concrete H¹ obstruction.

Boundary: this still does not prove Goldbach.  It proves that the arithmetic
defect is a genuine gauge-invariant closed-loop observable.  A later physics
producer must still prove that the Standard-Model allowed sector excludes the
nonzero-trace prime-edge loops.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace StandardModelConstraint

open GaugeProjection
open Matrix
open SaturationMonoid.AffineRelaxation

/-! ## Color-loop conjugation action -/

/-- A closed color loop: an endomorphism of the three-color block. -/
abbrev ColorLoopField := Matrix (Fin 3) (Fin 3) ℂ

/-- Color gauge action on a loop field by conjugation. -/
def colorLoopGaugeAction (c : SU3Gauge) (M : ColorLoopField) :
    ColorLoopField :=
  (c : Matrix (Fin 3) (Fin 3) ℂ) * M *
    ((c⁻¹ : SU3Gauge) : Matrix (Fin 3) (Fin 3) ℂ)

/-- THEOREM 1: the identity color element acts trivially on loop fields. -/
theorem colorLoopGaugeAction_one (M : ColorLoopField) :
    colorLoopGaugeAction 1 M = M := by
  simp [colorLoopGaugeAction]

/-- THEOREM 2: loop conjugation composes as a left group action. -/
theorem colorLoopGaugeAction_mul
    (c d : SU3Gauge) (M : ColorLoopField) :
    colorLoopGaugeAction (c * d) M =
      colorLoopGaugeAction c (colorLoopGaugeAction d M) := by
  simp [colorLoopGaugeAction, Matrix.mul_assoc]

/-- The loop trace observable. -/
def colorLoopTrace (M : ColorLoopField) : ℂ :=
  M.trace

/-- THEOREM 3: the color-loop trace is invariant under `SU(3)` conjugation. -/
theorem colorLoopTrace_gaugeInvariant
    (c : SU3Gauge) (M : ColorLoopField) :
    colorLoopTrace (colorLoopGaugeAction c M) = colorLoopTrace M := by
  unfold colorLoopTrace colorLoopGaugeAction
  have hinv :
      ((c⁻¹ : SU3Gauge) : Matrix (Fin 3) (Fin 3) ℂ) *
        (c : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
    exact congrArg Subtype.val (inv_mul_cancel c)
  calc
    ((c : Matrix (Fin 3) (Fin 3) ℂ) * M *
        ((c⁻¹ : SU3Gauge) : Matrix (Fin 3) (Fin 3) ℂ)).trace
        =
      (((c⁻¹ : SU3Gauge) : Matrix (Fin 3) (Fin 3) ℂ) *
        ((c : Matrix (Fin 3) (Fin 3) ℂ) * M)).trace := by
          simpa [Matrix.mul_assoc] using
            (Matrix.trace_mul_comm
              ((c : Matrix (Fin 3) (Fin 3) ℂ) * M)
              ((c⁻¹ : SU3Gauge) : Matrix (Fin 3) (Fin 3) ℂ))
    _ =
      ((((c⁻¹ : SU3Gauge) : Matrix (Fin 3) (Fin 3) ℂ) *
        (c : Matrix (Fin 3) (Fin 3) ℂ)) * M).trace := by
          rw [Matrix.mul_assoc]
    _ = M.trace := by
          rw [hinv]
          simp

/-- Trace-exact loops are the zero-fiber of the gauge-invariant trace
observable. -/
def ColorLoopTraceExact (M : ColorLoopField) : Prop :=
  colorLoopTrace M = 0

/-- THEOREM 4: the trace-exact loop fiber is nonempty. -/
theorem colorLoopTraceExact_zero :
    ColorLoopTraceExact (0 : ColorLoopField) := by
  simp [ColorLoopTraceExact, colorLoopTrace]

/-- THEOREM 5: trace-exactness is gauge-invariant. -/
theorem colorLoopTraceExact_gaugeInvariant
    (c : SU3Gauge) (M : ColorLoopField) :
    ColorLoopTraceExact (colorLoopGaugeAction c M) ↔
      ColorLoopTraceExact M := by
  unfold ColorLoopTraceExact
  rw [colorLoopTrace_gaugeInvariant]

/-- THEOREM 6: nonzero trace, hence loop obstruction, is also
gauge-invariant. -/
theorem colorLoopTrace_nonzero_gaugeInvariant
    (c : SU3Gauge) (M : ColorLoopField) :
    colorLoopTrace (colorLoopGaugeAction c M) ≠ 0 ↔
      colorLoopTrace M ≠ 0 := by
  rw [colorLoopTrace_gaugeInvariant]

/-! ## Prime-edge loops -/

/-- Embed the prime-edge three-cycle as the diagonal color loop
`diag(p, q, -2n)`. -/
def primeEdgeColorLoopMatrix
    (n : ℕ) (p q : PrimeExponent) : ColorLoopField :=
  Matrix.diagonal fun i : Fin 3 =>
    if i = (0 : Fin 3) then (p.1 : ℂ)
    else if i = (1 : Fin 3) then (q.1 : ℂ)
    else -((2 * n : ℕ) : ℂ)

/-- THEOREM 7: the prime-edge loop trace is the arithmetic defect
`p + q - 2n`. -/
theorem primeEdgeColorLoop_trace_eq
    (n : ℕ) (p q : PrimeExponent) :
    colorLoopTrace (primeEdgeColorLoopMatrix n p q) =
      (p.1 : ℂ) + (q.1 : ℂ) - ((2 * n : ℕ) : ℂ) := by
  simp [colorLoopTrace, primeEdgeColorLoopMatrix, Matrix.trace,
    Fin.sum_univ_three]
  ring

/-- THEOREM 8: trace zero of the prime-edge loop is exactly the equation
`p + q = 2n`. -/
theorem primeEdgeColorLoop_trace_zero_iff
    (n : ℕ) (p q : PrimeExponent) :
    colorLoopTrace (primeEdgeColorLoopMatrix n p q) = 0 ↔
      2 * n = p.1 + q.1 := by
  rw [primeEdgeColorLoop_trace_eq]
  constructor
  · intro h
    have h' : ((p.1 + q.1 : ℕ) : ℂ) = ((2 * n : ℕ) : ℂ) := by
      norm_num at h ⊢
      linear_combination h
    exact_mod_cast h'.symm
  · intro h
    rw [h]
    norm_num

/-- THEOREM 9: prime-edge loop trace-exactness is exactly P343 selected-edge
exactness. -/
theorem primeEdgeColorLoop_traceExact_iff_edgeExact
    (n : ℕ) (p q : PrimeExponent) :
    ColorLoopTraceExact (primeEdgeColorLoopMatrix n p q) ↔
      ThreeAgentRingEdgeExact (primeEdgeThreeCycleCochain n p q) := by
  rw [ColorLoopTraceExact, primeEdgeColorLoop_trace_zero_iff,
    primeEdgeThreeCycle_edgeExact_iff]

/-- The prime `2` as a prime exponent. -/
def twoPrimeExponent : PrimeExponent :=
  ⟨2, Nat.prime_two⟩

/-- THEOREM 10: the prime-edge loop fiber has a concrete exact point:
`2 + 2 = 4`. -/
theorem primeEdgeColorLoop_traceExact_two_two :
    ColorLoopTraceExact
      (primeEdgeColorLoopMatrix 2 twoPrimeExponent twoPrimeExponent) := by
  rw [primeEdgeColorLoop_traceExact_iff_edgeExact]
  exact (primeEdgeThreeCycle_edgeExact_iff
    2 twoPrimeExponent twoPrimeExponent).mpr (by norm_num [twoPrimeExponent])

/-- A prime-edge loop obstruction is nonzero trace of the closed-loop
observable. -/
def PrimeEdgeColorLoopObstructed
    (n : ℕ) (p q : PrimeExponent) : Prop :=
  colorLoopTrace (primeEdgeColorLoopMatrix n p q) ≠ 0

/-- THEOREM 11: nonzero color-loop trace is exactly the P343 prime-edge
obstruction predicate. -/
theorem primeEdgeColorLoop_obstructed_iff
    (n : ℕ) (p q : PrimeExponent) :
    PrimeEdgeColorLoopObstructed n p q ↔
      PrimeEdgeThreeCycleObstructed n p q := by
  unfold PrimeEdgeColorLoopObstructed PrimeEdgeThreeCycleObstructed
  change
    (¬ ColorLoopTraceExact (primeEdgeColorLoopMatrix n p q)) ↔
      ¬ ThreeAgentRingEdgeExact (primeEdgeThreeCycleCochain n p q)
  exact not_congr (primeEdgeColorLoop_traceExact_iff_edgeExact n p q)

/-- THEOREM 12: a nonzero prime-edge color-loop trace gives the concrete
three-agent H¹ obstruction. -/
theorem primeEdgeColorLoop_obstructed_h1
    {n : ℕ} {p q : PrimeExponent}
    (hobs : PrimeEdgeColorLoopObstructed n p q) :
    CechAdditiveCover.H1Obstruction
      (identityPairZeroTripleCover ThreeCycleTime Int)
      (primeEdgeThreeCycleCochain n p q) :=
  primeEdgeThreeCycle_obstructed_h1
    ((primeEdgeColorLoop_obstructed_iff n p q).mp hobs)

/-- THEOREM 13: the prime-edge color-loop obstruction is transported along the
color gauge action, because it is only the nonzero fiber of the invariant trace
observable. -/
theorem primeEdgeColorLoop_obstruction_gaugeInvariant
    (c : SU3Gauge) (n : ℕ) (p q : PrimeExponent) :
    colorLoopTrace
        (colorLoopGaugeAction c (primeEdgeColorLoopMatrix n p q)) ≠ 0 ↔
      PrimeEdgeColorLoopObstructed n p q := by
  rw [PrimeEdgeColorLoopObstructed,
    colorLoopTrace_nonzero_gaugeInvariant]

/-- A compact certificate for the color-loop trace bridge. -/
structure P348ColorLoopTraceGoldbachBridgeCertificate : Prop where
  action_one :
    ∀ M : ColorLoopField, colorLoopGaugeAction 1 M = M
  action_mul :
    ∀ (c d : SU3Gauge) (M : ColorLoopField),
      colorLoopGaugeAction (c * d) M =
        colorLoopGaugeAction c (colorLoopGaugeAction d M)
  trace_gauge_invariant :
    ∀ (c : SU3Gauge) (M : ColorLoopField),
      colorLoopTrace (colorLoopGaugeAction c M) = colorLoopTrace M
  trace_exact_gauge_invariant :
    ∀ (c : SU3Gauge) (M : ColorLoopField),
      ColorLoopTraceExact (colorLoopGaugeAction c M) ↔
        ColorLoopTraceExact M
  trace_exact_nonempty :
    ColorLoopTraceExact (0 : ColorLoopField)
  prime_edge_trace_eq :
    ∀ n p q,
      colorLoopTrace (primeEdgeColorLoopMatrix n p q) =
        (p.1 : ℂ) + (q.1 : ℂ) - ((2 * n : ℕ) : ℂ)
  prime_edge_trace_zero_iff :
    ∀ n p q,
      colorLoopTrace (primeEdgeColorLoopMatrix n p q) = 0 ↔
        2 * n = p.1 + q.1
  prime_edge_traceExact_iff_edgeExact :
    ∀ n p q,
      ColorLoopTraceExact (primeEdgeColorLoopMatrix n p q) ↔
        ThreeAgentRingEdgeExact (primeEdgeThreeCycleCochain n p q)
  prime_edge_traceExact_witness :
    ColorLoopTraceExact
      (primeEdgeColorLoopMatrix 2 twoPrimeExponent twoPrimeExponent)
  prime_edge_obstructed_iff :
    ∀ n p q,
      PrimeEdgeColorLoopObstructed n p q ↔
        PrimeEdgeThreeCycleObstructed n p q
  prime_edge_obstructed_h1 :
    ∀ {n p q}, PrimeEdgeColorLoopObstructed n p q ->
      CechAdditiveCover.H1Obstruction
        (identityPairZeroTripleCover ThreeCycleTime Int)
        (primeEdgeThreeCycleCochain n p q)

/-- THEOREM 14: the color-loop trace bridge is fully machine-checked. -/
theorem p348ColorLoopTraceGoldbachBridgeCertificate :
    P348ColorLoopTraceGoldbachBridgeCertificate where
  action_one := colorLoopGaugeAction_one
  action_mul := colorLoopGaugeAction_mul
  trace_gauge_invariant := colorLoopTrace_gaugeInvariant
  trace_exact_gauge_invariant := colorLoopTraceExact_gaugeInvariant
  trace_exact_nonempty := colorLoopTraceExact_zero
  prime_edge_trace_eq := primeEdgeColorLoop_trace_eq
  prime_edge_trace_zero_iff := primeEdgeColorLoop_trace_zero_iff
  prime_edge_traceExact_iff_edgeExact :=
    primeEdgeColorLoop_traceExact_iff_edgeExact
  prime_edge_traceExact_witness := primeEdgeColorLoop_traceExact_two_two
  prime_edge_obstructed_iff := primeEdgeColorLoop_obstructed_iff
  prime_edge_obstructed_h1 := by
    intro n p q hobs
    exact primeEdgeColorLoop_obstructed_h1 hobs

end StandardModelConstraint
end SaturationMonoid
