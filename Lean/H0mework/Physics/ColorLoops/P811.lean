import H0mework.Physics.ColorLoops.P348
import H0mework.Computation.SelfReduction.P697

/-!
# Proposition 811: color-loop trace residual as Lyapunov dissipation

P348 proves that the prime-edge color loop `diag(p,q,-2n)` has trace
`p + q - 2n`, so trace zero is exactly the selected Goldbach pair equation.
P697 proves that a residual transported by `r -> (1 - sigma) r` has geometric
Lyapunov energy decay.

This file welds those two facts: the color-loop trace defect is a one-coordinate
residual carrier, and its squared trace energy is dissipated by the same
Lyapunov law.  The Goldbach condition is the zero-energy / trace-exact fiber of
that carrier.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open Filter
open ComplexityProjection
open SaturationMonoid.AffineRelaxation

/-! ## Trace residual carrier for a prime-edge color loop -/

/-- The real trace residual of the prime-edge color loop
`diag(p,q,-2n)`. -/
def colorLoopTraceResidual (n : ℕ) (p q : PrimeExponent) : ℝ :=
  (p.1 : ℝ) + (q.1 : ℝ) - ((2 * n : ℕ) : ℝ)

/-- The one-coordinate residual surface used to feed the P697 Lyapunov
certificate. -/
def colorLoopTraceResidualFunction
    (n : ℕ) (p q : PrimeExponent) : Unit -> ℝ :=
  fun _ => colorLoopTraceResidual n p q

/-- Squared trace-residual energy. -/
def colorLoopTraceEnergy (n : ℕ) (p q : PrimeExponent) : ℝ :=
  (colorLoopTraceResidual n p q) ^ 2

/-- Iterated Lyapunov energy of the color-loop trace residual. -/
def colorLoopTraceRelaxIterateEnergy
    (sigma : ℝ) (steps n : ℕ) (p q : PrimeExponent) : ℝ :=
  phaseResidualEnergy
    (phaseResidualRelaxIterate sigma steps
      (colorLoopTraceResidualFunction n p q))

/-! ## The trace residual is exactly the Goldbach defect -/

/-- THEOREM 1: the real part of the P348 complex trace is the real trace
residual. -/
theorem colorLoopTraceResidual_eq_trace_re
    (n : ℕ) (p q : PrimeExponent) :
    (colorLoopTrace (primeEdgeColorLoopMatrix n p q)).re =
      colorLoopTraceResidual n p q := by
  rw [primeEdgeColorLoop_trace_eq]
  simp [colorLoopTraceResidual]

/-- THEOREM 2: zero trace residual is exactly the selected Goldbach pair
equation `p + q = 2n`. -/
theorem colorLoopTraceResidual_zero_iff_goldbach_pair
    (n : ℕ) (p q : PrimeExponent) :
    colorLoopTraceResidual n p q = 0 ↔
      2 * n = p.1 + q.1 := by
  unfold colorLoopTraceResidual
  constructor
  · intro h
    have h' : ((p.1 + q.1 : ℕ) : ℝ) = ((2 * n : ℕ) : ℝ) := by
      norm_num at h ⊢
      linear_combination h
    exact_mod_cast h'.symm
  · intro h
    rw [h]
    norm_num

/-- THEOREM 3: P348 trace-exactness is the zero fiber of the real trace
residual. -/
theorem colorLoopTraceExact_iff_traceResidual_zero
    (n : ℕ) (p q : PrimeExponent) :
    ColorLoopTraceExact (primeEdgeColorLoopMatrix n p q) ↔
      colorLoopTraceResidual n p q = 0 := by
  rw [ColorLoopTraceExact, primeEdgeColorLoop_trace_zero_iff,
    colorLoopTraceResidual_zero_iff_goldbach_pair]

/-- THEOREM 4: zero trace-residual energy is exactly the selected Goldbach pair
equation. -/
theorem colorLoopTraceEnergy_zero_iff_goldbach_pair
    (n : ℕ) (p q : PrimeExponent) :
    colorLoopTraceEnergy n p q = 0 ↔
      2 * n = p.1 + q.1 := by
  rw [colorLoopTraceEnergy, sq_eq_zero_iff,
    colorLoopTraceResidual_zero_iff_goldbach_pair]

/-- THEOREM 5: the one-coordinate P697 residual energy is exactly the
color-loop trace energy. -/
theorem colorLoopTraceResidualFunction_energy_eq
    (n : ℕ) (p q : PrimeExponent) :
    phaseResidualEnergy (colorLoopTraceResidualFunction n p q) =
      colorLoopTraceEnergy n p q := by
  simp [phaseResidualEnergy, colorLoopTraceResidualFunction,
    colorLoopTraceEnergy]

/-! ## Lyapunov transport of the trace residual -/

/-- THEOREM 6: after `steps` residual-transport steps, the color-loop trace
energy is multiplied by `((1 - sigma)^2)^steps`. -/
theorem colorLoopTraceRelaxIterateEnergy_eq
    (sigma : ℝ) (steps n : ℕ) (p q : PrimeExponent) :
    colorLoopTraceRelaxIterateEnergy sigma steps n p q =
      ((1 - sigma) ^ 2) ^ steps *
        colorLoopTraceEnergy n p q := by
  rw [colorLoopTraceRelaxIterateEnergy,
    phaseResidualEnergy_relax_iterate_eq,
    colorLoopTraceResidualFunction_energy_eq]

/-- THEOREM 7: finite color-loop trace transport is Lyapunov nonincreasing for
runtime rates `0 <= sigma <= 1`. -/
theorem colorLoopTraceRelaxIterateEnergy_nonincreasing
    (sigma : ℝ) (steps n : ℕ) (p q : PrimeExponent)
    (h0 : 0 <= sigma) (h1 : sigma <= 1) :
    colorLoopTraceRelaxIterateEnergy sigma steps n p q <=
      colorLoopTraceEnergy n p q := by
  calc
    colorLoopTraceRelaxIterateEnergy sigma steps n p q =
        phaseResidualEnergy
          (phaseResidualRelaxIterate sigma steps
            (colorLoopTraceResidualFunction n p q)) := rfl
    _ <= phaseResidualEnergy (colorLoopTraceResidualFunction n p q) :=
        phaseResidualEnergy_relax_iterate_nonincreasing
          sigma steps (colorLoopTraceResidualFunction n p q) h0 h1
    _ = colorLoopTraceEnergy n p q :=
        colorLoopTraceResidualFunction_energy_eq n p q

/-- THEOREM 8: for `0 < sigma < 1`, iterated color-loop trace energy tends to
zero. -/
theorem tendsto_colorLoopTraceRelaxIterateEnergy_zero
    (sigma : ℝ) (n : ℕ) (p q : PrimeExponent)
    (h0 : 0 < sigma) (h1 : sigma < 1) :
    Tendsto (fun steps : ℕ =>
      colorLoopTraceRelaxIterateEnergy sigma steps n p q)
      atTop (nhds (0 : ℝ)) := by
  unfold colorLoopTraceRelaxIterateEnergy
  exact tendsto_phaseResidualEnergy_relax_iterate_zero
    sigma (colorLoopTraceResidualFunction n p q) h0 h1

/-- THEOREM 9: under positive subunit rate, any finite relaxed zero-energy
state is already a Goldbach-pair zero trace state.  The Lyapunov flow dissipates
energy geometrically; finite exact zero still characterizes the original
trace-exact fiber. -/
theorem colorLoopTraceRelaxIterateEnergy_zero_iff_goldbach_pair
    (sigma : ℝ) (steps n : ℕ) (p q : PrimeExponent)
    (_hσ0 : 0 < sigma) (hσ1 : sigma < 1) :
    colorLoopTraceRelaxIterateEnergy sigma steps n p q = 0 ↔
      2 * n = p.1 + q.1 := by
  rw [colorLoopTraceRelaxIterateEnergy_eq]
  have hbase_pos : 0 < (1 - sigma) ^ 2 := by
    apply sq_pos_of_ne_zero
    nlinarith [hσ1]
  have hfactor_ne : ((1 - sigma) ^ 2) ^ steps ≠ 0 :=
    (pow_pos hbase_pos steps).ne'
  constructor
  · intro h
    have hE : colorLoopTraceEnergy n p q = 0 := by
      exact (mul_eq_zero.mp h).resolve_left hfactor_ne
    exact (colorLoopTraceEnergy_zero_iff_goldbach_pair n p q).mp hE
  · intro h
    have hE :
        colorLoopTraceEnergy n p q = 0 :=
      (colorLoopTraceEnergy_zero_iff_goldbach_pair n p q).mpr h
    simp [hE]

/-! ## Certificate packaging -/

/-- P811 certificate: P348's color-loop trace bridge is the same one-coordinate
residual carrier as P697's Lyapunov dissipation law. -/
structure ColorLoopTraceLyapunovGoldbachCertificate : Prop where
  p348_trace_bridge :
    P348ColorLoopTraceGoldbachBridgeCertificate
  p697_iterated_lyapunov :
    SATPhaseFlowIteratedLyapunovCertificate.{0, 0}
  trace_residual_eq_trace_re :
    ∀ (n : ℕ) (p q : PrimeExponent),
      (colorLoopTrace (primeEdgeColorLoopMatrix n p q)).re =
        colorLoopTraceResidual n p q
  trace_residual_zero_iff_goldbach_pair :
    ∀ (n : ℕ) (p q : PrimeExponent),
      colorLoopTraceResidual n p q = 0 ↔
        2 * n = p.1 + q.1
  trace_exact_iff_trace_residual_zero :
    ∀ (n : ℕ) (p q : PrimeExponent),
      ColorLoopTraceExact (primeEdgeColorLoopMatrix n p q) ↔
        colorLoopTraceResidual n p q = 0
  energy_zero_iff_goldbach_pair :
    ∀ (n : ℕ) (p q : PrimeExponent),
      colorLoopTraceEnergy n p q = 0 ↔
        2 * n = p.1 + q.1
  relax_iterate_energy_eq :
    ∀ (sigma : ℝ) (steps n : ℕ) (p q : PrimeExponent),
      colorLoopTraceRelaxIterateEnergy sigma steps n p q =
        ((1 - sigma) ^ 2) ^ steps *
          colorLoopTraceEnergy n p q
  relax_iterate_energy_nonincreasing :
    ∀ (sigma : ℝ) (steps n : ℕ) (p q : PrimeExponent),
      0 <= sigma -> sigma <= 1 ->
        colorLoopTraceRelaxIterateEnergy sigma steps n p q <=
          colorLoopTraceEnergy n p q
  relax_iterate_energy_tendsto_zero :
    ∀ (sigma : ℝ) (n : ℕ) (p q : PrimeExponent),
      0 < sigma -> sigma < 1 ->
        Tendsto (fun steps : ℕ =>
          colorLoopTraceRelaxIterateEnergy sigma steps n p q)
          atTop (nhds (0 : ℝ))
  finite_zero_iff_goldbach_pair :
    ∀ (sigma : ℝ) (steps n : ℕ) (p q : PrimeExponent),
      0 < sigma -> sigma < 1 ->
        (colorLoopTraceRelaxIterateEnergy sigma steps n p q = 0 ↔
          2 * n = p.1 + q.1)

/-- THEOREM 10: the color-loop trace residual has a certified Lyapunov
Goldbach face. -/
theorem colorLoopTraceLyapunovGoldbachCertificate :
    ColorLoopTraceLyapunovGoldbachCertificate where
  p348_trace_bridge :=
    p348ColorLoopTraceGoldbachBridgeCertificate
  p697_iterated_lyapunov :=
    satPhaseFlowIteratedLyapunovCertificate
  trace_residual_eq_trace_re :=
    colorLoopTraceResidual_eq_trace_re
  trace_residual_zero_iff_goldbach_pair :=
    colorLoopTraceResidual_zero_iff_goldbach_pair
  trace_exact_iff_trace_residual_zero :=
    colorLoopTraceExact_iff_traceResidual_zero
  energy_zero_iff_goldbach_pair :=
    colorLoopTraceEnergy_zero_iff_goldbach_pair
  relax_iterate_energy_eq :=
    colorLoopTraceRelaxIterateEnergy_eq
  relax_iterate_energy_nonincreasing :=
    colorLoopTraceRelaxIterateEnergy_nonincreasing
  relax_iterate_energy_tendsto_zero :=
    tendsto_colorLoopTraceRelaxIterateEnergy_zero
  finite_zero_iff_goldbach_pair :=
    colorLoopTraceRelaxIterateEnergy_zero_iff_goldbach_pair

end StandardModelConstraint
end SaturationMonoid
