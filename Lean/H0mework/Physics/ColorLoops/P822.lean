import H0mework.Arithmetic.PrimeShadow.P821

/-!
# Proposition 822: the color-loop producer core, and the Lyapunov no-shortcut

P816/P755/P821 identify the remaining front:

* `ColorLoopTraceUnitBracketProducer`;
* `Nonempty EvenGoldbachDynamicalFixedPointProducer`;
* explicit prime-pair production;
* ordinary even Goldbach.

This file makes the producer core executable as a normal form and rules out a
tempting false shortcut.  P811's Lyapunov theorem says every fixed prime-pair
trace residual dissipates asymptotically under `r ↦ (1 - σ) r`; that is not a
finite integer crossing theorem.  A nonzero integer trace can tend to zero in
energy without ever becoming zero at a finite step.

So the producer cannot be "Lyapunov convergence" alone.  It must supply the
discrete zero fiber: equivalently an explicit prime-pair selector, or the unit
trace bracket whose endpoint is forced to be zero.
-/

noncomputable section

namespace SaturationMonoid

namespace StandardModelConstraint

open Filter
open SaturationMonoid.AffineRelaxation

set_option linter.checkUnivs false
set_option linter.defProp false

/-! ## Producer normal form -/

/-- THEOREM 1: the color-loop unit-bracket producer is exactly an explicit
global prime-pair selector. -/
theorem colorLoopTraceUnitBracketProducer_iff_primePairProducer :
    ColorLoopTraceUnitBracketProducer ↔
      Nonempty EvenGoldbachPrimePairProducer := by
  exact colorLoopTraceUnitBracketProducer_iff_evenGoldbach.trans
    evenGoldbachPrimePairProducer_iff_goldbach.symm

/-- THEOREM 2: the color-loop unit-bracket producer is exactly the certified
global dynamical fixed-point producer. -/
theorem colorLoopTraceUnitBracketProducer_iff_fixedPointProducer :
    ColorLoopTraceUnitBracketProducer ↔
      Nonempty EvenGoldbachDynamicalFixedPointProducer := by
  exact colorLoopTraceUnitBracketProducer_iff_evenGoldbach.trans
    evenGoldbachDynamicalFixedPointProducer_iff_goldbach.symm

/-- Extract the explicit prime-pair selector carried by a unit-bracket
producer.  The extraction goes through the endpoint-zero theorem from P816;
this is the concrete content hidden inside any proposed color-loop producer. -/
noncomputable def primePairProducerOfUnitBracket
    (P : ColorLoopTraceUnitBracketProducer) :
    EvenGoldbachPrimePairProducer :=
  Classical.choice
    ((colorLoopTraceUnitBracketProducer_iff_primePairProducer).mp P)

/-- THEOREM 3: the selector extracted from a unit-bracket producer really sums
to each even target. -/
theorem primePairProducerOfUnitBracket_sum
    (P : ColorLoopTraceUnitBracketProducer)
    (n : ℕ) (hn : 2 ≤ n) :
    2 * n =
      ((primePairProducerOfUnitBracket P).pick n hn).1.1 +
        ((primePairProducerOfUnitBracket P).pick n hn).2.1 :=
  (primePairProducerOfUnitBracket P).sum_pick n hn

/-- Build a unit-bracket producer from a certified fixed-point producer. -/
noncomputable def unitBracketProducerOfFixedPoint
    (P : EvenGoldbachDynamicalFixedPointProducer) :
    ColorLoopTraceUnitBracketProducer :=
  colorLoopTraceUnitBracketProducer_of_evenGoldbach
    ((evenGoldbachDynamicalFixedPointProducer_iff_goldbach).mp ⟨P⟩)

/-- Build a certified fixed-point producer from a unit-bracket producer. -/
noncomputable def fixedPointProducerOfUnitBracket
    (P : ColorLoopTraceUnitBracketProducer) :
    EvenGoldbachDynamicalFixedPointProducer :=
  Classical.choice
    ((colorLoopTraceUnitBracketProducer_iff_fixedPointProducer).mp P)

/-- THEOREM 4: the fixed-point producer extracted from a unit-bracket producer
is fixed at every even target. -/
theorem fixedPointProducerOfUnitBracket_fixed
    (P : ColorLoopTraceUnitBracketProducer)
    (n : ℕ) (hn : 2 ≤ n) :
    goldbachDynamicalFixedPoint (2 * n)
      ((fixedPointProducerOfUnitBracket P).pick n hn) :=
  (fixedPointProducerOfUnitBracket P).fixed n hn

/-! ## Lyapunov convergence is not finite trace production -/

/-- THEOREM 5: for every `n >= 3`, the fixed prime pair `(2,2)` is a nonzero
color-loop trace residual for the target `2n`. -/
theorem colorLoopTraceResidual_two_two_ne_zero_of_three_le
    (n : ℕ) (hn : 3 ≤ n) :
    colorLoopTraceResidual n primeTwo primeTwo ≠ 0 := by
  intro hzero
  have hsum :
      2 * n = primeTwo.1 + primeTwo.1 :=
    (colorLoopTraceResidual_zero_iff_goldbach_pair n primeTwo primeTwo).mp
      hzero
  norm_num [primeTwo] at hsum
  omega

/-- THEOREM 6: the `(2,2)` trace energy is nonzero for every target `2n` with
`n >= 3`. -/
theorem colorLoopTraceEnergy_two_two_ne_zero_of_three_le
    (n : ℕ) (hn : 3 ≤ n) :
    colorLoopTraceEnergy n primeTwo primeTwo ≠ 0 := by
  intro henergy
  have hres :
      colorLoopTraceResidual n primeTwo primeTwo = 0 := by
    simpa [colorLoopTraceEnergy] using (sq_eq_zero_iff.mp henergy)
  exact colorLoopTraceResidual_two_two_ne_zero_of_three_le n hn hres

/-- THEOREM 7: despite the nonzero trace residual, Lyapunov transport still
drives the `(2,2)` trace energy to zero asymptotically.  Thus asymptotic
dissipation alone is too weak to produce a finite integer zero fiber. -/
theorem tendsto_colorLoopTraceEnergy_two_two_zero_even_when_nonzero
    (sigma : ℝ) (n : ℕ)
    (hσ0 : 0 < sigma) (hσ1 : sigma < 1) (_hn : 3 ≤ n) :
    Tendsto
      (fun steps : ℕ =>
        colorLoopTraceRelaxIterateEnergy sigma steps n primeTwo primeTwo)
      atTop (nhds (0 : ℝ)) :=
  tendsto_colorLoopTraceRelaxIterateEnergy_zero
    sigma n primeTwo primeTwo hσ0 hσ1

/-- THEOREM 8: on any active sigma fiber, the same obstructed `(2,2)` trace
state never hits exact zero at a finite step for targets `2n`, `n >= 3`. -/
theorem colorLoopTraceRelaxIterateEnergy_two_two_ne_zero_of_three_le
    (sigma : ℝ) (steps n : ℕ)
    (hσ0 : 0 < sigma) (hσ1 : sigma < 1) (hn : 3 ≤ n) :
    colorLoopTraceRelaxIterateEnergy sigma steps n primeTwo primeTwo ≠ 0 := by
  intro hzero
  have hsum :
      2 * n = primeTwo.1 + primeTwo.1 :=
    (colorLoopTraceRelaxIterateEnergy_zero_iff_goldbach_pair
      sigma steps n primeTwo primeTwo hσ0 hσ1).mp hzero
  norm_num [primeTwo] at hsum
  omega

/-- Compact certificate: the remaining color-loop producer has the explicit
prime-pair / fixed-point normal form, and the raw Lyapunov convergence theorem
does not by itself create the finite unit bracket. -/
structure ColorLoopProducerCoreCertificate : Prop where
  unit_bracket_iff_prime_pair :
    ColorLoopTraceUnitBracketProducer ↔
      Nonempty EvenGoldbachPrimePairProducer
  unit_bracket_iff_fixed_point :
    ColorLoopTraceUnitBracketProducer ↔
      Nonempty EvenGoldbachDynamicalFixedPointProducer
  extracted_pair_sums :
    ∀ (P : ColorLoopTraceUnitBracketProducer) (n : ℕ) (hn : 2 ≤ n),
      2 * n =
        ((primePairProducerOfUnitBracket P).pick n hn).1.1 +
          ((primePairProducerOfUnitBracket P).pick n hn).2.1
  extracted_fixed_point :
    ∀ (P : ColorLoopTraceUnitBracketProducer) (n : ℕ) (hn : 2 ≤ n),
      goldbachDynamicalFixedPoint (2 * n)
        ((fixedPointProducerOfUnitBracket P).pick n hn)
  lyapunov_tends_zero_for_nonzero_trace :
    ∀ (sigma : ℝ) (n : ℕ),
      0 < sigma -> sigma < 1 -> 3 ≤ n ->
        Tendsto
          (fun steps : ℕ =>
            colorLoopTraceRelaxIterateEnergy sigma steps n primeTwo primeTwo)
          atTop (nhds (0 : ℝ))
  finite_zero_not_from_obstructed_trace :
    ∀ (sigma : ℝ) (steps n : ℕ),
      0 < sigma -> sigma < 1 -> 3 ≤ n ->
        colorLoopTraceRelaxIterateEnergy sigma steps n primeTwo primeTwo ≠ 0

/-- THEOREM 9: canonical producer-core / Lyapunov no-shortcut certificate. -/
theorem colorLoopProducerCoreCertificate :
    ColorLoopProducerCoreCertificate where
  unit_bracket_iff_prime_pair :=
    colorLoopTraceUnitBracketProducer_iff_primePairProducer
  unit_bracket_iff_fixed_point :=
    colorLoopTraceUnitBracketProducer_iff_fixedPointProducer
  extracted_pair_sums :=
    primePairProducerOfUnitBracket_sum
  extracted_fixed_point :=
    fixedPointProducerOfUnitBracket_fixed
  lyapunov_tends_zero_for_nonzero_trace := by
    intro sigma n hσ0 hσ1 hn
    exact tendsto_colorLoopTraceEnergy_two_two_zero_even_when_nonzero
      sigma n hσ0 hσ1 hn
  finite_zero_not_from_obstructed_trace := by
    intro sigma steps n hσ0 hσ1 hn
    exact colorLoopTraceRelaxIterateEnergy_two_two_ne_zero_of_three_le
      sigma steps n hσ0 hσ1 hn

end StandardModelConstraint
end SaturationMonoid
