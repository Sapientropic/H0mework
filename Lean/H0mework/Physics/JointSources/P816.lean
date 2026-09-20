import H0mework.Arithmetic.PrimeShadow.P815

/-!
# Proposition 816: discrete trace crossing forces the zero fiber

P815 names the Lyapunov even-crossing producer.  This file lowers the next
producer debt by one layer.

The new primitive is a discrete trace bracket: for each even point, the
color-loop trace has an integer-valued prime-edge state on the nonnegative side
and one on the nonpositive side, and the two trace values differ by at most
one.  Since the trace observable is integer-valued on prime-edge loops, such a
unit bracket must hit the zero fiber exactly.

This is the formal version of the phrase:

`trace is decreasing, and at integer points crossing zero means exact zero`.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open SaturationMonoid.AffineRelaxation

/-! ## Integer trace defect -/

/-- Integer-valued trace defect of the prime-edge color loop. -/
def colorLoopTraceDefectInt
    (n : ℕ) (p q : PrimeExponent) : ℤ :=
  (p.1 : ℤ) + (q.1 : ℤ) - (((2 * n : ℕ) : ℤ))

/-- THEOREM 1: integer trace defect zero is exactly the selected Goldbach pair
equation. -/
theorem colorLoopTraceDefectInt_zero_iff_goldbach_pair
    (n : ℕ) (p q : PrimeExponent) :
    colorLoopTraceDefectInt n p q = 0 ↔
      2 * n = p.1 + q.1 := by
  unfold colorLoopTraceDefectInt
  constructor
  · intro h
    have h' : ((p.1 + q.1 : ℕ) : ℤ) = ((2 * n : ℕ) : ℤ) := by
      norm_num at h ⊢
      linear_combination h
    exact_mod_cast h'.symm
  · intro h
    rw [h]
    norm_num

/-- THEOREM 2: the integer trace defect and the real trace residual have the
same zero fiber. -/
theorem colorLoopTraceDefectInt_zero_iff_traceResidual_zero
    (n : ℕ) (p q : PrimeExponent) :
    colorLoopTraceDefectInt n p q = 0 ↔
      colorLoopTraceResidual n p q = 0 := by
  rw [colorLoopTraceDefectInt_zero_iff_goldbach_pair,
    colorLoopTraceResidual_zero_iff_goldbach_pair]

/-! ## Unit brackets force zero -/

/-- Pure integer lemma: a unit jump from the nonnegative side to the
nonpositive side must touch zero. -/
theorem int_zero_of_unit_bracket
    (a b : ℤ) (ha : 0 <= a) (hb : b <= 0) (hstep : a - b <= 1) :
    a = 0 ∨ b = 0 := by
  by_cases ha0 : a = 0
  · exact Or.inl ha0
  · right
    have ha1 : 1 <= a := by
      omega
    have hb0 : 0 <= b := by
      omega
    exact le_antisymm hb hb0

/-- A unit trace bracket for the even point `2n`: one prime-edge loop is on
the nonnegative side, one on the nonpositive side, and their integer trace
defects are adjacent enough that no nonzero integer can fit between them. -/
def ColorLoopTraceUnitBracket
    (n : ℕ) (pHi qHi pLo qLo : PrimeExponent) : Prop :=
  0 <= colorLoopTraceDefectInt n pHi qHi ∧
    colorLoopTraceDefectInt n pLo qLo <= 0 ∧
      colorLoopTraceDefectInt n pHi qHi -
        colorLoopTraceDefectInt n pLo qLo <= 1

/-- THEOREM 3: a unit trace bracket contains a Goldbach pair at one endpoint. -/
theorem colorLoopTraceUnitBracket_goldbach_endpoint
    {n : ℕ} {pHi qHi pLo qLo : PrimeExponent}
    (hbracket : ColorLoopTraceUnitBracket n pHi qHi pLo qLo) :
    2 * n = pHi.1 + qHi.1 ∨
      2 * n = pLo.1 + qLo.1 := by
  rcases hbracket with ⟨hhi, hlo, hstep⟩
  have hzero :=
    int_zero_of_unit_bracket
      (colorLoopTraceDefectInt n pHi qHi)
      (colorLoopTraceDefectInt n pLo qLo)
      hhi hlo hstep
  cases hzero with
  | inl hz =>
      exact Or.inl
        ((colorLoopTraceDefectInt_zero_iff_goldbach_pair n pHi qHi).mp hz)
  | inr hz =>
      exact Or.inr
        ((colorLoopTraceDefectInt_zero_iff_goldbach_pair n pLo qLo).mp hz)

/-- A global unit-bracket producer for all even exponents. -/
def ColorLoopTraceUnitBracketProducer : Prop :=
  ∀ n : ℕ, 2 <= n ->
    ∃ pHi qHi pLo qLo : PrimeExponent,
      ColorLoopTraceUnitBracket n pHi qHi pLo qLo

/-- THEOREM 4: unit brackets imply ordinary Goldbach. -/
theorem evenGoldbach_of_colorLoopTraceUnitBracketProducer
    (producer : ColorLoopTraceUnitBracketProducer) :
    EvenGoldbachStatement := by
  intro n hn
  rcases producer n hn with ⟨pHi, qHi, pLo, qLo, hbracket⟩
  cases colorLoopTraceUnitBracket_goldbach_endpoint hbracket with
  | inl hpair =>
      exact ⟨pHi, qHi, hpair⟩
  | inr hpair =>
      exact ⟨pLo, qLo, hpair⟩

/-- THEOREM 5: ordinary Goldbach gives the degenerate unit bracket whose two
endpoints are already the zero fiber. -/
theorem colorLoopTraceUnitBracketProducer_of_evenGoldbach
    (goldbach : EvenGoldbachStatement) :
    ColorLoopTraceUnitBracketProducer := by
  intro n hn
  rcases goldbach n hn with ⟨p, q, hpair⟩
  refine ⟨p, q, p, q, ?_⟩
  have hzero :
      colorLoopTraceDefectInt n p q = 0 :=
    (colorLoopTraceDefectInt_zero_iff_goldbach_pair n p q).mpr hpair
  simp [ColorLoopTraceUnitBracket, hzero]

/-- THEOREM 6: the unit-bracket producer is exactly ordinary Goldbach. -/
theorem colorLoopTraceUnitBracketProducer_iff_evenGoldbach :
    ColorLoopTraceUnitBracketProducer ↔
      EvenGoldbachStatement := by
  constructor
  · exact evenGoldbach_of_colorLoopTraceUnitBracketProducer
  · exact colorLoopTraceUnitBracketProducer_of_evenGoldbach

/-- THEOREM 7: on any active real sigma-fiber, the unit-bracket producer gives
the P815 Lyapunov even-crossing producer. -/
theorem colorLoopTraceLyapunovEvenCrossing_of_unitBracketProducer
    {sigma : ℝ} (hσ0 : 0 < sigma) (hσ1 : sigma < 1)
    (producer : ColorLoopTraceUnitBracketProducer) :
    ColorLoopTraceLyapunovEvenCrossingProducer sigma := by
  exact
    (colorLoopTraceLyapunovEvenCrossing_iff_evenGoldbach
      hσ0 hσ1).mpr
      (evenGoldbach_of_colorLoopTraceUnitBracketProducer producer)

/-- THEOREM 8: on any active real sigma-fiber, unit-bracket production and
Lyapunov even-crossing have the same strength. -/
theorem colorLoopTraceUnitBracketProducer_iff_evenCrossing
    {sigma : ℝ} (hσ0 : 0 < sigma) (hσ1 : sigma < 1) :
    ColorLoopTraceUnitBracketProducer ↔
      ColorLoopTraceLyapunovEvenCrossingProducer sigma := by
  rw [colorLoopTraceUnitBracketProducer_iff_evenGoldbach,
    colorLoopTraceLyapunovEvenCrossing_iff_evenGoldbach hσ0 hσ1]

/-- THEOREM 9: on any active real sigma-fiber, unit brackets are exactly the
sigma-atomic binary `satOr` cover. -/
theorem colorLoopTraceUnitBracketProducer_iff_sigmaAtomicCover
    {sigma : ℝ} (hσ0 : 0 < sigma) (hσ1 : sigma < 1) :
    ColorLoopTraceUnitBracketProducer ↔
      SigmaAtomicSatOrCoversEvenCarrier sigma (ne_of_lt hσ1) := by
  rw [colorLoopTraceUnitBracketProducer_iff_evenGoldbach,
    atomicSatOrCover_iff_evenGoldbach_of_mem_Ioo hσ0 hσ1]

/-! ## Certificate packaging -/

/-- P816 certificate: the remaining even-crossing producer can be attacked as
a discrete integer trace-bracket producer. -/
structure ColorLoopTraceDiscreteCrossingCertificate
    (sigma : ℝ) (hσ0 : 0 < sigma) (hσ1 : sigma < 1) : Prop where
  int_defect_zero_iff_goldbach_pair :
    ∀ (n : ℕ) (p q : PrimeExponent),
      colorLoopTraceDefectInt n p q = 0 ↔
        2 * n = p.1 + q.1
  unit_bracket_forces_endpoint_zero :
    ∀ {n : ℕ} {pHi qHi pLo qLo : PrimeExponent},
      ColorLoopTraceUnitBracket n pHi qHi pLo qLo ->
        2 * n = pHi.1 + qHi.1 ∨
          2 * n = pLo.1 + qLo.1
  unit_bracket_iff_goldbach :
    ColorLoopTraceUnitBracketProducer ↔
      EvenGoldbachStatement
  unit_bracket_iff_even_crossing :
    ColorLoopTraceUnitBracketProducer ↔
      ColorLoopTraceLyapunovEvenCrossingProducer sigma
  unit_bracket_iff_sigma_atomic_cover :
    ColorLoopTraceUnitBracketProducer ↔
      SigmaAtomicSatOrCoversEvenCarrier sigma (ne_of_lt hσ1)

/-- THEOREM 10: canonical discrete crossing certificate. -/
theorem colorLoopTraceDiscreteCrossingCertificate
    {sigma : ℝ} (hσ0 : 0 < sigma) (hσ1 : sigma < 1) :
    ColorLoopTraceDiscreteCrossingCertificate sigma hσ0 hσ1 where
  int_defect_zero_iff_goldbach_pair :=
    colorLoopTraceDefectInt_zero_iff_goldbach_pair
  unit_bracket_forces_endpoint_zero := by
    intro n pHi qHi pLo qLo hbracket
    exact colorLoopTraceUnitBracket_goldbach_endpoint hbracket
  unit_bracket_iff_goldbach :=
    colorLoopTraceUnitBracketProducer_iff_evenGoldbach
  unit_bracket_iff_even_crossing :=
    colorLoopTraceUnitBracketProducer_iff_evenCrossing hσ0 hσ1
  unit_bracket_iff_sigma_atomic_cover :=
    colorLoopTraceUnitBracketProducer_iff_sigmaAtomicCover hσ0 hσ1

end StandardModelConstraint
end SaturationMonoid
