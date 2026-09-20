import H0mework.Physics.BranchSources.P831

/-!
# Proposition 832: SU(7) allowed-sector normal form

P831 routed trace gaps through residual-split permanent holonomy.  This file
closes the more primitive algebraic object: the allowed sector itself.

For each even fiber `2n`, an allowed prime-edge loop is a prime-edge loop
carrying the SU(7) color-adjoint filter.  Its canonical normal form is the
same prime-edge loop read in the trace-zero fiber.  Because P818 proves

`SU7ColorAdjointRepresentationFilter M ↔ ColorLoopTraceExact M`,

this normal form is total, prime-edge preserving, and unique.  The global
selector/witness is then the normal-form readout of a global allowed sector,
not an extra choice shell.
-/

noncomputable section

namespace SaturationMonoid

namespace StandardModelConstraint

open SaturationMonoid.AffineRelaxation
open GrandUnification

/-! ## Fiber-level allowed loops and trace-zero normal forms -/

/-- A concrete SU(7)-allowed prime-edge loop over the even fiber `2n`. -/
structure SU7AllowedPrimeEdgeLoop (n : ℕ) where
  leftPrime : AffineRelaxation.PrimeExponent
  rightPrime : AffineRelaxation.PrimeExponent
  allowed :
    SU7ColorAdjointRepresentationFilter
      (primeEdgeColorLoopMatrix n leftPrime rightPrime)

/-- The canonical trace-zero normal form of a prime-edge loop over `2n`. -/
structure TraceZeroPrimeEdgeLoop (n : ℕ) where
  leftPrime : AffineRelaxation.PrimeExponent
  rightPrime : AffineRelaxation.PrimeExponent
  trace_zero :
    ColorLoopTraceExact (primeEdgeColorLoopMatrix n leftPrime rightPrime)

/-- THEOREM 1: the SU(7) allowed sector has a total normal form into the
trace-zero prime-edge sector. -/
def su7AllowedPrimeEdgeLoopNormalForm
    {n : ℕ} (L : SU7AllowedPrimeEdgeLoop n) :
    TraceZeroPrimeEdgeLoop n where
  leftPrime := L.leftPrime
  rightPrime := L.rightPrime
  trace_zero :=
    (su7ColorAdjointRepresentationFilter_iff_traceExact
      (primeEdgeColorLoopMatrix n L.leftPrime L.rightPrime)).mp L.allowed

/-- THEOREM 2: trace-zero prime-edge loops canonically lift back to the
SU(7)-allowed sector. -/
def su7AllowedPrimeEdgeLoopOfTraceZero
    {n : ℕ} (Z : TraceZeroPrimeEdgeLoop n) :
    SU7AllowedPrimeEdgeLoop n where
  leftPrime := Z.leftPrime
  rightPrime := Z.rightPrime
  allowed :=
    (su7ColorAdjointRepresentationFilter_iff_traceExact
      (primeEdgeColorLoopMatrix n Z.leftPrime Z.rightPrime)).mpr
        Z.trace_zero

/-- THEOREM 3: the normal form preserves the first prime edge. -/
theorem su7AllowedPrimeEdgeLoopNormalForm_preserves_left
    {n : ℕ} (L : SU7AllowedPrimeEdgeLoop n) :
    ((su7AllowedPrimeEdgeLoopNormalForm L).leftPrime :
        AffineRelaxation.PrimeExponent) =
      (L.leftPrime : AffineRelaxation.PrimeExponent) :=
  rfl

/-- THEOREM 4: the normal form preserves the second prime edge. -/
theorem su7AllowedPrimeEdgeLoopNormalForm_preserves_right
    {n : ℕ} (L : SU7AllowedPrimeEdgeLoop n) :
    ((su7AllowedPrimeEdgeLoopNormalForm L).rightPrime :
        AffineRelaxation.PrimeExponent) =
      (L.rightPrime : AffineRelaxation.PrimeExponent) :=
  rfl

/-- THEOREM 5: the normal form lands in the zero trace fiber. -/
theorem su7AllowedPrimeEdgeLoopNormalForm_trace_zero
    {n : ℕ} (L : SU7AllowedPrimeEdgeLoop n) :
    ColorLoopTraceExact
      (primeEdgeColorLoopMatrix n
        (su7AllowedPrimeEdgeLoopNormalForm L).leftPrime
        (su7AllowedPrimeEdgeLoopNormalForm L).rightPrime) :=
  (su7AllowedPrimeEdgeLoopNormalForm L).trace_zero

/-- THEOREM 6: converting trace-zero to allowed and normalizing returns the
same trace-zero normal form. -/
theorem su7AllowedPrimeEdgeLoopNormalForm_right_inv
    {n : ℕ} (Z : TraceZeroPrimeEdgeLoop n) :
    su7AllowedPrimeEdgeLoopNormalForm
      (su7AllowedPrimeEdgeLoopOfTraceZero Z) = Z := by
  cases Z
  dsimp [su7AllowedPrimeEdgeLoopNormalForm,
    su7AllowedPrimeEdgeLoopOfTraceZero]

/-- THEOREM 7: normalizing an allowed loop and lifting it back returns the
same allowed loop. -/
theorem su7AllowedPrimeEdgeLoopNormalForm_left_inv
    {n : ℕ} (L : SU7AllowedPrimeEdgeLoop n) :
    su7AllowedPrimeEdgeLoopOfTraceZero
      (su7AllowedPrimeEdgeLoopNormalForm L) = L := by
  cases L
  dsimp [su7AllowedPrimeEdgeLoopNormalForm,
    su7AllowedPrimeEdgeLoopOfTraceZero]

/-- THEOREM 8: the allowed sector and trace-zero sector are canonically
equivalent on every prime-edge fiber. -/
def su7AllowedTraceZeroPrimeEdgeLoopEquiv (n : ℕ) :
    SU7AllowedPrimeEdgeLoop n ≃ TraceZeroPrimeEdgeLoop n where
  toFun := su7AllowedPrimeEdgeLoopNormalForm
  invFun := su7AllowedPrimeEdgeLoopOfTraceZero
  left_inv := su7AllowedPrimeEdgeLoopNormalForm_left_inv
  right_inv := su7AllowedPrimeEdgeLoopNormalForm_right_inv

/-- THEOREM 9: the normal form is unique: it is the only trace-zero form whose
canonical lift is the original allowed loop. -/
theorem su7AllowedPrimeEdgeLoopNormalForm_unique
    {n : ℕ} (L : SU7AllowedPrimeEdgeLoop n) :
    ∃! Z : TraceZeroPrimeEdgeLoop n,
      su7AllowedPrimeEdgeLoopOfTraceZero Z = L := by
  refine ⟨su7AllowedPrimeEdgeLoopNormalForm L,
    su7AllowedPrimeEdgeLoopNormalForm_left_inv L, ?_⟩
  intro Z hZ
  calc
    Z = su7AllowedPrimeEdgeLoopNormalForm
          (su7AllowedPrimeEdgeLoopOfTraceZero Z) := by
            exact (su7AllowedPrimeEdgeLoopNormalForm_right_inv Z).symm
    _ = su7AllowedPrimeEdgeLoopNormalForm L := by
            rw [hZ]

/-- THEOREM 10: the normal form is injective. -/
theorem su7AllowedPrimeEdgeLoopNormalForm_injective
    {n : ℕ} :
    Function.Injective
      (su7AllowedPrimeEdgeLoopNormalForm :
        SU7AllowedPrimeEdgeLoop n -> TraceZeroPrimeEdgeLoop n) := by
  intro L₁ L₂ h
  have hleft :
      su7AllowedPrimeEdgeLoopOfTraceZero
        (su7AllowedPrimeEdgeLoopNormalForm L₁) =
        su7AllowedPrimeEdgeLoopOfTraceZero
          (su7AllowedPrimeEdgeLoopNormalForm L₂) := by
    simpa using congrArg su7AllowedPrimeEdgeLoopOfTraceZero h
  simpa [su7AllowedPrimeEdgeLoopNormalForm_left_inv] using hleft

/-! ## Global allowed sectors and selector extraction -/

/-- A global SU(7) allowed prime-edge sector: for every even fiber, a concrete
allowed loop is produced before any selector is read out. -/
structure SU7AllowedPrimeEdgeSector where
  loop : (n : ℕ) -> 2 ≤ n -> SU7AllowedPrimeEdgeLoop n

/-- The global trace-zero normal form of an allowed sector. -/
structure TraceZeroPrimeEdgeSector where
  loop : (n : ℕ) -> 2 ≤ n -> TraceZeroPrimeEdgeLoop n

/-- THEOREM 11: global allowed sectors normalize fiberwise to trace-zero
sectors. -/
def su7AllowedPrimeEdgeSectorNormalForm
    (S : SU7AllowedPrimeEdgeSector) :
    TraceZeroPrimeEdgeSector where
  loop := fun n hn =>
    su7AllowedPrimeEdgeLoopNormalForm (S.loop n hn)

/-- THEOREM 12: a global allowed sector directly reads out the data-level
confinement selector. -/
def confinementSelectorOfAllowedPrimeEdgeSector
    (S : SU7AllowedPrimeEdgeSector) :
    SU7ConfinementPrimeEdgeSelector where
  pick := fun n hn =>
    (((su7AllowedPrimeEdgeSectorNormalForm S).loop n hn).leftPrime,
      ((su7AllowedPrimeEdgeSectorNormalForm S).loop n hn).rightPrime)
  filtered := by
    intro n hn
    exact
      (su7ColorAdjointRepresentationFilter_iff_traceExact
        (primeEdgeColorLoopMatrix n
          ((su7AllowedPrimeEdgeSectorNormalForm S).loop n hn).leftPrime
          ((su7AllowedPrimeEdgeSectorNormalForm S).loop n hn).rightPrime)).mpr
        ((su7AllowedPrimeEdgeSectorNormalForm S).loop n hn).trace_zero

/-- THEOREM 13: the selector extracted from a global allowed sector preserves
the underlying prime-edge endpoints. -/
theorem confinementSelectorOfAllowedPrimeEdgeSector_pick_eq
    (S : SU7AllowedPrimeEdgeSector)
    (n : ℕ) (hn : 2 ≤ n) :
    (confinementSelectorOfAllowedPrimeEdgeSector S).pick n hn =
      ((S.loop n hn).leftPrime, (S.loop n hn).rightPrime) := by
  simp [confinementSelectorOfAllowedPrimeEdgeSector,
    su7AllowedPrimeEdgeSectorNormalForm,
    su7AllowedPrimeEdgeLoopNormalForm]

/-- THEOREM 14: a global allowed sector produces the color-loop
unit-bracket/fixed-point witness through normal form. -/
def colorLoopWitnessOfAllowedPrimeEdgeSector
    (S : SU7AllowedPrimeEdgeSector) :
    ColorLoopUnitBracketFixedPointWitness :=
  colorLoopUnitBracketFixedPointWitnessOfConfinementSelector
    (confinementSelectorOfAllowedPrimeEdgeSector S)

/-- THEOREM 15: the witness extracted from an allowed sector uses exactly the
normal-form endpoints. -/
theorem colorLoopWitnessOfAllowedPrimeEdgeSector_pick_eq
    (S : SU7AllowedPrimeEdgeSector)
    (n : ℕ) (hn : 2 ≤ n) :
    (colorLoopWitnessOfAllowedPrimeEdgeSector S).pick n hn =
      ((S.loop n hn).leftPrime, (S.loop n hn).rightPrime) := by
  simp [colorLoopWitnessOfAllowedPrimeEdgeSector,
    colorLoopUnitBracketFixedPointWitnessOfConfinementSelector,
    confinementSelectorOfAllowedPrimeEdgeSector,
    su7AllowedPrimeEdgeSectorNormalForm,
    su7AllowedPrimeEdgeLoopNormalForm]

/-! ## Certificate -/

/-- P832 certificate: the allowed sector has a canonical trace-zero normal
form; selector and witness extraction are readouts of that normal form. -/
structure SU7AllowedSectorNormalFormCertificate where
  fiber_equiv :
    ∀ n : ℕ, SU7AllowedPrimeEdgeLoop n ≃ TraceZeroPrimeEdgeLoop n
  normal_form_preserves_left :
    ∀ {n : ℕ} (L : SU7AllowedPrimeEdgeLoop n),
      ((su7AllowedPrimeEdgeLoopNormalForm L).leftPrime :
          AffineRelaxation.PrimeExponent) =
        (L.leftPrime : AffineRelaxation.PrimeExponent)
  normal_form_preserves_right :
    ∀ {n : ℕ} (L : SU7AllowedPrimeEdgeLoop n),
      ((su7AllowedPrimeEdgeLoopNormalForm L).rightPrime :
          AffineRelaxation.PrimeExponent) =
        (L.rightPrime : AffineRelaxation.PrimeExponent)
  normal_form_trace_zero :
    ∀ {n : ℕ} (L : SU7AllowedPrimeEdgeLoop n),
      ColorLoopTraceExact
        (primeEdgeColorLoopMatrix n
          (su7AllowedPrimeEdgeLoopNormalForm L).leftPrime
          (su7AllowedPrimeEdgeLoopNormalForm L).rightPrime)
  normal_form_unique :
    ∀ {n : ℕ} (L : SU7AllowedPrimeEdgeLoop n),
      ∃! Z : TraceZeroPrimeEdgeLoop n,
        su7AllowedPrimeEdgeLoopOfTraceZero Z = L
  normal_form_injective :
    ∀ {n : ℕ},
      Function.Injective
        (su7AllowedPrimeEdgeLoopNormalForm :
          SU7AllowedPrimeEdgeLoop n -> TraceZeroPrimeEdgeLoop n)
  allowed_sector_extracts_selector :
    SU7AllowedPrimeEdgeSector -> SU7ConfinementPrimeEdgeSelector
  allowed_sector_extracts_witness :
    SU7AllowedPrimeEdgeSector -> ColorLoopUnitBracketFixedPointWitness
  selector_pick_is_normal_form :
    ∀ (S : SU7AllowedPrimeEdgeSector)
      (n : ℕ) (hn : 2 ≤ n),
      (confinementSelectorOfAllowedPrimeEdgeSector S).pick n hn =
        ((S.loop n hn).leftPrime, (S.loop n hn).rightPrime)

/-- THEOREM 16: canonical SU(7) allowed-sector normal-form certificate. -/
def su7AllowedSectorNormalFormCertificate :
    SU7AllowedSectorNormalFormCertificate where
  fiber_equiv := su7AllowedTraceZeroPrimeEdgeLoopEquiv
  normal_form_preserves_left :=
    su7AllowedPrimeEdgeLoopNormalForm_preserves_left
  normal_form_preserves_right :=
    su7AllowedPrimeEdgeLoopNormalForm_preserves_right
  normal_form_trace_zero :=
    su7AllowedPrimeEdgeLoopNormalForm_trace_zero
  normal_form_unique :=
    su7AllowedPrimeEdgeLoopNormalForm_unique
  normal_form_injective := by
    intro n
    exact su7AllowedPrimeEdgeLoopNormalForm_injective
  allowed_sector_extracts_selector :=
    confinementSelectorOfAllowedPrimeEdgeSector
  allowed_sector_extracts_witness :=
    colorLoopWitnessOfAllowedPrimeEdgeSector
  selector_pick_is_normal_form :=
    confinementSelectorOfAllowedPrimeEdgeSector_pick_eq

end StandardModelConstraint
end SaturationMonoid
