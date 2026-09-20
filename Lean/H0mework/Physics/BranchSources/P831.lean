import H0mework.Arithmetic.CodePairs.P830
import H0mework.Realization.Residual.Algebra

/-!
# Proposition 831: trace gaps as residual-split permanent holonomy

P825 named a prime-edge trace-spectrum gap as permanent color holonomy.  This
file routes that statement through the truth-formula / residual-transport core:

* each color-loop trace defect is a scalar residual;
* an active keep `r ↦ (1 - σ) r` has fixed points only at `r = 0`;
* therefore a per-fiber trace-spectrum gap is exactly the statement that every
  prime-edge residual on that fiber is non-fixed, has nonzero forced trace, and
  has nonzero residual energy;
* SU(7) filtered confinement forbids that residual-split permanent holonomy and
  therefore yields the color-loop unit-bracket / fixed-point witness.
-/

noncomputable section

namespace SaturationMonoid

namespace StandardModelConstraint

open SaturationMonoid.AffineRelaxation

/-! ## Color-loop residual transport in the scalar truth-formula core -/

/-- The scalar keep used to read a color-loop trace defect as residual
transport. -/
abbrev colorLoopScalarKeep (sigma : ℝ) : ℝ →ₗ[ℝ] ℝ :=
  scalarKeepLinearMap (K := ℝ) (E := ℝ) sigma

/-- Positive-definite scalar residual energy for a trace defect. -/
def colorLoopScalarResidualEnergy (r : ℝ) : ℝ :=
  r ^ 2

/-- THEOREM 1: scalar trace-defect energy vanishes exactly at zero residual. -/
theorem colorLoopScalarResidualEnergy_zero_iff (r : ℝ) :
    colorLoopScalarResidualEnergy r = 0 ↔ r = 0 := by
  simp [colorLoopScalarResidualEnergy]

/-- THEOREM 2: for `σ ≠ 0`, the color-loop scalar keep is active. -/
theorem colorLoopScalarKeep_active_of_ne_zero
    (sigma : ℝ) (hsigma : sigma ≠ 0) :
    ResidualTransportActive (colorLoopScalarKeep sigma) :=
  scalarKeepLinearMap_active_of_ne_zero
    (K := ℝ) (E := ℝ) sigma hsigma

/-- THEOREM 3: a color-loop trace residual inherits the full truth-formula
collapse: fixed iff residual zero iff forced trace zero iff energy zero. -/
theorem colorLoopResidualSplitCoreEquivalence
    (sigma : ℝ) (hsigma : sigma ≠ 0)
    (n : ℕ) (p q : PrimeExponent) :
    TruthFormulaCoreEquivalence
      (colorLoopScalarKeep sigma)
      colorLoopScalarResidualEnergy
      (colorLoopTraceResidual n p q) :=
  residualTransportCore_equivalence
    (colorLoopScalarKeep sigma)
    colorLoopScalarResidualEnergy
    (colorLoopScalarKeep_active_of_ne_zero sigma hsigma)
    colorLoopScalarResidualEnergy_zero_iff
    (colorLoopTraceResidual n p q)

/-- A residual-split trace gap at `2n`: every prime-edge residual on that fiber
is non-fixed, produces nonzero forced trace, and has nonzero residual energy
under the active scalar keep. -/
def ColorLoopResidualSplitGap (sigma : ℝ) (n : ℕ) : Prop :=
  ∀ p q : PrimeExponent,
    ¬ ResidualTransportFixed
      (colorLoopScalarKeep sigma) (colorLoopTraceResidual n p q) ∧
    linearResidualTrace
      (colorLoopScalarKeep sigma) (colorLoopTraceResidual n p q) ≠ 0 ∧
    colorLoopScalarResidualEnergy (colorLoopTraceResidual n p q) ≠ 0

/-- THEOREM 4: under active scalar transport, the P825 trace-spectrum gap is
exactly residual-split non-fixed / nonzero-trace / nonzero-energy holonomy. -/
theorem primeEdgeTraceSpectrumGap_iff_residualSplitGap
    (sigma : ℝ) (hsigma : sigma ≠ 0) (n : ℕ) :
    PrimeEdgeTraceSpectrumGap n ↔
      ColorLoopResidualSplitGap sigma n := by
  constructor
  · intro hgap p q
    have hres_ne :
        colorLoopTraceResidual n p q ≠ 0 := by
      intro hzero
      exact hgap p q
        ((colorLoopTraceExact_iff_traceResidual_zero n p q).mpr hzero)
    have hcore :=
      colorLoopResidualSplitCoreEquivalence sigma hsigma n p q
    have hnot_fixed :
        ¬ ResidualTransportFixed
          (colorLoopScalarKeep sigma) (colorLoopTraceResidual n p q) := by
      intro hfixed
      exact hres_ne (hcore.fixed_iff_zero_residual.mp hfixed)
    refine ⟨hnot_fixed, ?_, ?_⟩
    · intro htrace
      exact hnot_fixed (hcore.fixed_iff_zero_trace.mpr htrace)
    · intro henergy
      exact hnot_fixed (hcore.fixed_iff_zero_energy.mpr henergy)
  · intro hsplit p q hexact
    rcases hsplit p q with ⟨hnot_fixed, _htrace, _henergy⟩
    have hcore :=
      colorLoopResidualSplitCoreEquivalence sigma hsigma n p q
    have hzero :
        colorLoopTraceResidual n p q = 0 :=
      (colorLoopTraceExact_iff_traceResidual_zero n p q).mp hexact
    exact hnot_fixed (hcore.fixed_iff_zero_residual.mpr hzero)

/-- Residual-split permanent holonomy: some even fiber has a trace gap when read
through active residual transport. -/
def ColorLoopResidualSplitPermanentHolonomy (sigma : ℝ) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ ColorLoopResidualSplitGap sigma n

/-- THEOREM 5: permanent color holonomy is exactly residual-split permanent
holonomy under any active scalar rate. -/
theorem permanentPrimeEdgeColorHolonomy_iff_residualSplitPermanentHolonomy
    (sigma : ℝ) (hsigma : sigma ≠ 0) :
    PermanentPrimeEdgeColorHolonomy ↔
      ColorLoopResidualSplitPermanentHolonomy sigma := by
  constructor
  · rintro ⟨n, hn, hgap⟩
    exact ⟨n, hn,
      (primeEdgeTraceSpectrumGap_iff_residualSplitGap sigma hsigma n).mp
        hgap⟩
  · rintro ⟨n, hn, hsplit⟩
    exact ⟨n, hn,
      (primeEdgeTraceSpectrumGap_iff_residualSplitGap sigma hsigma n).mpr
        hsplit⟩

/-- THEOREM 6: no residual-split permanent holonomy is the same no-gap
condition as no permanent color holonomy. -/
theorem noResidualSplitPermanentHolonomy_iff_noPermanentColorHolonomy
    (sigma : ℝ) (hsigma : sigma ≠ 0) :
    ¬ ColorLoopResidualSplitPermanentHolonomy sigma ↔
      ¬ PermanentPrimeEdgeColorHolonomy := by
  exact not_congr
    (permanentPrimeEdgeColorHolonomy_iff_residualSplitPermanentHolonomy
      sigma hsigma).symm

/-- THEOREM 7: a SU(7)-filtered producer forbids residual-split permanent
holonomy.  This is the confinement reading: permanent color holonomy cannot
survive in the filtered/traceless sector. -/
theorem noResidualSplitPermanentHolonomy_of_su7FilteredProducer
    (sigma : ℝ) (hsigma : sigma ≠ 0)
    (P : SU7FilteredPrimeEdgeLoopProducer) :
    ¬ ColorLoopResidualSplitPermanentHolonomy sigma := by
  have hno_color : ¬ PermanentPrimeEdgeColorHolonomy :=
    (noPermanentPrimeEdgeColorHolonomy_iff_su7FilteredProducer).mpr P
  exact
    (noResidualSplitPermanentHolonomy_iff_noPermanentColorHolonomy
      sigma hsigma).mpr hno_color

/-- THEOREM 8: once residual-split permanent holonomy is forbidden, Lean
extracts the data-level color-loop witness itself. -/
theorem colorLoopWitness_of_noResidualSplitPermanentHolonomy
    (sigma : ℝ) (hsigma : sigma ≠ 0)
    (hno : ¬ ColorLoopResidualSplitPermanentHolonomy sigma) :
    Nonempty ColorLoopUnitBracketFixedPointWitness := by
  have hno_color : ¬ PermanentPrimeEdgeColorHolonomy :=
    (noResidualSplitPermanentHolonomy_iff_noPermanentColorHolonomy
      sigma hsigma).mp hno
  have hunit : ColorLoopTraceUnitBracketProducer :=
    (noPermanentPrimeEdgeColorHolonomy_iff_unitBracketProducer).mp hno_color
  exact (nonemptyColorLoopWitness_iff_unitBracketProducer).mpr hunit

/-- THEOREM 9: a SU(7)-filtered producer directly yields the data-level
color-loop unit-bracket / fixed-point witness via the residual-split
no-permanent-holonomy route. -/
theorem colorLoopWitness_of_su7FilteredProducer
    (sigma : ℝ) (hsigma : sigma ≠ 0)
    (P : SU7FilteredPrimeEdgeLoopProducer) :
    Nonempty ColorLoopUnitBracketFixedPointWitness :=
  colorLoopWitness_of_noResidualSplitPermanentHolonomy sigma hsigma
    (noResidualSplitPermanentHolonomy_of_su7FilteredProducer
      sigma hsigma P)

/-! ## Certificate -/

/-- P831 certificate: the no-gap route is now explicitly a truth-formula
residual-split permanent-holonomy route. -/
structure ColorLoopResidualSplitPermanentHolonomyCertificate : Prop where
  scalar_energy_zero_iff :
    ∀ r : ℝ, colorLoopScalarResidualEnergy r = 0 ↔ r = 0
  scalar_keep_active :
    ∀ sigma : ℝ, sigma ≠ 0 ->
      ResidualTransportActive (colorLoopScalarKeep sigma)
  gap_iff_residual_split_gap :
    ∀ (sigma : ℝ), sigma ≠ 0 ->
      ∀ n : ℕ,
        (PrimeEdgeTraceSpectrumGap n ↔
          ColorLoopResidualSplitGap sigma n)
  permanent_iff_residual_split_permanent :
    ∀ (sigma : ℝ), sigma ≠ 0 ->
      (PermanentPrimeEdgeColorHolonomy ↔
        ColorLoopResidualSplitPermanentHolonomy sigma)
  confinement_forbids_residual_split_permanent :
    ∀ (sigma : ℝ), sigma ≠ 0 ->
      SU7FilteredPrimeEdgeLoopProducer ->
        ¬ ColorLoopResidualSplitPermanentHolonomy sigma
  no_residual_split_permanent_extracts_witness :
    ∀ (sigma : ℝ), sigma ≠ 0 ->
      ¬ ColorLoopResidualSplitPermanentHolonomy sigma ->
        Nonempty ColorLoopUnitBracketFixedPointWitness
  su7_filtered_extracts_witness :
    ∀ (sigma : ℝ), sigma ≠ 0 ->
      SU7FilteredPrimeEdgeLoopProducer ->
        Nonempty ColorLoopUnitBracketFixedPointWitness

/-- THEOREM 10: canonical residual-split permanent holonomy certificate. -/
theorem colorLoopResidualSplitPermanentHolonomyCertificate :
    ColorLoopResidualSplitPermanentHolonomyCertificate where
  scalar_energy_zero_iff :=
    colorLoopScalarResidualEnergy_zero_iff
  scalar_keep_active :=
    colorLoopScalarKeep_active_of_ne_zero
  gap_iff_residual_split_gap := by
    intro sigma hsigma n
    exact primeEdgeTraceSpectrumGap_iff_residualSplitGap sigma hsigma n
  permanent_iff_residual_split_permanent := by
    exact fun sigma hsigma =>
      permanentPrimeEdgeColorHolonomy_iff_residualSplitPermanentHolonomy
        sigma hsigma
  confinement_forbids_residual_split_permanent := by
    intro sigma hsigma P
    exact noResidualSplitPermanentHolonomy_of_su7FilteredProducer
      sigma hsigma P
  no_residual_split_permanent_extracts_witness := by
    intro sigma hsigma hno
    exact colorLoopWitness_of_noResidualSplitPermanentHolonomy
      sigma hsigma hno
  su7_filtered_extracts_witness := by
    intro sigma hsigma P
    exact colorLoopWitness_of_su7FilteredProducer sigma hsigma P

end StandardModelConstraint
end SaturationMonoid
