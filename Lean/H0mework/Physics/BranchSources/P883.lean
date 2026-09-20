import H0mework.Arithmetic.PrimeShadow.P882

/-!
# Proposition 883: spectrum-level descent produces zero support

P881's `SU7PrimeCodedBranchingSpectrumGenerator` still stores a support cell
whose prime-coded residual is already zero.  P882 then uses that support cell
to forbid permanent holonomy.

This file pushes the producer one layer lower.  A spectrum descent orbit stores
only:

* a finite prime-coded SU(7) spectrum family;
* one positive-weight starting cell;
* a strict spectrum-internal Lyapunov successor law for nonzero residual cells.

Lean then extracts a positive-weight zero-residual support cell by strong
induction on the natural-number residual energy, producing P881's generator
without storing the zero support as primitive data.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Spectrum-level residual energy -/

/-- Prime-coded residual energy of a SU(7) branching-spectrum cell. -/
def primeCodedSpectrumResidualEnergy
    {n : ℕ} (C : SU7PrimeCodedBranchingSpectrumCell n) : ℕ :=
  Int.natAbs C.primeCodedResidual

/-- THEOREM 1: zero spectrum residual energy is zero spectrum residual. -/
theorem primeCodedSpectrumResidualEnergy_eq_zero_iff
    {n : ℕ} (C : SU7PrimeCodedBranchingSpectrumCell n) :
    primeCodedSpectrumResidualEnergy C = 0 ↔
      C.primeCodedResidual = 0 := by
  unfold primeCodedSpectrumResidualEnergy
  rw [Int.natAbs_eq_zero]

/-- THEOREM 2: nonzero spectrum residual means strictly positive spectrum
residual energy. -/
theorem primeCodedSpectrumResidualEnergy_pos_of_nonzero
    {n : ℕ} (C : SU7PrimeCodedBranchingSpectrumCell n)
    (hnonzero : C.primeCodedResidual ≠ 0) :
    0 < primeCodedSpectrumResidualEnergy C := by
  apply Nat.pos_of_ne_zero
  intro henergy
  exact hnonzero
    ((primeCodedSpectrumResidualEnergy_eq_zero_iff C).mp henergy)

/-! ## Spectrum descent orbits -/

/-- A spectrum-level Lyapunov descent orbit.

The successor law is internal to the spectrum family and preserves positive
representation weight.  It does not store a zero support cell. -/
structure SU7PrimeCodedBranchingSpectrumDescentOrbit (n : ℕ) where
  family : SU7PrimeCodedBranchingSpectrumFamily n
  startCell : SU7PrimeCodedBranchingSpectrumCell n
  start_mem : startCell ∈ family.spectrumCells
  start_weight_positive : 0 < family.representationWeight startCell
  lyapunov_descends_nonzero :
    ∀ C : SU7PrimeCodedBranchingSpectrumCell n,
      C ∈ family.spectrumCells ->
        0 < family.representationWeight C ->
          C.primeCodedResidual ≠ 0 ->
            ∃ next : SU7PrimeCodedBranchingSpectrumCell n,
              next ∈ family.spectrumCells ∧
                0 < family.representationWeight next ∧
                  primeCodedSpectrumResidualEnergy next <
                    primeCodedSpectrumResidualEnergy C

/-- THEOREM 3: a spectrum descent orbit produces a positive-weight
zero-residual support cell. -/
theorem exists_zeroSupport_of_spectrumDescentOrbit
    {n : ℕ} (O : SU7PrimeCodedBranchingSpectrumDescentOrbit n) :
    ∃ Z : SU7PrimeCodedBranchingSpectrumCell n,
      Z ∈ O.family.spectrumCells ∧
        0 < O.family.representationWeight Z ∧
          Z.primeCodedResidual = 0 := by
  let motive : ℕ -> Prop := fun e =>
    ∀ C : SU7PrimeCodedBranchingSpectrumCell n,
      C ∈ O.family.spectrumCells ->
        0 < O.family.representationWeight C ->
          primeCodedSpectrumResidualEnergy C = e ->
            ∃ Z : SU7PrimeCodedBranchingSpectrumCell n,
              Z ∈ O.family.spectrumCells ∧
                0 < O.family.representationWeight Z ∧
                  Z.primeCodedResidual = 0
  have hstep : ∀ e : ℕ, (∀ e' < e, motive e') -> motive e := by
    intro e ih C hmem hwt henergy
    by_cases hzero : C.primeCodedResidual = 0
    · exact ⟨C, hmem, hwt, hzero⟩
    · rcases O.lyapunov_descends_nonzero C hmem hwt hzero with
        ⟨next, hnext_mem, hnext_wt, hnext_lt⟩
      exact ih (primeCodedSpectrumResidualEnergy next)
        (by simpa [henergy] using hnext_lt)
        next hnext_mem hnext_wt rfl
  have hstart : motive (primeCodedSpectrumResidualEnergy O.startCell) :=
    Nat.strong_induction_on
      (primeCodedSpectrumResidualEnergy O.startCell) hstep
  exact hstart O.startCell O.start_mem O.start_weight_positive rfl

/-- THEOREM 4: a spectrum descent orbit computes P881's prime-coded
branching-spectrum generator. -/
def primeCodedSpectrumGenerator_of_descentOrbit
    {n : ℕ} (O : SU7PrimeCodedBranchingSpectrumDescentOrbit n) :
    SU7PrimeCodedBranchingSpectrumGenerator n :=
  let Z := Classical.choose (exists_zeroSupport_of_spectrumDescentOrbit O)
  let hZ := Classical.choose_spec
    (exists_zeroSupport_of_spectrumDescentOrbit O)
  { family := O.family
    supportCell := Z
    support_mem := hZ.1
    support_weight_positive := hZ.2.1
    support_primeCodedResidual_zero := hZ.2.2 }

/-! ## Fiberwise descent produces P882's support-confinement route -/

/-- Every even fiber carries a prime-coded spectrum descent orbit. -/
def SU7PrimeCodedBranchingSpectrumDescentOrbitEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7PrimeCodedBranchingSpectrumDescentOrbit n)

/-- THEOREM 5: fiberwise spectrum descent produces P881's fiberwise
prime-coded spectrum generators. -/
theorem primeCodedSpectrumGeneratorEveryEvenFiber_of_descentOrbit
    (H : SU7PrimeCodedBranchingSpectrumDescentOrbitEveryEvenFiber) :
    SU7PrimeCodedBranchingSpectrumGeneratorEveryEvenFiber := by
  intro n hn
  rcases H n hn with ⟨O⟩
  exact ⟨primeCodedSpectrumGenerator_of_descentOrbit O⟩

/-- Spectrum-descent confinement data: physical law names plus a spectrum-level
descent orbit on every even fiber. -/
structure SU7PrimeCodedSpectrumDescentConfinement where
  compact_gauge_orbit : SU7CompactGaugeOrbit
  lyapunov_residual_dissipation : SU7LyapunovResidualDissipation
  quantized_spectrum_no_escaping_boundary :
    SU7QuantizedSpectrumNoEscapingBoundary
  spectrum_descent :
    SU7PrimeCodedBranchingSpectrumDescentOrbitEveryEvenFiber

/-- THEOREM 6: spectrum-descent confinement produces P882's spectrum-support
confinement object. -/
def primeCodedSpectrumSupportConfinement_of_descent
    (D : SU7PrimeCodedSpectrumDescentConfinement) :
    SU7PrimeCodedSpectrumSupportConfinement where
  compact_gauge_orbit := D.compact_gauge_orbit
  lyapunov_residual_dissipation := D.lyapunov_residual_dissipation
  quantized_spectrum_no_escaping_boundary :=
    D.quantized_spectrum_no_escaping_boundary
  spectrum_generator :=
    primeCodedSpectrumGeneratorEveryEvenFiber_of_descentOrbit
      D.spectrum_descent

/-- THEOREM 7: spectrum-descent confinement produces P880's holonomy
elimination object. -/
def primeCodedPhysicalHolonomyElimination_of_spectrumDescent
    (D : SU7PrimeCodedSpectrumDescentConfinement) :
    SU7PrimeCodedPhysicalHolonomyEliminationConfinement :=
  primeCodedPhysicalHolonomyElimination_of_spectrumSupport
    (primeCodedSpectrumSupportConfinement_of_descent D)

/-- THEOREM 8: spectrum-descent confinement gives the ordinary even Goldbach
readout through the spectrum -> support -> holonomy-elimination chain. -/
theorem evenGoldbach_of_primeCodedSpectrumDescentConfinement
    (D : SU7PrimeCodedSpectrumDescentConfinement) :
    EvenGoldbachStatement :=
  evenGoldbach_of_primeCodedSpectrumSupportConfinement
    (primeCodedSpectrumSupportConfinement_of_descent D)

/-! ## Certificate -/

/-- P883 certificate: spectrum-internal Lyapunov descent generates the zero
support cell required by P881/P882. -/
structure SU7PrimeCodedSpectrumDescentProducerCertificate where
  energy_zero_iff :
    ∀ {n : ℕ} (C : SU7PrimeCodedBranchingSpectrumCell n),
      primeCodedSpectrumResidualEnergy C = 0 ↔
        C.primeCodedResidual = 0
  nonzero_energy_positive :
    ∀ {n : ℕ} (C : SU7PrimeCodedBranchingSpectrumCell n),
      C.primeCodedResidual ≠ 0 ->
        0 < primeCodedSpectrumResidualEnergy C
  descent_to_zero_support :
    ∀ {n : ℕ} (O : SU7PrimeCodedBranchingSpectrumDescentOrbit n),
      ∃ Z : SU7PrimeCodedBranchingSpectrumCell n,
        Z ∈ O.family.spectrumCells ∧
          0 < O.family.representationWeight Z ∧
            Z.primeCodedResidual = 0
  descent_to_generator :
    ∀ {n : ℕ}, SU7PrimeCodedBranchingSpectrumDescentOrbit n ->
      SU7PrimeCodedBranchingSpectrumGenerator n
  every_fiber_to_generator :
    SU7PrimeCodedBranchingSpectrumDescentOrbitEveryEvenFiber ->
      SU7PrimeCodedBranchingSpectrumGeneratorEveryEvenFiber
  descent_to_support_confinement :
    SU7PrimeCodedSpectrumDescentConfinement ->
      SU7PrimeCodedSpectrumSupportConfinement
  descent_to_holonomy_elimination :
    SU7PrimeCodedSpectrumDescentConfinement ->
      SU7PrimeCodedPhysicalHolonomyEliminationConfinement
  descent_to_goldbach :
    SU7PrimeCodedSpectrumDescentConfinement ->
      EvenGoldbachStatement

def su7PrimeCodedSpectrumDescentProducerCertificate :
    SU7PrimeCodedSpectrumDescentProducerCertificate where
  energy_zero_iff :=
    primeCodedSpectrumResidualEnergy_eq_zero_iff
  nonzero_energy_positive :=
    primeCodedSpectrumResidualEnergy_pos_of_nonzero
  descent_to_zero_support :=
    exists_zeroSupport_of_spectrumDescentOrbit
  descent_to_generator :=
    primeCodedSpectrumGenerator_of_descentOrbit
  every_fiber_to_generator :=
    primeCodedSpectrumGeneratorEveryEvenFiber_of_descentOrbit
  descent_to_support_confinement :=
    primeCodedSpectrumSupportConfinement_of_descent
  descent_to_holonomy_elimination :=
    primeCodedPhysicalHolonomyElimination_of_spectrumDescent
  descent_to_goldbach :=
    evenGoldbach_of_primeCodedSpectrumDescentConfinement


end
end StandardModelConstraint
end SaturationMonoid
