import H0mework.Arithmetic.PrimeShadow.P881

/-!
# Proposition 882: prime-coded spectrum support forbids permanent holonomy

P881 showed that a prime-coded branching-spectrum generator gives a zero
prime-coded physical support cell on each even fiber.  P880 showed that
forbidding permanent prime-coded holonomy is exactly the strict successor law
needed for well-founded residual descent.

This file connects the two:

* a zero prime-coded support cell has energy `0`;
* every nonzero residual cell has positive energy;
* therefore the zero support cell is a strictly lower successor for every
  nonzero residual cell on the same fiber;
* hence fiberwise prime-coded spectrum support produces P880's physical
  holonomy-elimination confinement object.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Zero support cells as Lyapunov minima -/

/-- The physical zero support cell computed from a prime-coded spectrum
generator. -/
def primeCodedPhysicalZeroCell_of_spectrumGenerator
    {n : ℕ} (G : SU7PrimeCodedBranchingSpectrumGenerator n) :
    SU7PhysicalBranchCell n :=
  physicalBranchCell_of_primeCodedSpectrumCell G.supportCell

/-- THEOREM 1: the support cell computed from a prime-coded spectrum generator
has zero prime-coded residual. -/
theorem primeCodedPhysicalZeroCell_of_spectrumGenerator_residual_zero
    {n : ℕ} (G : SU7PrimeCodedBranchingSpectrumGenerator n) :
    primeCodedPhysicalResidual
        (primeCodedPhysicalZeroCell_of_spectrumGenerator G) = 0 :=
  primeCodedPhysicalResidual_zero_of_spectrumGenerator G

/-- THEOREM 2: the support cell computed from a prime-coded spectrum generator
has zero prime-coded residual energy. -/
theorem primeCodedPhysicalZeroCell_of_spectrumGenerator_energy_zero
    {n : ℕ} (G : SU7PrimeCodedBranchingSpectrumGenerator n) :
    primeCodedPhysicalResidualEnergy
        (primeCodedPhysicalZeroCell_of_spectrumGenerator G) = 0 := by
  exact
    (primeCodedPhysicalResidualEnergy_eq_zero_iff
      (primeCodedPhysicalZeroCell_of_spectrumGenerator G)).mpr
      (primeCodedPhysicalZeroCell_of_spectrumGenerator_residual_zero G)

/-- THEOREM 3: nonzero prime-coded residual means strictly positive residual
energy. -/
theorem primeCodedPhysicalResidualEnergy_pos_of_nonzero
    {n : ℕ} (cell : SU7PhysicalBranchCell n)
    (hnonzero : primeCodedPhysicalResidual cell ≠ 0) :
    0 < primeCodedPhysicalResidualEnergy cell := by
  apply Nat.pos_of_ne_zero
  intro henergy
  exact hnonzero
    ((primeCodedPhysicalResidualEnergy_eq_zero_iff cell).mp henergy)

/-- THEOREM 4: the generated zero support cell is a lower-energy successor for
every nonzero residual cell on the same fiber. -/
theorem zeroSupportCell_descends_nonzero
    {n : ℕ} (G : SU7PrimeCodedBranchingSpectrumGenerator n)
    (cell : SU7PhysicalBranchCell n)
    (hnonzero : primeCodedPhysicalResidual cell ≠ 0) :
    primeCodedPhysicalResidualEnergy
        (primeCodedPhysicalZeroCell_of_spectrumGenerator G) <
      primeCodedPhysicalResidualEnergy cell := by
  have hzero :
      primeCodedPhysicalResidualEnergy
        (primeCodedPhysicalZeroCell_of_spectrumGenerator G) = 0 :=
    primeCodedPhysicalZeroCell_of_spectrumGenerator_energy_zero G
  have hpos :
      0 < primeCodedPhysicalResidualEnergy cell :=
    primeCodedPhysicalResidualEnergy_pos_of_nonzero cell hnonzero
  simpa [hzero] using hpos

/-! ## Spectrum support produces holonomy elimination -/

/-- Spectrum-support confinement data: the physical law names plus a
prime-coded branching-spectrum support generator on every even fiber.

This stores no zero cell directly.  The zero cell is computed from each
generator's support cell. -/
structure SU7PrimeCodedSpectrumSupportConfinement where
  compact_gauge_orbit : SU7CompactGaugeOrbit
  lyapunov_residual_dissipation : SU7LyapunovResidualDissipation
  quantized_spectrum_no_escaping_boundary :
    SU7QuantizedSpectrumNoEscapingBoundary
  spectrum_generator :
    SU7PrimeCodedBranchingSpectrumGeneratorEveryEvenFiber

/-- The starting cell on a fiber is the physical zero support cell computed
from that fiber's prime-coded spectrum generator. -/
def startCell_of_primeCodedSpectrumSupport
    (D : SU7PrimeCodedSpectrumSupportConfinement)
    (n : ℕ) (hn : 2 ≤ n) :
    SU7PhysicalBranchCell n :=
  primeCodedPhysicalZeroCell_of_spectrumGenerator
    (Classical.choice (D.spectrum_generator n hn))

/-- THEOREM 5: spectrum support forbids permanent prime-coded color holonomy.
For any nonzero residual cell, the generated zero support cell is a strictly
lower-energy successor. -/
theorem noPermanentHolonomy_of_primeCodedSpectrumSupport
    (D : SU7PrimeCodedSpectrumSupportConfinement) :
    SU7PrimeCodedConfinementForbidsPermanentHolonomy := by
  intro n hn cell hperm
  rcases hperm with ⟨hnonzero, hterminal⟩
  let G : SU7PrimeCodedBranchingSpectrumGenerator n :=
    Classical.choice (D.spectrum_generator n hn)
  let zeroCell : SU7PhysicalBranchCell n :=
    primeCodedPhysicalZeroCell_of_spectrumGenerator G
  have hlt :
      primeCodedPhysicalResidualEnergy zeroCell <
        primeCodedPhysicalResidualEnergy cell :=
    zeroSupportCell_descends_nonzero G cell hnonzero
  exact hterminal zeroCell hlt

/-- THEOREM 6: spectrum-support confinement produces P880's holonomy
elimination confinement object. -/
def primeCodedPhysicalHolonomyElimination_of_spectrumSupport
    (D : SU7PrimeCodedSpectrumSupportConfinement) :
    SU7PrimeCodedPhysicalHolonomyEliminationConfinement where
  compact_gauge_orbit := D.compact_gauge_orbit
  lyapunov_residual_dissipation := D.lyapunov_residual_dissipation
  quantized_spectrum_no_escaping_boundary :=
    D.quantized_spectrum_no_escaping_boundary
  startCell := startCell_of_primeCodedSpectrumSupport D
  no_permanent_holonomy :=
    noPermanentHolonomy_of_primeCodedSpectrumSupport D

/-- THEOREM 7: spectrum-support confinement produces the prime-coded
well-founded confinement dynamics. -/
def primeCodedWellFoundedConfinementDynamics_of_spectrumSupport
    (D : SU7PrimeCodedSpectrumSupportConfinement) :
    SU7PrimeCodedWellFoundedConfinementDynamics :=
  primeCodedWellFoundedConfinementDynamics_of_physicalHolonomyElimination
    (primeCodedPhysicalHolonomyElimination_of_spectrumSupport D)

/-- THEOREM 8: spectrum-support confinement gives the ordinary even Goldbach
readout through the P881 -> P880 -> P879 chain. -/
theorem evenGoldbach_of_primeCodedSpectrumSupportConfinement
    (D : SU7PrimeCodedSpectrumSupportConfinement) :
    EvenGoldbachStatement :=
  evenGoldbach_of_primeCodedPhysicalHolonomyElimination
    (primeCodedPhysicalHolonomyElimination_of_spectrumSupport D)

/-! ## Certificate -/

/-- P882 certificate: prime-coded spectrum support is already strong enough to
forbid permanent holonomy and generate the P880/P879 descent route. -/
structure SU7PrimeCodedSpectrumSupportHolonomyCertificate where
  zero_cell_energy_zero :
    ∀ {n : ℕ} (G : SU7PrimeCodedBranchingSpectrumGenerator n),
      primeCodedPhysicalResidualEnergy
          (primeCodedPhysicalZeroCell_of_spectrumGenerator G) = 0
  nonzero_energy_positive :
    ∀ {n : ℕ} (cell : SU7PhysicalBranchCell n),
      primeCodedPhysicalResidual cell ≠ 0 ->
        0 < primeCodedPhysicalResidualEnergy cell
  zero_support_descends :
    ∀ {n : ℕ} (G : SU7PrimeCodedBranchingSpectrumGenerator n)
      (cell : SU7PhysicalBranchCell n),
      primeCodedPhysicalResidual cell ≠ 0 ->
        primeCodedPhysicalResidualEnergy
            (primeCodedPhysicalZeroCell_of_spectrumGenerator G) <
          primeCodedPhysicalResidualEnergy cell
  support_forbids_holonomy :
    SU7PrimeCodedSpectrumSupportConfinement ->
      SU7PrimeCodedConfinementForbidsPermanentHolonomy
  support_to_holonomy_elimination :
    SU7PrimeCodedSpectrumSupportConfinement ->
      SU7PrimeCodedPhysicalHolonomyEliminationConfinement
  support_to_well_founded :
    SU7PrimeCodedSpectrumSupportConfinement ->
      SU7PrimeCodedWellFoundedConfinementDynamics
  support_to_goldbach :
    SU7PrimeCodedSpectrumSupportConfinement ->
      EvenGoldbachStatement

def su7PrimeCodedSpectrumSupportHolonomyCertificate :
    SU7PrimeCodedSpectrumSupportHolonomyCertificate where
  zero_cell_energy_zero :=
    primeCodedPhysicalZeroCell_of_spectrumGenerator_energy_zero
  nonzero_energy_positive :=
    primeCodedPhysicalResidualEnergy_pos_of_nonzero
  zero_support_descends :=
    zeroSupportCell_descends_nonzero
  support_forbids_holonomy :=
    noPermanentHolonomy_of_primeCodedSpectrumSupport
  support_to_holonomy_elimination :=
    primeCodedPhysicalHolonomyElimination_of_spectrumSupport
  support_to_well_founded :=
    primeCodedWellFoundedConfinementDynamics_of_spectrumSupport
  support_to_goldbach :=
    evenGoldbach_of_primeCodedSpectrumSupportConfinement


end
end StandardModelConstraint
end SaturationMonoid
