import H0mework.Arithmetic.PrimeShadow.P879

/-!
# Proposition 880: prime-coded permanent holonomy elimination

P879 moved the color-loop residual to the canonical prime-coded atom readout.
This file closes the next producer step on that route:

* a nonzero prime-coded residual branch cell with no lower-energy successor is
  permanent prime-coded color holonomy;
* confinement forbids such permanent holonomy;
* therefore every nonzero prime-coded residual cell has a lower-energy
  successor;
* hence P879's well-founded prime-coded dynamics is generated without storing a
  zero cell and without assuming `SU7AtomCodePrimeProjectionLaw`.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Prime-coded permanent holonomy -/

/-- A physical branch cell carries permanent prime-coded color holonomy exactly
when its prime-coded residual is nonzero and the prime-coded Lyapunov order has
no strictly lower successor. -/
def SU7PrimeCodedPermanentHolonomyCell
    {n : ℕ} (cell : SU7PhysicalBranchCell n) : Prop :=
  primeCodedPhysicalResidual cell ≠ 0 ∧
    ∀ next : SU7PhysicalBranchCell n,
      ¬ primeCodedPhysicalResidualEnergy next <
        primeCodedPhysicalResidualEnergy cell

/-- Confinement forbids permanent prime-coded physical color holonomy on every
even fiber. -/
def SU7PrimeCodedConfinementForbidsPermanentHolonomy : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    ∀ cell : SU7PhysicalBranchCell n,
      ¬ SU7PrimeCodedPermanentHolonomyCell cell

/-- THEOREM 1: forbidding permanent prime-coded holonomy is exactly the strict
successor law needed by P879's well-founded Lyapunov descent. -/
theorem noPrimeCodedPermanentHolonomy_iff_successorLaw :
    SU7PrimeCodedConfinementForbidsPermanentHolonomy ↔
      ∀ n : ℕ, 2 ≤ n ->
        ∀ cell : SU7PhysicalBranchCell n,
          primeCodedPhysicalResidual cell ≠ 0 ->
            ∃ next : SU7PhysicalBranchCell n,
              primeCodedPhysicalResidualEnergy next <
                primeCodedPhysicalResidualEnergy cell := by
  constructor
  · intro H n hn cell hnonzero
    by_contra hnone
    have hterminal :
        ∀ next : SU7PhysicalBranchCell n,
          ¬ primeCodedPhysicalResidualEnergy next <
            primeCodedPhysicalResidualEnergy cell := by
      intro next hlt
      exact hnone ⟨next, hlt⟩
    exact H n hn cell ⟨hnonzero, hterminal⟩
  · intro H n hn cell hperm
    rcases hperm with ⟨hnonzero, hterminal⟩
    rcases H n hn cell hnonzero with ⟨next, hlt⟩
    exact hterminal next hlt

/-- Direct successor extraction from confinement's no-permanent-holonomy law. -/
theorem successor_of_noPrimeCodedPermanentHolonomy
    (H : SU7PrimeCodedConfinementForbidsPermanentHolonomy)
    {n : ℕ} (hn : 2 ≤ n) (cell : SU7PhysicalBranchCell n)
    (hnonzero : primeCodedPhysicalResidual cell ≠ 0) :
    ∃ next : SU7PhysicalBranchCell n,
      primeCodedPhysicalResidualEnergy next <
        primeCodedPhysicalResidualEnergy cell :=
  (noPrimeCodedPermanentHolonomy_iff_successorLaw.mp H) n hn cell hnonzero

/-! ## Prime-coded confinement as holonomy elimination -/

/-- Prime-coded physical confinement data below zero-cell storage.

The fiberwise producer content is:

* a starting physical branch cell;
* no permanent prime-coded physical holonomy.

The zero residual cell is generated later by P879's well-founded descent. -/
structure SU7PrimeCodedPhysicalHolonomyEliminationConfinement where
  compact_gauge_orbit : SU7CompactGaugeOrbit
  lyapunov_residual_dissipation : SU7LyapunovResidualDissipation
  quantized_spectrum_no_escaping_boundary :
    SU7QuantizedSpectrumNoEscapingBoundary
  startCell :
    ∀ n : ℕ, 2 ≤ n -> SU7PhysicalBranchCell n
  no_permanent_holonomy :
    SU7PrimeCodedConfinementForbidsPermanentHolonomy

/-- THEOREM 2: prime-coded physical holonomy elimination generates the
well-founded orbit required by P879 on one even fiber. -/
def primeCodedWellFoundedOrbit_of_physicalHolonomyElimination
    (D : SU7PrimeCodedPhysicalHolonomyEliminationConfinement)
    (n : ℕ) (hn : 2 ≤ n) :
    SU7PrimeCodedWellFoundedPhysicalOrbit n where
  startCell := D.startCell n hn
  lyapunov_descends_nonzero := by
    intro cell hnonzero
    exact successor_of_noPrimeCodedPermanentHolonomy
      D.no_permanent_holonomy hn cell hnonzero

/-- THEOREM 3: prime-coded physical holonomy elimination produces P879's
well-founded confinement dynamics. -/
def primeCodedWellFoundedConfinementDynamics_of_physicalHolonomyElimination
    (D : SU7PrimeCodedPhysicalHolonomyEliminationConfinement) :
    SU7PrimeCodedWellFoundedConfinementDynamics where
  compact_gauge_orbit := D.compact_gauge_orbit
  lyapunov_residual_dissipation := D.lyapunov_residual_dissipation
  quantized_spectrum_no_escaping_boundary :=
    D.quantized_spectrum_no_escaping_boundary
  orbit := primeCodedWellFoundedOrbit_of_physicalHolonomyElimination D

/-- THEOREM 4: prime-coded physical holonomy elimination reaches a zero
prime-coded physical cell on every even fiber. -/
theorem primeCodedZeroCellEveryEvenFiber_of_physicalHolonomyElimination
    (D : SU7PrimeCodedPhysicalHolonomyEliminationConfinement) :
    ∀ n : ℕ, 2 ≤ n ->
      ∃ cell : SU7PhysicalBranchCell n,
        primeCodedPhysicalResidual cell = 0 := by
  intro n hn
  exact exists_zeroCell_of_primeCodedWellFoundedLyapunovOrbit
    ((primeCodedWellFoundedConfinementDynamics_of_physicalHolonomyElimination
      D).orbit n hn)

/-- THEOREM 5: prime-coded physical holonomy elimination gives ordinary even
Goldbach directly through P879's canonical prime readout. -/
theorem evenGoldbach_of_primeCodedPhysicalHolonomyElimination
    (D : SU7PrimeCodedPhysicalHolonomyEliminationConfinement) :
    EvenGoldbachStatement :=
  evenGoldbach_of_primeCodedWellFoundedConfinement
    (primeCodedWellFoundedConfinementDynamics_of_physicalHolonomyElimination D)

/-! ## Certificate -/

/-- P880 certificate: permanent prime-coded physical holonomy elimination is
the exact producer of P879's strict Lyapunov successor law and its Goldbach
readout, with no external atom-code prime projection law. -/
structure SU7PrimeCodedPhysicalHolonomyEliminationProducerCertificate where
  no_permanent_iff_successor :
    SU7PrimeCodedConfinementForbidsPermanentHolonomy ↔
      ∀ n : ℕ, 2 ≤ n ->
        ∀ cell : SU7PhysicalBranchCell n,
          primeCodedPhysicalResidual cell ≠ 0 ->
            ∃ next : SU7PhysicalBranchCell n,
              primeCodedPhysicalResidualEnergy next <
                primeCodedPhysicalResidualEnergy cell
  to_well_founded :
    SU7PrimeCodedPhysicalHolonomyEliminationConfinement ->
      SU7PrimeCodedWellFoundedConfinementDynamics
  to_zero_fibers :
    SU7PrimeCodedPhysicalHolonomyEliminationConfinement ->
      ∀ n : ℕ, 2 ≤ n ->
        ∃ cell : SU7PhysicalBranchCell n,
          primeCodedPhysicalResidual cell = 0
  to_goldbach :
    SU7PrimeCodedPhysicalHolonomyEliminationConfinement ->
      EvenGoldbachStatement

def su7PrimeCodedPhysicalHolonomyEliminationProducerCertificate :
    SU7PrimeCodedPhysicalHolonomyEliminationProducerCertificate where
  no_permanent_iff_successor :=
    noPrimeCodedPermanentHolonomy_iff_successorLaw
  to_well_founded :=
    primeCodedWellFoundedConfinementDynamics_of_physicalHolonomyElimination
  to_zero_fibers :=
    primeCodedZeroCellEveryEvenFiber_of_physicalHolonomyElimination
  to_goldbach :=
    evenGoldbach_of_primeCodedPhysicalHolonomyElimination


end
end StandardModelConstraint
end SaturationMonoid
