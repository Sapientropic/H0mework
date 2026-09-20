import H0mework.Physics.JointSources.P875

/-!
# Proposition 876: physical permanent holonomy elimination produces descent

P875 proves that a starting cell plus strict natural-number Lyapunov descent
reaches a zero-residual physical cell.

This file identifies the strict successor law with the physical confinement
reading requested by the proof spine:

* a nonzero residual branch cell with no lower-energy successor is a permanent
  physical color holonomy;
* confinement forbids such permanent holonomy;
* therefore every nonzero residual cell has a lower-energy successor;
* hence P875's well-founded descent dynamics is generated without storing a
  zero cell, a minimum, or prime-edge data.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

set_option linter.defProp false

/-! ## Physical permanent holonomy -/

/-- A physical branch cell carries permanent color holonomy exactly when its
residual is nonzero and the physical Lyapunov order has no strictly lower
successor. -/
def SU7PhysicalPermanentHolonomyCell
    {n : ℕ} (cell : SU7PhysicalBranchCell n) : Prop :=
  physicalResidual cell ≠ 0 ∧
    ∀ next : SU7PhysicalBranchCell n,
      ¬ physicalResidualEnergy next < physicalResidualEnergy cell

/-- Confinement forbids permanent physical color holonomy on every even fiber. -/
def SU7PhysicalConfinementForbidsPermanentHolonomy : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    ∀ cell : SU7PhysicalBranchCell n,
      ¬ SU7PhysicalPermanentHolonomyCell cell

/-- THEOREM 1: forbidding permanent physical holonomy is exactly the strict
successor law needed by well-founded Lyapunov descent. -/
theorem noPermanentPhysicalHolonomy_iff_successorLaw :
    SU7PhysicalConfinementForbidsPermanentHolonomy ↔
      ∀ n : ℕ, 2 ≤ n ->
        ∀ cell : SU7PhysicalBranchCell n,
          physicalResidual cell ≠ 0 ->
            ∃ next : SU7PhysicalBranchCell n,
              physicalResidualEnergy next < physicalResidualEnergy cell := by
  constructor
  · intro H n hn cell hnonzero
    by_contra hnone
    have hterminal :
        ∀ next : SU7PhysicalBranchCell n,
          ¬ physicalResidualEnergy next < physicalResidualEnergy cell := by
      intro next hlt
      exact hnone ⟨next, hlt⟩
    exact H n hn cell ⟨hnonzero, hterminal⟩
  · intro H n hn cell hperm
    rcases hperm with ⟨hnonzero, hterminal⟩
    rcases H n hn cell hnonzero with ⟨next, hlt⟩
    exact hterminal next hlt

/-- Direct successor extraction from confinement's no-permanent-holonomy law. -/
theorem successor_of_noPermanentPhysicalHolonomy
    (H : SU7PhysicalConfinementForbidsPermanentHolonomy)
    {n : ℕ} (hn : 2 ≤ n) (cell : SU7PhysicalBranchCell n)
    (hnonzero : physicalResidual cell ≠ 0) :
    ∃ next : SU7PhysicalBranchCell n,
      physicalResidualEnergy next < physicalResidualEnergy cell :=
  (noPermanentPhysicalHolonomy_iff_successorLaw.mp H) n hn cell hnonzero

/-! ## Confinement as holonomy elimination -/

/-- Physical confinement data below prime coding and below zero-cell storage.

The only fiberwise producer content is:

* a starting physical branch cell;
* no permanent physical holonomy.

The zero residual cell is generated later by P875's well-founded descent. -/
structure SU7PhysicalHolonomyEliminationConfinement where
  compact_gauge_orbit : SU7CompactGaugeOrbit
  lyapunov_residual_dissipation : SU7LyapunovResidualDissipation
  quantized_spectrum_no_escaping_boundary :
    SU7QuantizedSpectrumNoEscapingBoundary
  startCell :
    ∀ n : ℕ, 2 ≤ n -> SU7PhysicalBranchCell n
  no_permanent_holonomy :
    SU7PhysicalConfinementForbidsPermanentHolonomy

/-- THEOREM 2: physical holonomy elimination generates the well-founded orbit
required by P875 on one even fiber. -/
def wellFoundedOrbit_of_physicalHolonomyElimination
    (D : SU7PhysicalHolonomyEliminationConfinement)
    (n : ℕ) (hn : 2 ≤ n) :
    SU7WellFoundedPhysicalOrbit n where
  startCell := D.startCell n hn
  lyapunov_descends_nonzero := by
    intro cell hnonzero
    exact successor_of_noPermanentPhysicalHolonomy
      D.no_permanent_holonomy hn cell hnonzero

/-- THEOREM 3: physical holonomy elimination produces P875's well-founded
confinement dynamics. -/
def wellFoundedConfinementDynamics_of_physicalHolonomyElimination
    (D : SU7PhysicalHolonomyEliminationConfinement) :
    SU7WellFoundedConfinementDynamics where
  compact_gauge_orbit := D.compact_gauge_orbit
  lyapunov_residual_dissipation := D.lyapunov_residual_dissipation
  quantized_spectrum_no_escaping_boundary :=
    D.quantized_spectrum_no_escaping_boundary
  orbit := wellFoundedOrbit_of_physicalHolonomyElimination D

/-- THEOREM 4: physical holonomy elimination reaches a zero physical cell on
every even fiber, by well-founded residual descent. -/
theorem physicalZeroCellEveryEvenFiber_of_physicalHolonomyElimination
    (D : SU7PhysicalHolonomyEliminationConfinement) :
    ∀ n : ℕ, 2 ≤ n ->
      ∃ cell : SU7PhysicalBranchCell n, physicalResidual cell = 0 :=
  physicalZeroCellEveryEvenFiber_of_wellFoundedLyapunov
    (wellFoundedConfinementDynamics_of_physicalHolonomyElimination D)

/-! ## Downstream no-gap and unit bracket after faithful atom-code projection -/

/-- THEOREM 5: physical holonomy elimination plus atom-code prime projection
gives prime-edge trace no-gap. -/
theorem traceSpectrumNoGap_of_physicalHolonomyElimination
    (D : SU7PhysicalHolonomyEliminationConfinement)
    (P : SU7AtomCodePrimeProjectionLaw) :
    PrimeEdgeTraceSpectrumNoGap :=
  traceSpectrumNoGap_of_wellFoundedLyapunov
    (wellFoundedConfinementDynamics_of_physicalHolonomyElimination D) P

/-- THEOREM 6: physical holonomy elimination plus atom-code prime projection
gives the color-loop unit bracket. -/
theorem unitBracketProducer_of_physicalHolonomyElimination
    (D : SU7PhysicalHolonomyEliminationConfinement)
    (P : SU7AtomCodePrimeProjectionLaw) :
    ColorLoopTraceUnitBracketProducer :=
  unitBracketProducer_of_wellFoundedLyapunov
    (wellFoundedConfinementDynamics_of_physicalHolonomyElimination D) P

/-- THEOREM 7: physical holonomy elimination plus atom-code prime projection
gives ordinary even Goldbach. -/
theorem evenGoldbach_of_physicalHolonomyElimination
    (D : SU7PhysicalHolonomyEliminationConfinement)
    (P : SU7AtomCodePrimeProjectionLaw) :
    AffineRelaxation.EvenGoldbachStatement :=
  evenGoldbach_of_wellFoundedLyapunov
    (wellFoundedConfinementDynamics_of_physicalHolonomyElimination D) P

/-! ## Certificate -/

/-- P876 certificate: permanent physical holonomy elimination is the exact
producer of P875's strict Lyapunov successor law. -/
structure SU7PhysicalHolonomyEliminationProducerCertificate where
  no_permanent_iff_successor :
    SU7PhysicalConfinementForbidsPermanentHolonomy ↔
      ∀ n : ℕ, 2 ≤ n ->
        ∀ cell : SU7PhysicalBranchCell n,
          physicalResidual cell ≠ 0 ->
            ∃ next : SU7PhysicalBranchCell n,
              physicalResidualEnergy next < physicalResidualEnergy cell
  to_well_founded :
    SU7PhysicalHolonomyEliminationConfinement ->
      SU7WellFoundedConfinementDynamics
  to_zero_fibers :
    SU7PhysicalHolonomyEliminationConfinement ->
      ∀ n : ℕ, 2 ≤ n ->
        ∃ cell : SU7PhysicalBranchCell n, physicalResidual cell = 0
  to_no_gap :
    SU7PhysicalHolonomyEliminationConfinement ->
      SU7AtomCodePrimeProjectionLaw ->
        PrimeEdgeTraceSpectrumNoGap
  to_unit_bracket :
    SU7PhysicalHolonomyEliminationConfinement ->
      SU7AtomCodePrimeProjectionLaw ->
        ColorLoopTraceUnitBracketProducer
  to_goldbach :
    SU7PhysicalHolonomyEliminationConfinement ->
      SU7AtomCodePrimeProjectionLaw ->
        AffineRelaxation.EvenGoldbachStatement

def su7PhysicalHolonomyEliminationProducerCertificate :
    SU7PhysicalHolonomyEliminationProducerCertificate where
  no_permanent_iff_successor :=
    noPermanentPhysicalHolonomy_iff_successorLaw
  to_well_founded :=
    wellFoundedConfinementDynamics_of_physicalHolonomyElimination
  to_zero_fibers :=
    physicalZeroCellEveryEvenFiber_of_physicalHolonomyElimination
  to_no_gap :=
    traceSpectrumNoGap_of_physicalHolonomyElimination
  to_unit_bracket :=
    unitBracketProducer_of_physicalHolonomyElimination
  to_goldbach :=
    evenGoldbach_of_physicalHolonomyElimination


end
end StandardModelConstraint
end SaturationMonoid
