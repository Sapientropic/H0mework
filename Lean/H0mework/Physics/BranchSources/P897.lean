import H0mework.Physics.BranchSources.P896

/-!
# Proposition 897: residual dynamics forbids branching-decomposition holonomy

P896 lowers the color-loop producer to finite SU(7) branching-decomposition
spectra.  Its remaining input is a static statement that the spectrum forbids
permanent decomposition holonomy.

This file replaces that static input by explicit residual-transport dynamics
on the same decomposition cells:

* a finite branching-decomposition spectrum;
* a start cell in that spectrum;
* a generated successor relation;
* successor steps stay in the same spectrum and strictly lower residual energy;
* every nonzero residual cell has a successor.

Strong induction on the natural residual energy then produces a zero residual
cell and proves the P896 no-permanent-holonomy rule.  The gap is now exactly
what the truth-formula route says it is: a nonzero residual split with no
lower-energy transport.  Confinement is represented by the fact that the
residual dynamics never leaves such a permanent color holonomy behind.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation

set_option linter.defProp false

/-! ## Residual transport dynamics on branching decompositions -/

/-- Residual-transport dynamics on one finite SU(7) branching-decomposition
spectrum.

The object contains no zero cell, no prime edge, and no Goldbach pair.  It says
only that a nonzero residual cell admits a same-spectrum successor of strictly
lower residual energy. -/
structure SU7BranchingDecompositionResidualDynamics (n : ℕ) where
  spectrum : SU7BranchingDecompositionSpectrum n
  startCell : SU7BranchingDecompositionCell n
  start_mem : startCell ∈ spectrum.cells
  step :
    SU7BranchingDecompositionCell n ->
      SU7BranchingDecompositionCell n -> Prop
  step_mem_preserves :
    ∀ C next : SU7BranchingDecompositionCell n,
      C ∈ spectrum.cells ->
        step C next ->
          next ∈ spectrum.cells
  step_strictly_decreases_energy :
    ∀ C next : SU7BranchingDecompositionCell n,
      C ∈ spectrum.cells ->
        step C next ->
          branchingDecompositionResidualEnergy next <
            branchingDecompositionResidualEnergy C
  no_terminal_nonzero :
    ∀ C : SU7BranchingDecompositionCell n,
      C ∈ spectrum.cells ->
        branchingDecompositionResidual C ≠ 0 ->
          ∃ next : SU7BranchingDecompositionCell n, step C next

/-- THEOREM 1: a residual-dynamics step preserves membership in the generated
branching spectrum. -/
theorem branchingResidualStep_mem_preserves
    {n : ℕ} (D : SU7BranchingDecompositionResidualDynamics n)
    (C next : SU7BranchingDecompositionCell n)
    (hmem : C ∈ D.spectrum.cells)
    (hstep : D.step C next) :
    next ∈ D.spectrum.cells :=
  D.step_mem_preserves C next hmem hstep

/-- THEOREM 2: a residual-dynamics step strictly lowers decomposition
residual energy. -/
theorem branchingResidualStep_strictly_decreases_energy
    {n : ℕ} (D : SU7BranchingDecompositionResidualDynamics n)
    (C next : SU7BranchingDecompositionCell n)
    (hmem : C ∈ D.spectrum.cells)
    (hstep : D.step C next) :
    branchingDecompositionResidualEnergy next <
      branchingDecompositionResidualEnergy C :=
  D.step_strictly_decreases_energy C next hmem hstep

/-- THEOREM 3: residual dynamics generates a zero decomposition-residual cell
inside the finite branching spectrum. -/
theorem exists_zeroCell_of_branchingResidualDynamics
    {n : ℕ} (D : SU7BranchingDecompositionResidualDynamics n) :
    ∃ Z : SU7BranchingDecompositionCell n,
      Z ∈ D.spectrum.cells ∧
        branchingDecompositionResidual Z = 0 := by
  let motive : ℕ -> Prop := fun e =>
    ∀ C : SU7BranchingDecompositionCell n,
      C ∈ D.spectrum.cells ->
        branchingDecompositionResidualEnergy C = e ->
          ∃ Z : SU7BranchingDecompositionCell n,
            Z ∈ D.spectrum.cells ∧
              branchingDecompositionResidual Z = 0
  have hstep : ∀ e : ℕ, (∀ e' < e, motive e') -> motive e := by
    intro e ih C hmem henergy
    by_cases hzero : branchingDecompositionResidual C = 0
    · exact ⟨C, hmem, hzero⟩
    · rcases D.no_terminal_nonzero C hmem hzero with ⟨next, hnext_step⟩
      have hnext_mem : next ∈ D.spectrum.cells :=
        D.step_mem_preserves C next hmem hnext_step
      have hnext_lt :
          branchingDecompositionResidualEnergy next <
            branchingDecompositionResidualEnergy C :=
        D.step_strictly_decreases_energy C next hmem hnext_step
      exact ih (branchingDecompositionResidualEnergy next)
        (by simpa [henergy] using hnext_lt)
        next hnext_mem rfl
  have hstart :
      motive
        (branchingDecompositionResidualEnergy D.startCell) :=
    Nat.strong_induction_on
      (branchingDecompositionResidualEnergy D.startCell) hstep
  exact hstart D.startCell D.start_mem rfl

/-- THEOREM 4: residual dynamics forbids permanent branching-decomposition
holonomy. -/
theorem branchingResidualDynamics_forbidsPermanentHolonomy
    {n : ℕ} (D : SU7BranchingDecompositionResidualDynamics n) :
    SU7BranchingDecompositionSpectrumForbidsPermanentHolonomy
      D.spectrum := by
  intro C hperm
  rcases hperm with ⟨hmem, hnonzero, hterminal⟩
  rcases D.no_terminal_nonzero C hmem hnonzero with ⟨next, hstep⟩
  have hnext_mem : next ∈ D.spectrum.cells :=
    D.step_mem_preserves C next hmem hstep
  have hnext_lt :
      branchingDecompositionResidualEnergy next <
        branchingDecompositionResidualEnergy C :=
    D.step_strictly_decreases_energy C next hmem hstep
  exact hterminal next hnext_mem hnext_lt

/-- THEOREM 5: residual dynamics generates P896's holonomy-confinement rule. -/
def branchingDecompositionRule_of_residualDynamics
    {n : ℕ} (D : SU7BranchingDecompositionResidualDynamics n) :
    SU7BranchingDecompositionHolonomyConfinementRule n where
  spectrum := D.spectrum
  startCell := D.startCell
  start_mem := D.start_mem
  forbids_permanent_decomposition_holonomy :=
    branchingResidualDynamics_forbidsPermanentHolonomy D

/-- THEOREM 6: residual dynamics computes a trace-zero prime-edge loop via
the P897 -> P896 -> P895 -> P894 -> P893 -> P884 -> P892 spine. -/
def traceZeroPrimeEdgeLoop_of_branchingResidualDynamics
    {n : ℕ} (D : SU7BranchingDecompositionResidualDynamics n) :
    TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoop_of_branchingDecompositionRule
    (branchingDecompositionRule_of_residualDynamics D)

/-! ## Fiberwise residual transport confinement -/

/-- Every even fiber carries residual dynamics on a branching-decomposition
spectrum. -/
def SU7BranchingDecompositionResidualDynamicsEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    Nonempty (SU7BranchingDecompositionResidualDynamics n)

/-- THEOREM 7: fiberwise residual dynamics generates P896 holonomy rules on
every even fiber. -/
theorem branchingRulesEveryEvenFiber_of_residualDynamics
    (H : SU7BranchingDecompositionResidualDynamicsEveryEvenFiber) :
    SU7BranchingDecompositionHolonomyConfinementRuleEveryEvenFiber := by
  intro n hn
  let D : SU7BranchingDecompositionResidualDynamics n :=
    Classical.choice (H n hn)
  exact ⟨branchingDecompositionRule_of_residualDynamics D⟩

/-- Physical residual-transport confinement data at the branching-decomposition
level.  The law names are the physical side; the mathematical content is the
fiberwise residual dynamics. -/
structure SU7BranchingResidualTransportConfinement where
  compact_gauge_orbit : SU7CompactGaugeOrbit
  lyapunov_residual_dissipation : SU7LyapunovResidualDissipation
  quantized_spectrum_no_escaping_boundary :
    SU7QuantizedSpectrumNoEscapingBoundary
  incidence_schedule_no_free :
    RunningSigmaBeta.SU7IncidenceScheduleNoFreeCertificate
  residual_dynamics :
    SU7BranchingDecompositionResidualDynamicsEveryEvenFiber

/-- THEOREM 8: residual-transport confinement generates P896 physical
branching-decomposition confinement. -/
def branchingDecompositionConfinement_of_residualTransportConfinement
    (D : SU7BranchingResidualTransportConfinement) :
    SU7PhysicalBranchingDecompositionConfinement where
  compact_gauge_orbit := D.compact_gauge_orbit
  lyapunov_residual_dissipation := D.lyapunov_residual_dissipation
  quantized_spectrum_no_escaping_boundary :=
    D.quantized_spectrum_no_escaping_boundary
  incidence_schedule_no_free := D.incidence_schedule_no_free
  branching_decomposition_rules :=
    branchingRulesEveryEvenFiber_of_residualDynamics D.residual_dynamics

/-- THEOREM 9: residual-transport confinement computes trace-zero prime-edge
loops on every even fiber. -/
def traceZeroPrimeEdgeLoopEveryEvenFiber_of_residualTransportConfinement
    (D : SU7BranchingResidualTransportConfinement) :
    ∀ n : ℕ, 2 ≤ n -> TraceZeroPrimeEdgeLoop n :=
  traceZeroPrimeEdgeLoopEveryEvenFiber_of_branchingDecompositionConfinement
    (branchingDecompositionConfinement_of_residualTransportConfinement D)

/-- THEOREM 10: residual-transport confinement gives ordinary even Goldbach
through the non-storing branch-decomposition projection chain. -/
theorem evenGoldbach_of_branchingResidualTransportConfinement
    (D : SU7BranchingResidualTransportConfinement) :
    EvenGoldbachStatement :=
  evenGoldbach_of_physicalBranchingDecompositionConfinement
    (branchingDecompositionConfinement_of_residualTransportConfinement D)

/-! ## Certificate -/

/-- P897 certificate, with explicit projections. -/
structure SU7BranchingResidualTransportProducerCertificate where
  dynamics_to_zero_cell :
    ∀ {n : ℕ} (D : SU7BranchingDecompositionResidualDynamics n),
      ∃ Z : SU7BranchingDecompositionCell n,
        Z ∈ D.spectrum.cells ∧
          branchingDecompositionResidual Z = 0
  dynamics_forbids_permanent_holonomy :
    ∀ {n : ℕ} (D : SU7BranchingDecompositionResidualDynamics n),
      SU7BranchingDecompositionSpectrumForbidsPermanentHolonomy D.spectrum
  dynamics_to_branching_rule :
    ∀ {n : ℕ}, SU7BranchingDecompositionResidualDynamics n ->
      SU7BranchingDecompositionHolonomyConfinementRule n
  dynamics_to_trace_zero :
    ∀ {n : ℕ}, SU7BranchingDecompositionResidualDynamics n ->
      TraceZeroPrimeEdgeLoop n
  residual_transport_to_branching_confinement :
    SU7BranchingResidualTransportConfinement ->
      SU7PhysicalBranchingDecompositionConfinement
  residual_transport_to_goldbach :
    SU7BranchingResidualTransportConfinement -> EvenGoldbachStatement

def su7BranchingResidualTransportProducerCertificate :
    SU7BranchingResidualTransportProducerCertificate where
  dynamics_to_zero_cell :=
    exists_zeroCell_of_branchingResidualDynamics
  dynamics_forbids_permanent_holonomy :=
    branchingResidualDynamics_forbidsPermanentHolonomy
  dynamics_to_branching_rule :=
    branchingDecompositionRule_of_residualDynamics
  dynamics_to_trace_zero :=
    traceZeroPrimeEdgeLoop_of_branchingResidualDynamics
  residual_transport_to_branching_confinement :=
    branchingDecompositionConfinement_of_residualTransportConfinement
  residual_transport_to_goldbach :=
    evenGoldbach_of_branchingResidualTransportConfinement


end
end StandardModelConstraint
end SaturationMonoid
