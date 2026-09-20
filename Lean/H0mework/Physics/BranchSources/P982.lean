import H0mework.Physics.BranchSources.P981

/-!
# Proposition 982: terminal gauge spectrum generators produce finite orbits

P981 still accepted a finite terminal gauge orbit in every fiber.  This file
pushes one level lower: a single SU(7) terminal gauge-spectrum generator
provides the branch-cell list, ground cell, terminal holonomy law, and
confinement law uniformly in the fiber.  From that uniform spectrum object Lean
constructs the P981 finite-orbit family and therefore zero terminal physical
residual on every even fiber.

The file remains on the terminal physical layer; arithmetic readouts are not
part of this producer.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

set_option linter.defProp false

/-! ## Uniform terminal gauge-spectrum generator -/

/-- A uniform terminal gauge-spectrum generator.

This is the global physical producer object below P981: the finite cell list
and its certified ground cell are generated uniformly for every fiber. -/
structure SU7TerminalGaugeSpectrumGenerator where
  branchCells : ∀ n : ℕ, List (SU7TerminalPhysicalBranchCell n)
  groundCell : ∀ n : ℕ, SU7TerminalPhysicalBranchCell n
  ground_mem :
    ∀ n : ℕ, groundCell n ∈ branchCells n
  ground_residual_le :
    ∀ n : ℕ,
      ∀ cell : SU7TerminalPhysicalBranchCell n,
        cell ∈ branchCells n ->
          terminalPhysicalResidual (groundCell n) ≤
            terminalPhysicalResidual cell
  terminal_nonzero_to_holonomy :
    ∀ n : ℕ,
      ∀ cell : SU7TerminalPhysicalBranchCell n,
        TerminalEnergyPoint {x | x ∈ branchCells n}
          terminalPhysicalResidual cell ->
          terminalPhysicalResidual cell ≠ 0 ->
            terminalPhysicalPermanentColorHolonomy cell
  confinement_excludes_holonomy :
    ∀ n : ℕ,
      ∀ cell : SU7TerminalPhysicalBranchCell n,
        ¬ terminalPhysicalPermanentColorHolonomy cell

/-! ## Spectrum generator to finite terminal orbit -/

/-- The uniform spectrum generator constructs the finite terminal gauge orbit
in one fiber. -/
def terminalFiniteGaugeOrbit_of_spectrumGenerator
    (G : SU7TerminalGaugeSpectrumGenerator) (n : ℕ) :
    SU7TerminalFiniteGaugeOrbit n where
  cells := G.branchCells n
  minimalCell := G.groundCell n
  minimal_mem := G.ground_mem n
  minimal_residual_le := G.ground_residual_le n
  terminal_nonzero_to_holonomy := G.terminal_nonzero_to_holonomy n
  confinement_excludes_holonomy := G.confinement_excludes_holonomy n

/-- In the generated finite orbit, the ground cell is terminal. -/
theorem spectrumGenerator_groundCell_terminal
    (G : SU7TerminalGaugeSpectrumGenerator) (n : ℕ) :
    TerminalEnergyPoint
      (terminalFiniteGaugeOrbitSet
        (terminalFiniteGaugeOrbit_of_spectrumGenerator G n))
      terminalPhysicalResidual
      (G.groundCell n) :=
  terminalFiniteGaugeOrbit_minimalCell_terminal
    (terminalFiniteGaugeOrbit_of_spectrumGenerator G n)

/-- The uniform spectrum generator supplies P981's every-fiber finite-orbit
producer. -/
theorem finiteGaugeOrbitsEveryEven_of_spectrumGenerator
    (G : SU7TerminalGaugeSpectrumGenerator) :
    SU7TerminalFiniteGaugeOrbitEveryEvenFiber := by
  intro n _hn
  exact ⟨terminalFiniteGaugeOrbit_of_spectrumGenerator G n⟩

/-- The uniform spectrum generator supplies P980 terminal confinement on every
even fiber. -/
theorem terminalConfinementEveryEven_of_spectrumGenerator
    (G : SU7TerminalGaugeSpectrumGenerator) :
    ∀ n : ℕ, 2 ≤ n -> Nonempty (SU7ColorOrbitTerminalConfinement n) :=
  terminalConfinementEveryEven_of_finiteGaugeOrbits
    (finiteGaugeOrbitsEveryEven_of_spectrumGenerator G)

/-- The uniform spectrum generator produces zero terminal physical residual on
every even fiber. -/
theorem zeroResidualEveryEven_of_spectrumGenerator
    (G : SU7TerminalGaugeSpectrumGenerator) :
    ∀ n : ℕ, 2 ≤ n ->
      ∃ cell : SU7TerminalPhysicalBranchCell n,
        terminalPhysicalResidual cell = 0 :=
  zeroResidualEveryEven_of_finiteGaugeOrbits
    (finiteGaugeOrbitsEveryEven_of_spectrumGenerator G)

/-! ## Certificate -/

/-- P982 certificate: a uniform terminal gauge-spectrum generator produces the
finite terminal orbit family consumed by P981. -/
structure TerminalGaugeSpectrumGeneratorProducerCertificate where
  spectrum_to_finite_orbit :
    SU7TerminalGaugeSpectrumGenerator ->
      ∀ n : ℕ, SU7TerminalFiniteGaugeOrbit n
  generated_ground_terminal :
    ∀ (G : SU7TerminalGaugeSpectrumGenerator) (n : ℕ),
      TerminalEnergyPoint
        (terminalFiniteGaugeOrbitSet
          (terminalFiniteGaugeOrbit_of_spectrumGenerator G n))
        terminalPhysicalResidual
        (G.groundCell n)
  spectrum_to_every_fiber_finite_orbit :
    SU7TerminalGaugeSpectrumGenerator ->
      SU7TerminalFiniteGaugeOrbitEveryEvenFiber
  spectrum_to_terminal_confinement_every_fiber :
    SU7TerminalGaugeSpectrumGenerator ->
      ∀ n : ℕ, 2 ≤ n -> Nonempty (SU7ColorOrbitTerminalConfinement n)
  spectrum_to_zero_residual_every_fiber :
    SU7TerminalGaugeSpectrumGenerator ->
      ∀ n : ℕ, 2 ≤ n ->
        ∃ cell : SU7TerminalPhysicalBranchCell n,
          terminalPhysicalResidual cell = 0

/-- Canonical P982 terminal-spectrum generator certificate. -/
def terminalGaugeSpectrumGeneratorProducerCertificate :
    TerminalGaugeSpectrumGeneratorProducerCertificate where
  spectrum_to_finite_orbit :=
    terminalFiniteGaugeOrbit_of_spectrumGenerator
  generated_ground_terminal :=
    spectrumGenerator_groundCell_terminal
  spectrum_to_every_fiber_finite_orbit :=
    finiteGaugeOrbitsEveryEven_of_spectrumGenerator
  spectrum_to_terminal_confinement_every_fiber :=
    terminalConfinementEveryEven_of_spectrumGenerator
  spectrum_to_zero_residual_every_fiber :=
    zeroResidualEveryEven_of_spectrumGenerator


end
end StandardModelConstraint
end SaturationMonoid
