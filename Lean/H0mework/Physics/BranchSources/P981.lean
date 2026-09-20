import H0mework.Physics.BranchSources.P980

/-!
# Proposition 981: finite gauge orbits generate terminal confinement

P980 proved the pure terminal-confinement theorem.  This file lowers the SU(7)
input one step: a finite/quantized gauge orbit, together with the terminal
nonzero-holonomy law and confinement exclusion, generates the
`SU7ColorOrbitTerminalConfinement` certificate consumed by P980.

The file stays entirely on the terminal physical layer.  The cell type is the
P980 terminal physical cell, and later arithmetic readouts remain outside this
producer.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

set_option linter.defProp false

/-! ## Finite terminal gauge orbits -/

/-- A finite SU(7) terminal gauge orbit over one fiber.

The `minimalCell` fields are the quantized compactness certificate: the finite
orbit has a cell whose terminal physical residual is minimal.  The last two
fields are purely physical: nonzero terminal minima carry permanent color
holonomy, while confinement excludes permanent color holonomy. -/
structure SU7TerminalFiniteGaugeOrbit (n : ℕ) where
  cells : List (SU7TerminalPhysicalBranchCell n)
  minimalCell : SU7TerminalPhysicalBranchCell n
  minimal_mem : minimalCell ∈ cells
  minimal_residual_le :
    ∀ cell : SU7TerminalPhysicalBranchCell n,
      cell ∈ cells ->
        terminalPhysicalResidual minimalCell ≤ terminalPhysicalResidual cell
  terminal_nonzero_to_holonomy :
    ∀ cell : SU7TerminalPhysicalBranchCell n,
      TerminalEnergyPoint {x | x ∈ cells} terminalPhysicalResidual cell ->
        terminalPhysicalResidual cell ≠ 0 ->
          terminalPhysicalPermanentColorHolonomy cell
  confinement_excludes_holonomy :
    ∀ cell : SU7TerminalPhysicalBranchCell n,
      ¬ terminalPhysicalPermanentColorHolonomy cell

/-- The set-orbit associated to a finite terminal gauge orbit. -/
def terminalFiniteGaugeOrbitSet {n : ℕ}
    (O : SU7TerminalFiniteGaugeOrbit n) :
    Set (SU7TerminalPhysicalBranchCell n) :=
  {cell | cell ∈ O.cells}

/-- The finite terminal gauge orbit is nonempty. -/
theorem terminalFiniteGaugeOrbitSet_nonempty
    {n : ℕ} (O : SU7TerminalFiniteGaugeOrbit n) :
    (terminalFiniteGaugeOrbitSet O).Nonempty :=
  ⟨O.minimalCell, O.minimal_mem⟩

/-- The certified minimum cell is terminal in the associated set-orbit. -/
theorem terminalFiniteGaugeOrbit_minimalCell_terminal
    {n : ℕ} (O : SU7TerminalFiniteGaugeOrbit n) :
    TerminalEnergyPoint
      (terminalFiniteGaugeOrbitSet O)
      terminalPhysicalResidual
      O.minimalCell := by
  constructor
  · exact O.minimal_mem
  · intro cell hmem
    exact O.minimal_residual_le cell hmem

/-- A finite terminal gauge orbit provides the quantized-minimum input for
P980. -/
theorem quantizedMinimum_of_terminalFiniteGaugeOrbit
    {n : ℕ} (O : SU7TerminalFiniteGaugeOrbit n) :
    QuantizedMinimum
      (terminalFiniteGaugeOrbitSet O)
      terminalPhysicalResidual := by
  intro _hnonempty
  exact ⟨O.minimalCell, terminalFiniteGaugeOrbit_minimalCell_terminal O⟩

/-! ## Finite orbit to P980 terminal confinement -/

/-- A finite terminal gauge orbit generates the P980 SU(7) terminal
confinement certificate. -/
def colorOrbitTerminalConfinement_of_terminalFiniteGaugeOrbit
    {n : ℕ} (O : SU7TerminalFiniteGaugeOrbit n) :
    SU7ColorOrbitTerminalConfinement n where
  orbit := terminalFiniteGaugeOrbitSet O
  orbit_nonempty := terminalFiniteGaugeOrbitSet_nonempty O
  quantized_minimum := quantizedMinimum_of_terminalFiniteGaugeOrbit O
  terminal_nonzero_to_holonomy := O.terminal_nonzero_to_holonomy
  confinement_excludes_holonomy := O.confinement_excludes_holonomy

/-- A finite terminal gauge orbit produces a zero-residual terminal physical
branch cell in its orbit. -/
theorem terminalFiniteGaugeOrbit_zeroResidual_mem
    {n : ℕ} (O : SU7TerminalFiniteGaugeOrbit n) :
    ∃ cell : SU7TerminalPhysicalBranchCell n,
      cell ∈ terminalFiniteGaugeOrbitSet O ∧
        terminalPhysicalResidual cell = 0 :=
  su7ColorOrbitTerminalConfinement_zeroResidual_mem
    (colorOrbitTerminalConfinement_of_terminalFiniteGaugeOrbit O)

/-- A finite terminal gauge orbit produces a zero-residual terminal physical
branch cell. -/
theorem terminalFiniteGaugeOrbit_zeroResidual
    {n : ℕ} (O : SU7TerminalFiniteGaugeOrbit n) :
    ∃ cell : SU7TerminalPhysicalBranchCell n,
      terminalPhysicalResidual cell = 0 :=
  su7ColorOrbitTerminalConfinement_zeroResidual
    (colorOrbitTerminalConfinement_of_terminalFiniteGaugeOrbit O)

/-! ## Every-fiber producer form -/

/-- Every fiber has a finite terminal gauge orbit. -/
def SU7TerminalFiniteGaugeOrbitEveryEvenFiber : Prop :=
  ∀ n : ℕ, 2 ≤ n -> Nonempty (SU7TerminalFiniteGaugeOrbit n)

/-- Fiberwise finite terminal gauge orbits generate P980 terminal confinement
on every even fiber. -/
theorem terminalConfinementEveryEven_of_finiteGaugeOrbits
    (H : SU7TerminalFiniteGaugeOrbitEveryEvenFiber) :
    ∀ n : ℕ, 2 ≤ n -> Nonempty (SU7ColorOrbitTerminalConfinement n) := by
  intro n hn
  let O := Classical.choice (H n hn)
  exact ⟨colorOrbitTerminalConfinement_of_terminalFiniteGaugeOrbit O⟩

/-- Fiberwise finite terminal gauge orbits produce zero-residual terminal
physical branch cells on every even fiber. -/
theorem zeroResidualEveryEven_of_finiteGaugeOrbits
    (H : SU7TerminalFiniteGaugeOrbitEveryEvenFiber) :
    ∀ n : ℕ, 2 ≤ n ->
      ∃ cell : SU7TerminalPhysicalBranchCell n,
        terminalPhysicalResidual cell = 0 := by
  intro n hn
  let O := Classical.choice (H n hn)
  exact terminalFiniteGaugeOrbit_zeroResidual O

/-! ## Certificate -/

/-- P981 certificate: finite/quantized physical gauge orbits are enough to
generate P980 terminal confinement and zero residual. -/
structure TerminalFiniteGaugeOrbitProducerCertificate where
  orbit_nonempty :
    ∀ {n : ℕ} (O : SU7TerminalFiniteGaugeOrbit n),
      (terminalFiniteGaugeOrbitSet O).Nonempty
  minimum_terminal :
    ∀ {n : ℕ} (O : SU7TerminalFiniteGaugeOrbit n),
      TerminalEnergyPoint
        (terminalFiniteGaugeOrbitSet O)
        terminalPhysicalResidual
        O.minimalCell
  quantized_minimum :
    ∀ {n : ℕ} (O : SU7TerminalFiniteGaugeOrbit n),
      QuantizedMinimum
        (terminalFiniteGaugeOrbitSet O)
        terminalPhysicalResidual
  finite_orbit_to_terminal_confinement :
    ∀ {n : ℕ}, SU7TerminalFiniteGaugeOrbit n ->
      SU7ColorOrbitTerminalConfinement n
  finite_orbit_to_zero_residual_mem :
    ∀ {n : ℕ} (O : SU7TerminalFiniteGaugeOrbit n),
      ∃ cell : SU7TerminalPhysicalBranchCell n,
        cell ∈ terminalFiniteGaugeOrbitSet O ∧
          terminalPhysicalResidual cell = 0
  finite_orbit_to_zero_residual :
    ∀ {n : ℕ}, SU7TerminalFiniteGaugeOrbit n ->
      ∃ cell : SU7TerminalPhysicalBranchCell n,
        terminalPhysicalResidual cell = 0
  every_fiber_to_terminal_confinement :
    SU7TerminalFiniteGaugeOrbitEveryEvenFiber ->
      ∀ n : ℕ, 2 ≤ n -> Nonempty (SU7ColorOrbitTerminalConfinement n)
  every_fiber_to_zero_residual :
    SU7TerminalFiniteGaugeOrbitEveryEvenFiber ->
      ∀ n : ℕ, 2 ≤ n ->
        ∃ cell : SU7TerminalPhysicalBranchCell n,
          terminalPhysicalResidual cell = 0

/-- Canonical P981 finite-gauge-orbit producer certificate. -/
def terminalFiniteGaugeOrbitProducerCertificate :
    TerminalFiniteGaugeOrbitProducerCertificate where
  orbit_nonempty := terminalFiniteGaugeOrbitSet_nonempty
  minimum_terminal := terminalFiniteGaugeOrbit_minimalCell_terminal
  quantized_minimum := quantizedMinimum_of_terminalFiniteGaugeOrbit
  finite_orbit_to_terminal_confinement :=
    colorOrbitTerminalConfinement_of_terminalFiniteGaugeOrbit
  finite_orbit_to_zero_residual_mem :=
    terminalFiniteGaugeOrbit_zeroResidual_mem
  finite_orbit_to_zero_residual :=
    terminalFiniteGaugeOrbit_zeroResidual
  every_fiber_to_terminal_confinement :=
    terminalConfinementEveryEven_of_finiteGaugeOrbits
  every_fiber_to_zero_residual :=
    zeroResidualEveryEven_of_finiteGaugeOrbits


end
end StandardModelConstraint
end SaturationMonoid
