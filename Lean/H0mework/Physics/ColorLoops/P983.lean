import H0mework.Physics.BranchSources.P982

/-!
# Proposition 983: scoped confinement from generated color-loop readout

P982 exposed a useful pressure point: a concrete spectrum should only need to
exclude permanent holonomy on its generated orbit, not on every possible
terminal physical cell.  This file adds the orbit-scoped terminal confinement
theorem and then builds a concrete generated color-loop spectrum whose
residual is computed from the color-loop readout rather than stored as a free
field.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

set_option linter.defProp false

/-! ## Orbit-scoped terminal confinement -/

/-- Orbit-scoped terminal confinement.

This is the same argument as P980, but the confinement law only has to hold on
the generated orbit. -/
theorem terminalConfinement_zeroResidual_onOrbit
    {X : Type*} {orbit : Set X} {E : X -> ℕ}
    {PermanentColorHolonomy : X -> Prop}
    (hnonempty : orbit.Nonempty)
    (hminimum : QuantizedMinimum orbit E)
    (hterminal :
      ∀ x : X,
        TerminalEnergyPoint orbit E x ->
          E x ≠ 0 ->
            PermanentColorHolonomy x)
    (hconfinement :
      ∀ x : X, x ∈ orbit -> ¬ PermanentColorHolonomy x) :
    ∃ x : X, x ∈ orbit ∧ E x = 0 := by
  rcases hminimum hnonempty with ⟨x, hxterminal⟩
  by_cases hzero : E x = 0
  · exact ⟨x, hxterminal.1, hzero⟩
  · exact False.elim
      ((hconfinement x hxterminal.1) (hterminal x hxterminal hzero))

/-! ## Generated terminal color-loop cells -/

/-- A generated terminal color cell below P980's physical cell.

It does not store a residual or holonomy proposition.  Both are computed from
the color-loop coordinates. -/
structure SU7GeneratedTerminalColorCell (n : ℕ) where
  leftWeight : Fin 7 -> ℤ
  rightWeight : Fin 7 -> ℤ
  colorLoop : Fin 3 -> ℤ
  gaugeAllowed : Prop
  colorSinglet : Prop
  nonSingletExcluded : Prop

/-- Residual readout of a generated terminal color cell: total absolute color
loop charge. -/
def generatedTerminalColorResidual {n : ℕ}
    (cell : SU7GeneratedTerminalColorCell n) : ℕ :=
  Int.natAbs (cell.colorLoop (0 : Fin 3)) +
    Int.natAbs (cell.colorLoop (1 : Fin 3)) +
      Int.natAbs (cell.colorLoop (2 : Fin 3))

/-- Permanent holonomy is precisely nonzero generated color-loop residual. -/
def generatedTerminalColorPermanentHolonomy {n : ℕ}
    (cell : SU7GeneratedTerminalColorCell n) : Prop :=
  generatedTerminalColorResidual cell ≠ 0

/-- Exact generated color loop: all three color coordinates vanish. -/
def GeneratedTerminalColorLoopExact {n : ℕ}
    (cell : SU7GeneratedTerminalColorCell n) : Prop :=
  ∀ i : Fin 3, cell.colorLoop i = 0

/-- Exact generated color loops have zero residual. -/
theorem generatedTerminalColorResidual_eq_zero_of_exact
    {n : ℕ} (cell : SU7GeneratedTerminalColorCell n)
    (hexact : GeneratedTerminalColorLoopExact cell) :
    generatedTerminalColorResidual cell = 0 := by
  unfold generatedTerminalColorResidual
  simp [hexact (0 : Fin 3), hexact (1 : Fin 3), hexact (2 : Fin 3)]

/-- Project a generated terminal color cell to P980's terminal physical cell.
The residual and holonomy fields are computed readouts. -/
def terminalPhysicalCellOfGeneratedColorCell
    {n : ℕ} (cell : SU7GeneratedTerminalColorCell n) :
    SU7TerminalPhysicalBranchCell n where
  leftWeight := cell.leftWeight
  rightWeight := cell.rightWeight
  colorLoop := cell.colorLoop
  gaugeAllowed := cell.gaugeAllowed
  colorSinglet := cell.colorSinglet
  nonSingletExcluded := cell.nonSingletExcluded
  residual := generatedTerminalColorResidual cell
  permanentHolonomy := generatedTerminalColorPermanentHolonomy cell

@[simp] theorem terminalPhysicalCellOfGeneratedColorCell_residual
    {n : ℕ} (cell : SU7GeneratedTerminalColorCell n) :
    terminalPhysicalResidual
        (terminalPhysicalCellOfGeneratedColorCell cell) =
      generatedTerminalColorResidual cell := rfl

@[simp] theorem terminalPhysicalCellOfGeneratedColorCell_holonomy
    {n : ℕ} (cell : SU7GeneratedTerminalColorCell n) :
    terminalPhysicalPermanentColorHolonomy
        (terminalPhysicalCellOfGeneratedColorCell cell) =
      generatedTerminalColorPermanentHolonomy cell := rfl

/-! ## Generated spectrum with scoped confinement -/

/-- A generated terminal color spectrum.

This is a concrete producer shape: it generates color cells, picks a ground
cell, proves the ground cell is residual-minimal, and confines holonomy only on
the generated list. -/
structure SU7GeneratedTerminalColorSpectrum where
  branchCells : ∀ n : ℕ, List (SU7GeneratedTerminalColorCell n)
  groundCell : ∀ n : ℕ, SU7GeneratedTerminalColorCell n
  ground_mem :
    ∀ n : ℕ, groundCell n ∈ branchCells n
  ground_residual_le :
    ∀ n : ℕ,
      ∀ cell : SU7GeneratedTerminalColorCell n,
        cell ∈ branchCells n ->
          generatedTerminalColorResidual (groundCell n) ≤
            generatedTerminalColorResidual cell
  confinement_excludes_generated_holonomy :
    ∀ n : ℕ,
      ∀ cell : SU7GeneratedTerminalColorCell n,
        cell ∈ branchCells n ->
          ¬ generatedTerminalColorPermanentHolonomy cell

/-- Set-orbit of a generated terminal color spectrum in one fiber. -/
def generatedTerminalColorSpectrumOrbit
    (G : SU7GeneratedTerminalColorSpectrum) (n : ℕ) :
    Set (SU7GeneratedTerminalColorCell n) :=
  {cell | cell ∈ G.branchCells n}

/-- Generated spectrum orbits are nonempty. -/
theorem generatedTerminalColorSpectrumOrbit_nonempty
    (G : SU7GeneratedTerminalColorSpectrum) (n : ℕ) :
    (generatedTerminalColorSpectrumOrbit G n).Nonempty :=
  ⟨G.groundCell n, G.ground_mem n⟩

/-- The generated ground cell is terminal in the generated orbit. -/
theorem generatedTerminalColorSpectrum_ground_terminal
    (G : SU7GeneratedTerminalColorSpectrum) (n : ℕ) :
    TerminalEnergyPoint
      (generatedTerminalColorSpectrumOrbit G n)
      generatedTerminalColorResidual
      (G.groundCell n) := by
  constructor
  · exact G.ground_mem n
  · intro cell hmem
    exact G.ground_residual_le n cell hmem

/-- Generated spectra provide the quantized minimum input. -/
theorem quantizedMinimum_of_generatedTerminalColorSpectrum
    (G : SU7GeneratedTerminalColorSpectrum) (n : ℕ) :
    QuantizedMinimum
      (generatedTerminalColorSpectrumOrbit G n)
      generatedTerminalColorResidual := by
  intro _hnonempty
  exact ⟨G.groundCell n, generatedTerminalColorSpectrum_ground_terminal G n⟩

/-- A generated spectrum produces zero generated color-loop residual in every
fiber. -/
theorem zeroGeneratedColorResidual_of_generatedTerminalColorSpectrum
    (G : SU7GeneratedTerminalColorSpectrum) (n : ℕ) :
    ∃ cell : SU7GeneratedTerminalColorCell n,
      cell ∈ generatedTerminalColorSpectrumOrbit G n ∧
        generatedTerminalColorResidual cell = 0 :=
  terminalConfinement_zeroResidual_onOrbit
    (generatedTerminalColorSpectrumOrbit_nonempty G n)
    (quantizedMinimum_of_generatedTerminalColorSpectrum G n)
    (fun _cell _hterminal hnonzero => hnonzero)
    (G.confinement_excludes_generated_holonomy n)

/-- A zero generated color residual projects to a zero terminal physical
residual. -/
theorem zeroTerminalPhysicalResidual_of_generatedTerminalColorSpectrum
    (G : SU7GeneratedTerminalColorSpectrum) (n : ℕ) :
    ∃ cell : SU7TerminalPhysicalBranchCell n,
      terminalPhysicalResidual cell = 0 := by
  rcases zeroGeneratedColorResidual_of_generatedTerminalColorSpectrum G n with
    ⟨cell, _hmem, hzero⟩
  exact ⟨terminalPhysicalCellOfGeneratedColorCell cell, by simp [hzero]⟩

/-! ## Concrete singlet color-loop spectrum -/

/-- The generated color-singlet terminal cell: the color loop is identically
zero, so residual is computed to be zero. -/
def generatedSingletTerminalColorCell (n : ℕ) :
    SU7GeneratedTerminalColorCell n where
  leftWeight := fun _ => 0
  rightWeight := fun _ => 0
  colorLoop := fun _ => 0
  gaugeAllowed := True
  colorSinglet := True
  nonSingletExcluded := True

theorem generatedSingletTerminalColorCell_exact (n : ℕ) :
    GeneratedTerminalColorLoopExact (generatedSingletTerminalColorCell n) :=
  fun _ => rfl

theorem generatedSingletTerminalColorCell_residual_zero (n : ℕ) :
    generatedTerminalColorResidual (generatedSingletTerminalColorCell n) = 0 :=
  generatedTerminalColorResidual_eq_zero_of_exact
    (generatedSingletTerminalColorCell n)
    (generatedSingletTerminalColorCell_exact n)

/-- The concrete singleton singlet spectrum. -/
def singletTerminalColorSpectrum :
    SU7GeneratedTerminalColorSpectrum where
  branchCells := fun n => [generatedSingletTerminalColorCell n]
  groundCell := generatedSingletTerminalColorCell
  ground_mem := by
    intro n
    simp
  ground_residual_le := by
    intro n cell hmem
    simp at hmem
    subst cell
    exact Nat.le_refl _
  confinement_excludes_generated_holonomy := by
    intro n cell hmem
    simp at hmem
    subst cell
    unfold generatedTerminalColorPermanentHolonomy
    simp [generatedSingletTerminalColorCell_residual_zero n]

/-- The concrete singlet spectrum produces zero terminal physical residual in
every fiber. -/
theorem zeroTerminalPhysicalResidual_of_singletSpectrum (n : ℕ) :
    ∃ cell : SU7TerminalPhysicalBranchCell n,
      terminalPhysicalResidual cell = 0 :=
  zeroTerminalPhysicalResidual_of_generatedTerminalColorSpectrum
    singletTerminalColorSpectrum n

/-! ## Certificate -/

/-- P983 certificate: scoped terminal confinement plus computed color-loop
readout produces zero residual without storing residual in the generated cell.
-/
structure GeneratedColorLoopScopedConfinementCertificate where
  scoped_terminal_confinement :
    ∀ {X : Type*} {orbit : Set X} {E : X -> ℕ}
      {PermanentColorHolonomy : X -> Prop},
      orbit.Nonempty ->
        QuantizedMinimum orbit E ->
          (∀ x : X,
            TerminalEnergyPoint orbit E x ->
              E x ≠ 0 ->
                PermanentColorHolonomy x) ->
            (∀ x : X, x ∈ orbit -> ¬ PermanentColorHolonomy x) ->
              ∃ x : X, x ∈ orbit ∧ E x = 0
  generated_exact_to_zero :
    ∀ {n : ℕ} (cell : SU7GeneratedTerminalColorCell n),
      GeneratedTerminalColorLoopExact cell ->
        generatedTerminalColorResidual cell = 0
  generated_spectrum_to_zero :
    SU7GeneratedTerminalColorSpectrum ->
      ∀ n : ℕ,
        ∃ cell : SU7TerminalPhysicalBranchCell n,
          terminalPhysicalResidual cell = 0
  singlet_spectrum_to_zero :
    ∀ n : ℕ,
      ∃ cell : SU7TerminalPhysicalBranchCell n,
        terminalPhysicalResidual cell = 0

def generatedColorLoopScopedConfinementCertificate :
    GeneratedColorLoopScopedConfinementCertificate where
  scoped_terminal_confinement := by
    intro X orbit E PermanentColorHolonomy hnonempty hminimum hterminal
      hconfinement
    exact
      terminalConfinement_zeroResidual_onOrbit
        hnonempty hminimum hterminal hconfinement
  generated_exact_to_zero :=
    generatedTerminalColorResidual_eq_zero_of_exact
  generated_spectrum_to_zero :=
    zeroTerminalPhysicalResidual_of_generatedTerminalColorSpectrum
  singlet_spectrum_to_zero :=
    zeroTerminalPhysicalResidual_of_singletSpectrum


end
end StandardModelConstraint
end SaturationMonoid
