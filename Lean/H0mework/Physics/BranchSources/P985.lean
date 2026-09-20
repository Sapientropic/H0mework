import H0mework.Physics.BranchSources.P984

/-!
# Proposition 985: full SU(7) incidence spectrum splits into exact/confined sectors

P984 generated the singlet incidence sector.  This file generates the full
SU(7) incidence spectrum and proves the representation-slot decomposition:
each generated slot is either color-loop exact or carries permanent holonomy.
The confined exact sector is then used as the P983 spectrum input.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open RunningSigmaBeta

set_option linter.defProp false

/-! ## Full and exact incidence spectra -/

/-- The color-exact incidence slots: they do not touch the color block in the
terminal color-loop readout. -/
def su7ColorExactIncidences : List SU7BlockIncidence :=
  [.weakPositiveSinglet, .weakNegativeSinglet, .positiveNegativeSinglet]

/-- The color-charged incidence slots: they touch the color block. -/
def su7ColorChargedIncidences : List SU7BlockIncidence :=
  [.colorWeak, .colorPositiveSinglet, .colorNegativeSinglet]

/-- Full SU(7) terminal incidence spectrum generated from all Schubert cells
and all six block incidences. -/
def su7RepresentationFullTerminalCells (n : ℕ) :
    List (SU7GeneratedTerminalColorCell n) :=
  SU3FlagSchubertCell.all.flatMap fun branch =>
    SU7BlockIncidence.all.map fun incidence =>
      generatedTerminalColorCellOfRepresentationSlot n branch incidence

/-- Confined exact SU(7) terminal incidence spectrum generated from all
Schubert cells and the color-exact incidence subcarrier. -/
def su7RepresentationExactTerminalCells (n : ℕ) :
    List (SU7GeneratedTerminalColorCell n) :=
  SU3FlagSchubertCell.all.flatMap fun branch =>
    su7ColorExactIncidences.map fun incidence =>
      generatedTerminalColorCellOfRepresentationSlot n branch incidence

/-! ## Incidence-level decomposition -/

/-- Any color-exact incidence has zero terminal color-loop readout. -/
theorem terminalColorLoop_exact_of_mem_colorExactIncidences
    {incidence : SU7BlockIncidence}
    (hmem : incidence ∈ su7ColorExactIncidences) :
    ∀ i : Fin 3, terminalColorLoopOfIncidence incidence i = 0 := by
  simp [su7ColorExactIncidences] at hmem
  rcases hmem with h | h | h
  · subst incidence
    intro i
    rfl
  · subst incidence
    intro i
    rfl
  · subst incidence
    exact terminalColorLoop_positiveNegativeSinglet_exact

/-- Any generated slot from a color-exact incidence has zero residual. -/
theorem generatedRepresentationExactIncidence_residual_zero
    (n : ℕ) (branch : SU3FlagSchubertCell)
    {incidence : SU7BlockIncidence}
    (hmem : incidence ∈ su7ColorExactIncidences) :
    generatedTerminalColorResidual
        (generatedTerminalColorCellOfRepresentationSlot n branch incidence) =
      0 :=
  generatedTerminalColorResidual_eq_zero_of_exact
    (generatedTerminalColorCellOfRepresentationSlot n branch incidence)
    (terminalColorLoop_exact_of_mem_colorExactIncidences hmem)

/-- Color-charged incidences produce permanent holonomy under the terminal
color-loop readout. -/
theorem generatedRepresentationChargedIncidence_holonomy
    (n : ℕ) (branch : SU3FlagSchubertCell)
    {incidence : SU7BlockIncidence}
    (hmem : incidence ∈ su7ColorChargedIncidences) :
    generatedTerminalColorPermanentHolonomy
      (generatedTerminalColorCellOfRepresentationSlot n branch incidence) := by
  simp [su7ColorChargedIncidences] at hmem
  unfold generatedTerminalColorPermanentHolonomy generatedTerminalColorResidual
  rcases hmem with h | h | h
  · subst incidence
    norm_num [generatedTerminalColorCellOfRepresentationSlot,
      terminalColorLoopOfIncidence]
  · subst incidence
    norm_num [generatedTerminalColorCellOfRepresentationSlot,
      terminalColorLoopOfIncidence]
  · subst incidence
    norm_num [generatedTerminalColorCellOfRepresentationSlot,
      terminalColorLoopOfIncidence]

/-- Every SU(7) incidence is either color-exact or color-charged. -/
theorem su7Incidence_exact_or_charged
    (incidence : SU7BlockIncidence) :
    incidence ∈ su7ColorExactIncidences ∨
      incidence ∈ su7ColorChargedIncidences := by
  cases incidence <;>
    simp [su7ColorExactIncidences, su7ColorChargedIncidences]

/-- Every generated full-spectrum representation slot is either exact or
carries permanent holonomy. -/
theorem generatedRepresentationSlot_exact_or_holonomy
    (n : ℕ) (branch : SU3FlagSchubertCell)
    (incidence : SU7BlockIncidence) :
    generatedTerminalColorResidual
        (generatedTerminalColorCellOfRepresentationSlot n branch incidence) =
        0 ∨
      generatedTerminalColorPermanentHolonomy
        (generatedTerminalColorCellOfRepresentationSlot n branch incidence) := by
  rcases su7Incidence_exact_or_charged incidence with hExact | hCharged
  · exact Or.inl
      (generatedRepresentationExactIncidence_residual_zero
        n branch hExact)
  · exact Or.inr
      (generatedRepresentationChargedIncidence_holonomy
        n branch hCharged)

/-! ## Exact sector as a confined terminal spectrum -/

/-- The identity Schubert cell with the singlet incidence belongs to the exact
incidence spectrum. -/
theorem su7RepresentationExactGround_mem (n : ℕ) :
    generatedTerminalColorCellOfRepresentationSlot n
        SU3FlagSchubertCell.e
        SU7BlockIncidence.positiveNegativeSinglet ∈
      su7RepresentationExactTerminalCells n := by
  unfold su7RepresentationExactTerminalCells
  exact List.mem_flatMap.mpr
    ⟨SU3FlagSchubertCell.e,
      by simp [SU3FlagSchubertCell.all],
      by
        exact List.mem_map.mpr
          ⟨SU7BlockIncidence.positiveNegativeSinglet,
            by simp [su7ColorExactIncidences],
            rfl⟩⟩

/-- Every member of the exact terminal spectrum has zero residual. -/
theorem su7RepresentationExactCell_residual_zero_of_mem
    {n : ℕ} {cell : SU7GeneratedTerminalColorCell n}
    (hmem : cell ∈ su7RepresentationExactTerminalCells n) :
    generatedTerminalColorResidual cell = 0 := by
  unfold su7RepresentationExactTerminalCells at hmem
  rcases List.mem_flatMap.mp hmem with
    ⟨branch, _hbranch, hmap⟩
  rcases List.mem_map.mp hmap with
    ⟨incidence, hincidence, rfl⟩
  exact generatedRepresentationExactIncidence_residual_zero
    n branch hincidence

/-- The exact-sector spectrum generated from the full SU(7) incidence
carrier after confinement removes color-holonomy slots. -/
def su7RepresentationExactTerminalColorSpectrum :
    SU7GeneratedTerminalColorSpectrum where
  branchCells := su7RepresentationExactTerminalCells
  groundCell := fun n =>
    generatedTerminalColorCellOfRepresentationSlot n
      SU3FlagSchubertCell.e
      SU7BlockIncidence.positiveNegativeSinglet
  ground_mem := su7RepresentationExactGround_mem
  ground_residual_le := by
    intro n cell _hmem
    rw [generatedRepresentationSingletTerminalCell_residual_zero
      n SU3FlagSchubertCell.e]
    exact Nat.zero_le _
  confinement_excludes_generated_holonomy := by
    intro n cell hmem hhol
    unfold generatedTerminalColorPermanentHolonomy at hhol
    exact hhol (su7RepresentationExactCell_residual_zero_of_mem hmem)

/-- The exact-sector SU(7) incidence spectrum produces zero terminal physical
residual in every fiber. -/
theorem zeroTerminalPhysicalResidual_of_su7RepresentationExactSpectrum
    (n : ℕ) :
    ∃ cell : SU7TerminalPhysicalBranchCell n,
      terminalPhysicalResidual cell = 0 :=
  zeroTerminalPhysicalResidual_of_generatedTerminalColorSpectrum
    su7RepresentationExactTerminalColorSpectrum n

/-! ## Certificate -/

/-- P985 certificate: the full SU(7) incidence spectrum decomposes into exact
and confined-away color-holonomy sectors, and the exact sector feeds P983. -/
structure SU7FullIncidenceTerminalSpectrumDecompositionCertificate where
  full_cells :
    ∀ n : ℕ, List (SU7GeneratedTerminalColorCell n)
  exact_cells :
    ∀ n : ℕ, List (SU7GeneratedTerminalColorCell n)
  incidence_decomposition :
    ∀ incidence : SU7BlockIncidence,
      incidence ∈ su7ColorExactIncidences ∨
        incidence ∈ su7ColorChargedIncidences
  slot_exact_or_holonomy :
    ∀ (n : ℕ) (branch : SU3FlagSchubertCell)
      (incidence : SU7BlockIncidence),
      generatedTerminalColorResidual
          (generatedTerminalColorCellOfRepresentationSlot
            n branch incidence) = 0 ∨
        generatedTerminalColorPermanentHolonomy
          (generatedTerminalColorCellOfRepresentationSlot
            n branch incidence)
  exact_member_zero :
    ∀ {n : ℕ} {cell : SU7GeneratedTerminalColorCell n},
      cell ∈ su7RepresentationExactTerminalCells n ->
        generatedTerminalColorResidual cell = 0
  exact_spectrum :
    SU7GeneratedTerminalColorSpectrum
  exact_spectrum_zero :
    ∀ n : ℕ,
      ∃ cell : SU7TerminalPhysicalBranchCell n,
        terminalPhysicalResidual cell = 0

/-- Canonical P985 full-incidence terminal spectrum decomposition certificate.
-/
def su7FullIncidenceTerminalSpectrumDecompositionCertificate :
    SU7FullIncidenceTerminalSpectrumDecompositionCertificate where
  full_cells := su7RepresentationFullTerminalCells
  exact_cells := su7RepresentationExactTerminalCells
  incidence_decomposition := su7Incidence_exact_or_charged
  slot_exact_or_holonomy :=
    generatedRepresentationSlot_exact_or_holonomy
  exact_member_zero :=
    su7RepresentationExactCell_residual_zero_of_mem
  exact_spectrum := su7RepresentationExactTerminalColorSpectrum
  exact_spectrum_zero :=
    zeroTerminalPhysicalResidual_of_su7RepresentationExactSpectrum


end
end StandardModelConstraint
end SaturationMonoid
