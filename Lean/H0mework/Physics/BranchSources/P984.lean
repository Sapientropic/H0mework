import H0mework.Physics.ColorLoops.P983

/-!
# Proposition 984: SU(7) representation slots generate singlet terminal spectrum

P983 built a singleton singlet spectrum.  This file replaces that singleton
with a finite spectrum generated from the existing SU(7) representation-slot
carriers:

* the six Schubert cells of the color orbit;
* the SU(7) block-incidence carrier;
* the singlet incidence between the two gauge-transparent blocks.

The generated cells still do not store residual.  Their color-loop residual is
computed from the representation incidence readout.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open RunningSigmaBeta

set_option linter.defProp false

/-! ## Representation-slot terminal cells -/

/-- A block-label weight readout for terminal generated cells.  This records
only the SU(7) carrier block, not an endpoint arithmetic code. -/
def terminalWeightOfCarrierBlock
    (block : SU7CarrierBlock) : Fin 7 -> ℤ :=
  fun _ => (SU7CarrierBlock.code block : ℤ)

/-- Color-loop readout of a SU(7) incidence.  Incidences touching the color
block carry one unit of color-loop residual; non-color incidences are
color-neutral. -/
def terminalColorLoopOfIncidence
    (incidence : SU7BlockIncidence) : Fin 3 -> ℤ :=
  match incidence with
  | .colorWeak => fun i => if i = (0 : Fin 3) then 1 else 0
  | .colorPositiveSinglet => fun i => if i = (0 : Fin 3) then 1 else 0
  | .colorNegativeSinglet => fun i => if i = (0 : Fin 3) then 1 else 0
  | .weakPositiveSinglet => fun _ => 0
  | .weakNegativeSinglet => fun _ => 0
  | .positiveNegativeSinglet => fun _ => 0

/-- A generated terminal color cell from a Schubert branch and SU(7)
incidence slot. -/
def generatedTerminalColorCellOfRepresentationSlot
    (n : ℕ)
    (_branch : SU3FlagSchubertCell)
    (incidence : SU7BlockIncidence) :
    SU7GeneratedTerminalColorCell n where
  leftWeight :=
    terminalWeightOfCarrierBlock (SU7BlockIncidence.endpoints incidence).1
  rightWeight :=
    terminalWeightOfCarrierBlock (SU7BlockIncidence.endpoints incidence).2
  colorLoop := terminalColorLoopOfIncidence incidence
  gaugeAllowed := True
  colorSinglet :=
    terminalColorLoopOfIncidence incidence = fun _ => 0
  nonSingletExcluded :=
    terminalColorLoopOfIncidence incidence = fun _ => 0

/-- The singlet incidence has exact zero color-loop readout. -/
theorem terminalColorLoop_positiveNegativeSinglet_exact :
    ∀ i : Fin 3,
      terminalColorLoopOfIncidence
          SU7BlockIncidence.positiveNegativeSinglet i = 0 := by
  intro i
  rfl

/-- The representation-generated singlet terminal cell is exact. -/
theorem generatedRepresentationSingletTerminalCell_exact
    (n : ℕ) (branch : SU3FlagSchubertCell) :
    GeneratedTerminalColorLoopExact
      (generatedTerminalColorCellOfRepresentationSlot n branch
        SU7BlockIncidence.positiveNegativeSinglet) :=
  terminalColorLoop_positiveNegativeSinglet_exact

/-- Therefore its generated color-loop residual computes to zero. -/
theorem generatedRepresentationSingletTerminalCell_residual_zero
    (n : ℕ) (branch : SU3FlagSchubertCell) :
    generatedTerminalColorResidual
        (generatedTerminalColorCellOfRepresentationSlot n branch
          SU7BlockIncidence.positiveNegativeSinglet) = 0 :=
  generatedTerminalColorResidual_eq_zero_of_exact
    (generatedTerminalColorCellOfRepresentationSlot n branch
      SU7BlockIncidence.positiveNegativeSinglet)
    (generatedRepresentationSingletTerminalCell_exact n branch)

/-! ## Finite Schubert-generated singlet spectrum -/

/-- The singlet terminal spectrum generated across all six Schubert cells. -/
def su7RepresentationSingletTerminalCells (n : ℕ) :
    List (SU7GeneratedTerminalColorCell n) :=
  SU3FlagSchubertCell.all.map fun branch =>
    generatedTerminalColorCellOfRepresentationSlot n branch
      SU7BlockIncidence.positiveNegativeSinglet

/-- The identity Schubert cell is a generated singlet terminal cell. -/
theorem su7RepresentationSingletGround_mem (n : ℕ) :
    generatedTerminalColorCellOfRepresentationSlot n
        SU3FlagSchubertCell.e
        SU7BlockIncidence.positiveNegativeSinglet ∈
      su7RepresentationSingletTerminalCells n := by
  unfold su7RepresentationSingletTerminalCells
  exact List.mem_map.mpr
    ⟨SU3FlagSchubertCell.e, by simp [SU3FlagSchubertCell.all], rfl⟩

/-- Every member of the representation-generated singlet spectrum has zero
generated color-loop residual. -/
theorem su7RepresentationSingletCell_residual_zero_of_mem
    {n : ℕ} {cell : SU7GeneratedTerminalColorCell n}
    (hmem : cell ∈ su7RepresentationSingletTerminalCells n) :
    generatedTerminalColorResidual cell = 0 := by
  unfold su7RepresentationSingletTerminalCells at hmem
  rcases List.mem_map.mp hmem with ⟨branch, _hbranch, rfl⟩
  exact generatedRepresentationSingletTerminalCell_residual_zero n branch

/-- The finite SU(7) representation-slot-generated singlet terminal spectrum.
-/
def su7RepresentationSingletTerminalColorSpectrum :
    SU7GeneratedTerminalColorSpectrum where
  branchCells := su7RepresentationSingletTerminalCells
  groundCell := fun n =>
    generatedTerminalColorCellOfRepresentationSlot n
      SU3FlagSchubertCell.e
      SU7BlockIncidence.positiveNegativeSinglet
  ground_mem := su7RepresentationSingletGround_mem
  ground_residual_le := by
    intro n cell _hmem
    rw [generatedRepresentationSingletTerminalCell_residual_zero
      n SU3FlagSchubertCell.e]
    exact Nat.zero_le _
  confinement_excludes_generated_holonomy := by
    intro n cell hmem hhol
    unfold generatedTerminalColorPermanentHolonomy at hhol
    exact hhol (su7RepresentationSingletCell_residual_zero_of_mem hmem)

/-- The SU(7) representation-slot-generated singlet spectrum produces zero
terminal physical residual in every fiber. -/
theorem zeroTerminalPhysicalResidual_of_su7RepresentationSingletSpectrum
    (n : ℕ) :
    ∃ cell : SU7TerminalPhysicalBranchCell n,
      terminalPhysicalResidual cell = 0 :=
  zeroTerminalPhysicalResidual_of_generatedTerminalColorSpectrum
    su7RepresentationSingletTerminalColorSpectrum n

/-! ## Certificate -/

/-- P984 certificate: SU(7) representation slots generate the finite singlet
terminal spectrum consumed by P983. -/
structure SU7RepresentationSingletTerminalSpectrumCertificate where
  incidence_color_loop :
    SU7BlockIncidence -> Fin 3 -> ℤ
  singlet_incidence_exact :
    ∀ i : Fin 3,
      terminalColorLoopOfIncidence
          SU7BlockIncidence.positiveNegativeSinglet i = 0
  generated_cells :
    ∀ n : ℕ, List (SU7GeneratedTerminalColorCell n)
  generated_member_zero :
    ∀ {n : ℕ} {cell : SU7GeneratedTerminalColorCell n},
      cell ∈ su7RepresentationSingletTerminalCells n ->
        generatedTerminalColorResidual cell = 0
  generated_spectrum :
    SU7GeneratedTerminalColorSpectrum
  generated_spectrum_zero :
    ∀ n : ℕ,
      ∃ cell : SU7TerminalPhysicalBranchCell n,
        terminalPhysicalResidual cell = 0

/-- Canonical P984 representation-slot singlet spectrum certificate. -/
def su7RepresentationSingletTerminalSpectrumCertificate :
    SU7RepresentationSingletTerminalSpectrumCertificate where
  incidence_color_loop := terminalColorLoopOfIncidence
  singlet_incidence_exact := terminalColorLoop_positiveNegativeSinglet_exact
  generated_cells := su7RepresentationSingletTerminalCells
  generated_member_zero :=
    su7RepresentationSingletCell_residual_zero_of_mem
  generated_spectrum := su7RepresentationSingletTerminalColorSpectrum
  generated_spectrum_zero :=
    zeroTerminalPhysicalResidual_of_su7RepresentationSingletSpectrum


end
end StandardModelConstraint
end SaturationMonoid
