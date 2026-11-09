import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Inventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.SourceReserve

open Capitalism.Universal.Source.Program
open Reparation.Actual (Occurrence Script)

variable {Party Good Port Technology Instrument : Type} [DecidableEq Good]

private def held (original current : ℚ) : ℚ := max 0 (max original current)

/-- The old and current minima constrain the same service. Necessity and
maintenance use separate shares of the same stock. -/
def atRaw (law : RawLaw Party Good Port Technology Instrument)
    (original current : RawCurrent Party Good Technology Instrument) (person : Party) (good : Good) : ℚ :=
  held (amount Good (law.necessities original person) good)
    (amount Good (law.necessities current person) good) +
  held (amount Good (law.mandatoryMaintenance original person) good)
    (amount Good (law.mandatoryMaintenance current person) good)

theorem atRaw_nonnegative (law : RawLaw Party Good Port Technology Instrument)
    (original current : RawCurrent Party Good Technology Instrument) (person : Party) (good : Good) :
    0 ≤ atRaw law original current person good :=
  add_nonneg (le_max_left _ _) (le_max_left _ _)

def Fits (law : RawLaw Party Good Port Technology Instrument)
    (original current : RawCurrent Party Good Technology Instrument) (person : Party) (good : Good)
    (stock : ℚ) : Prop :=
  ∃ life maintain : ℚ,
    (0 ≤ life ∧ amount Good (law.necessities original person) good ≤ life ∧
      amount Good (law.necessities current person) good ≤ life) ∧
    (0 ≤ maintain ∧ amount Good (law.mandatoryMaintenance original person) good ≤ maintain ∧
      amount Good (law.mandatoryMaintenance current person) good ≤ maintain) ∧
    life + maintain ≤ stock

theorem atRaw_le_iff (law : RawLaw Party Good Port Technology Instrument)
    (original current : RawCurrent Party Good Technology Instrument) (person : Party) (good : Good) (stock : ℚ) :
    atRaw law original current person good ≤ stock ↔ Fits law original current person good stock := by
  constructor
  · intro enough
    refine ⟨_, _, ⟨le_max_left _ _, ?_, ?_⟩, ⟨le_max_left _ _, ?_, ?_⟩, enough⟩
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  · rintro ⟨life, maintain, ⟨lifeZero, lifeOld, lifeNew⟩, ⟨maintainZero, maintainOld, maintainNew⟩, enough⟩
    exact (add_le_add (max_le lifeZero (max_le lifeOld lifeNew))
      (max_le maintainZero (max_le maintainOld maintainNew))).trans enough

variable {Community : Type} [DecidableEq Party] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

noncomputable def reserveAt (loss : Occurrence seed community)
    (front : Script Party Good Port Technology Instrument) : Party → Good → ℚ :=
  atRaw seed.native.input.law (originalRaw loss) (prefixRaw loss front)

noncomputable def openingReserve (loss : Occurrence seed community) : Party → Good → ℚ :=
  reserveAt loss []

theorem reserveAt_nonnegative (loss : Occurrence seed community)
    (front : Script Party Good Port Technology Instrument) (person : Party) (good : Good) :
    0 ≤ reserveAt loss front person good :=
  atRaw_nonnegative _ _ _ _ _

/-- Each live inventory read protects its own need vector, even across a
technology write that changes the later stock. -/
def ProtectsNeeds (loss : Occurrence seed community)
    (word : Script Party Good Port Technology Instrument) : Prop :=
  ∀ cut ∈ inventoryTrace loss word, ∀ person good,
    atRaw seed.native.input.law (originalRaw loss) cut.raw person good ≤ cut.raw.stock person good

theorem protectsNeeds_iff (loss : Occurrence seed community)
    (word : Script Party Good Port Technology Instrument) :
    ProtectsNeeds loss word ↔ ∀ cut ∈ inventoryTrace loss word, ∀ person good,
      Fits seed.native.input.law (originalRaw loss) cut.raw person good (cut.raw.stock person good) := by
  constructor <;> intro safe cut listed person good
  · exact (atRaw_le_iff _ _ _ _ _ _).mp (safe cut listed person good)
  · exact (atRaw_le_iff _ _ _ _ _ _).mpr (safe cut listed person good)

theorem openingReserve_le_atRaw (loss : Occurrence seed community)
    (raw : RawCurrent Party Good Technology Instrument) (person : Party) (good : Good) :
    openingReserve loss person good ≤ atRaw seed.native.input.law (originalRaw loss) raw person good := by
  have start : prefixRaw loss [] = originalRaw loss := by
    simp only [prefixRaw, originalRaw, List.append_nil]
  unfold openingReserve reserveAt
  rw [start]
  unfold atRaw held
  simp only [max_self]
  apply add_le_add <;> exact max_le (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _))

theorem ProtectsNeeds.retains_opening_reserve (loss : Occurrence seed community)
    {word : Script Party Good Port Technology Instrument} (safe : ProtectsNeeds loss word) :
    ProtectedThrough loss (openingReserve loss) word :=
  fun cut listed person good => (openingReserve_le_atRaw loss cut.raw person good).trans (safe cut listed person good)

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.SourceReserve
