import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Aggression
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Agenda

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution

open Capitalism.Universal.Source.Program

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument

def isAggressive (source : C) (community : Party → Community) (option : Root.Admitted source) : Bool :=
  !(Boundary.aggressions source option.val community option.property).isEmpty

theorem isAggressive_exact {source : C} {community : Party → Community} (option : Root.Admitted source) :
    isAggressive source community option = true ↔ Nonempty (Boundary.AggressionAt source option.val community) := by
  unfold isAggressive
  cases observed : Boundary.aggressions source option.val community option.property with
  | nil =>
    constructor
    · simp
    · rintro ⟨attack⟩
      have present := attack.listed_in_generated_aggressions
      rw [observed] at present
      exact (List.not_mem_nil present).elim
  | cons attack tail =>
    exact ⟨fun _ => ⟨attack⟩, fun _ => rfl⟩

def aggressors (source : C) (community : Party → Community) (submitted : List Word) :
    List (Root.Admitted source) :=
  (Root.admitted source submitted).filter (isAggressive source community)

def unaggressive (source : C) (community : Party → Community) (submitted : List Word) :
    List (Root.Admitted source) :=
  (Root.admitted source submitted).filter (fun option => !(isAggressive source community option))

theorem aggressors_empty_iff (source : C) (community : Party → Community) (submitted : List Word) :
    aggressors source community submitted = [] ↔
      ∀ word ∈ submitted, ¬ Nonempty (Boundary.AggressionAt source word community) := by
  rw [List.eq_nil_iff_forall_not_mem]
  constructor
  · rintro none word original ⟨attack⟩
    let admitted : Root.Admitted source := ⟨word, attack.paid⟩
    exact none admitted (List.mem_filter.mpr
      ⟨Root.mem_admitted.mpr original, (isAggressive_exact admitted).mpr ⟨attack⟩⟩)
  · intro none option listed
    obtain ⟨submitted, aggressive⟩ := List.mem_filter.mp listed
    exact none option.val (Root.mem_admitted.mp submitted) ((isAggressive_exact option).mp aggressive)

/-- The original offers are checked once as executions. The two menus
come from the M11 incidence, including any change at the next cut. -/
def pressure (source : C) (community : Party → Community) (read : C → ℚ) (submitted : List Word) :
    Option ℚ :=
  Threshold.gap (Root.value source read) (Root.value source read)
    (aggressors source community submitted) (unaggressive source community submitted)

theorem a_positive_m11_gap_has_a_paid_invasion_and_a_paid_nonaggressive_baseline
    (source : C) (community : Party → Community) (read : C → ℚ) (submitted : List Word) (value : ℚ)
    (computed : pressure source community read submitted = some value) (positive : 0 < value) :
    ∃ attack ∈ submitted, ∃ peace ∈ submitted,
      Nonempty (Boundary.AggressionAt source attack community) ∧ Root.Paid source peace ∧
      ¬ Nonempty (Boundary.AggressionAt source peace community) ∧
      read (Root.terminal source peace) < read (Root.terminal source attack) := by
  obtain ⟨attack, attacking, peace, quiet, exactValue, _, _⟩ := Threshold.gap_exact computed
  obtain ⟨attackPaid, attackClass⟩ := List.mem_filter.mp attacking
  obtain ⟨peacePaid, peaceClass⟩ := List.mem_filter.mp quiet
  have nonAggressive : ¬ Nonempty (Boundary.AggressionAt source peace.val community) := by
    intro actual
    have yes := (isAggressive_exact peace).mpr actual
    simp [yes] at peaceClass
  exact ⟨attack.val, Root.mem_admitted.mp attackPaid, peace.val, Root.mem_admitted.mp peacePaid,
    (isAggressive_exact attack).mp attackClass, peace.property, nonAggressive,
    sub_pos.mp (exactValue ▸ positive)⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution
