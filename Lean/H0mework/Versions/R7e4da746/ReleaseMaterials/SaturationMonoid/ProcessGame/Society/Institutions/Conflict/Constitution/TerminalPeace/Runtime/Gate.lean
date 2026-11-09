import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Runtime.Trajectory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)
open ExposureGuard

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "Cut" => Root.Cut Party Good Port Technology Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port Technology Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port Technology Instrument

variable {seed : Root.Cut Party Good Port Technology Instrument} (community : Party → Community)

/-- The same position used by the original damage assessor and allocator. -/
def damageGate : Rule seed :=
  fun _ _ past input position =>
    position ∉ (Boundary.Actual.damages (endAt seed past) input community).map
      (fun damage => damage.position)

instance : DecidableRule (damageGate (seed := seed) community) := by
  intro _ _ past input position
  unfold damageGate
  infer_instance

theorem passes_exactly_the_original_damage_free_inputs
    (roster : List Party) (answers : OwnerAnswers seed) (past : Word) (input : Input) :
    (∀ position, damageGate community roster answers past input position) ↔
      Boundary.Actual.damages (endAt seed past) input community = [] := by
  constructor
  · intro allowed
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro damage listed
    exact allowed damage.position (List.mem_map_of_mem listed)
  · intro empty position
    simp [damageGate, empty]

variable {community}
  {roster : List Party} {answers : OwnerAnswers seed}

theorem selected_input_has_no_actual_damage
    {viable : Word → Prop} {check : Probe viable} {past : Word} {input : Input}
    (selected : Selection roster answers (damageGate community) viable check past input)
    (actual : Input) (written : actual ∈ selected.emitted) :
    Boundary.Actual.damages (endAt seed past) actual community = [] :=
  (passes_exactly_the_original_damage_free_inputs community roster answers past actual).mp
    (selected.every_emitted_input_is_lawful actual written).2

theorem an_original_damaging_attempt_is_returned_as_refused
    {viable : Word → Prop} {check : Probe viable} {past : Word} {input : Input}
    (harm : Boundary.Actual.DamageAt (endAt seed past) input community) :
    let selected := select roster answers (damageGate community) viable check past input
    input ∉ selected.emitted ∧
      ((∃ issue empty continues, selected = .stopped issue empty continues) ∨
        (∃ issue unavailable, selected = .retained issue unavailable)) := by
  dsimp only
  generalize select roster answers (damageGate community) viable check past input = selected
  have denied : input ∉ selected.emitted := by
    intro emitted
    have original := Boundary.Actual.every_actual_debit_is_assessed harm
    rw [selected_input_has_no_actual_damage selected input emitted] at original
    exact List.not_mem_nil original
  refine ⟨denied, ?_⟩
  cases selected with
  | accepted => exact (denied List.mem_cons_self).elim
  | stopped issue empty continues => exact Or.inl ⟨issue, empty, continues, rfl⟩
  | retained issue unavailable => exact Or.inr ⟨issue, unavailable, rfl⟩

/-- At a fixed original cut, every damage-free input with the original
authority and continuation is kept. Any safe authorization can only
allow inputs in this same domain. -/
theorem the_original_gate_keeps_every_safe_admissible_input
    {viable : Word → Prop} {check : Probe viable} {past : Word} {input : Input}
    (original : Admitted roster answers past input)
    (safe : Boundary.Actual.damages (endAt seed past) input community = [])
    {verified : PLift (viable (past ++ [input]))}
    (continues : check (past ++ [input]) = some verified) :
    (select roster answers (damageGate community) viable check past input).emitted = [input] :=
  the_composed_gate_forwards_an_admitted_continuation roster answers (damageGate community)
    viable check past input original
    ((passes_exactly_the_original_damage_free_inputs community roster answers past input).mpr safe)
    continues

theorem the_selected_suffix_preserves_all_original_loss_addresses
    {viable : Word → Prop} {check : Probe viable} {past : Word} {input : Input}
    (selected : Selection roster answers (damageGate community) viable check past input) :
    Reparation.Actual.originalLosses seed community (past ++ selected.emitted) =
      Reparation.Actual.originalLosses seed community past := by
  have unchanged (actual : Input) (safe : Boundary.Actual.damages (endAt seed past) actual community = []) :
      Reparation.Actual.originalLosses seed community (past ++ [actual]) =
        Reparation.Actual.originalLosses seed community past := by
    rw [Reparation.Actual.losses_snoc]
    simp [Reparation.Actual.openings, safe]
  cases selected with
  | retained => simp [Selection.emitted]
  | stopped _ empty _ =>
    exact unchanged stop (Boundary.Actual.no_material_write_has_no_damage _ _ _ empty)
  | accepted _ additional _ =>
    exact unchanged input ((passes_exactly_the_original_damage_free_inputs _ _ _ _ _).mp additional)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace
