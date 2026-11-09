import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Frontier
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Frontier

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Reparation.Actual (StateAt)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (prior : StateAt seed community cut)
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin : RawCurrent Party Good Technology Instrument) (roster : List Party)
  (menus : Menus Party Good Port Technology Instrument)

abbrev Current := AnyAuthoritativeRootCurrent × ℚ
abbrev Write (Party Good Port Technology Instrument : Type) :=
  AnyAuthoritativeRootCurrent × List (ExecutionItem Party Good Port Technology Instrument)

def currentAt (n : Nat) : Current :=
  let whole := match n with
    | 0 => prior.resident.erase
    | n + 1 => (run prior input origin roster menus n).state.resident.erase
  (whole, clockAt prior input origin roster menus n)

def writeAt (n : Nat) : Write Party Good Port Technology Instrument :=
  let actual := run prior input origin roster menus n
  (actual.state.resident.erase, actual.read.items)

variable (external : External.Trace Current (Write Party Good Port Technology Instrument))

/-- Every external write must match the complete installed successor
and the entire actual material inventory at its original position. -/
def auditExternal :=
  external.audit (currentAt prior input origin roster menus) (writeAt prior input origin roster menus)

theorem cofinal_external_time_iff_complete_original_progress
    (factor : external.Factors (currentAt prior input origin roster menus)
      (writeAt prior input origin roster menus) external.ordinal)
    (internal : ClockCofinal prior input origin roster menus) :
    external.Progress ↔ ∀ start bound, ∃ visit ≥ start, bound < (external.current visit).2 := by
  have mono : Monotone (Prod.snd ∘ currentAt prior input origin roster menus) :=
    clock_mono prior input origin roster menus
  constructor
  · intro progress
    apply external.clock_cofinal_after_each_visit_of_progress Prod.snd factor mono _ progress
    intro bound
    obtain ⟨n, _, paid⟩ := internal 0 bound
    exact ⟨n, paid⟩
  · intro cofinal
    apply external.progress_of_clock_cofinal Prod.snd factor mono
    intro bound
    obtain ⟨n, _, paid⟩ := cofinal 0 bound
    exact ⟨n, paid⟩

theorem every_complete_external_presentation_crosses_the_same_first_whole_write
    (factor : external.Factors (currentAt prior input origin roster menus)
      (writeAt prior input origin roster menus) external.ordinal) (progress : external.Progress) :
    ∃! visit, external.FirstAt 1 visit ∧
      (external.current visit).1 = (run prior input origin roster menus 0).state.resident.erase := by
  obtain ⟨visit, first, unique⟩ := external.earliest_cut_of_reached (progress 1)
  refine ⟨visit, ⟨first, ?_⟩, fun other found => unique other found.1⟩
  exact congrArg Prod.fst ((factor.reads visit).trans (congrArg (currentAt prior input origin roster menus) first.1))

theorem the_same_original_clock_and_material_effect_hold_in_every_factored_write
    (factor : external.Factors (currentAt prior input origin roster menus)
      (writeAt prior input origin roster menus) external.ordinal) (visit : Nat) :
    (external.current visit).2 = clockAt prior input origin roster menus (external.ordinal visit) ∧
      ∀ written, external.effect visit = some written →
        ∀ item ∈ written.2, ∀ key, Reparation.loss input.law community item key = 0 := by
  refine ⟨congrArg Prod.snd (factor.reads visit), ?_⟩
  intro written writes
  rw [factor.writes visit written writes]
  exact no_actual_service_or_refusal_causes_new_war_damage prior input origin roster menus (external.ordinal visit)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime
