import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable.Start
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation.Material
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Contract.Deadline
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime.Resign

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable

open Capitalism.Universal.Source.Program Capitalism.Universal.Root Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Root Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Root.Registered.Macro
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (normalise)
open Material.Continuation
open Installed (Port Tech Raw Req liftRequest)
open Transition.Handoff.Consumers.Continuation (gain gain_nonnegative)

noncomputable section

abbrev Word := Reparation.Actual.Script Bool Bool Port Tech Unit
abbrev Item := ExecutionItem Bool Bool Port Tech Unit
abbrev Cell := Bool × Use × Bool × ℚ
abbrev checkInput := Public.Scope.checkInput input
abbrev material := checkInput.law

/-- The same replenishment recipe as the paid handoff, at the registered
Mandate source's ordinary ports. -/
def period : List Req := Transition.Handoff.Consumers.Actual.period.map liftRequest

def service : Reparation.Actual.Input Bool Bool Port Tech Unit := some (.execute period)

theorem original_consents_empty : ∀ request ∈ period, request.consents = [] := by decide +kernel

theorem normalised_period : normalise period = period := rfl

theorem time_independent : material.TimeIndependent :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem reserve_insensitive : material.ReserveInsensitive :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem paid_gain : (material.execute opening 0 period).final = opening.addReserve gain := by
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;> decide +kernel
  · funext instrument debtor creditor
    cases instrument
    cases debtor <;> cases creditor <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem opening_shared (members : List Bool) : SharedPeriod checkInput opening members period := by
  refine ⟨by decide +kernel, ?_, fun _ _ _ _ _ => rfl, trivial⟩
  intro person _
  cases person <;> decide +kernel

theorem opening_valid : ∀ item ∈ material.rawItems opening period, material.Valid item.before item.request :=
  fun item present => ((opening_shared []).1 item present).1

theorem native_cell (origin : Raw) (members : List Bool) (cell : Cell)
    (listed : cell ∈ Material.originalRequirements checkInput origin members) :
    ∃ person, cell = (person, .necessity, true, (1 : ℚ)) := by
  unfold Material.originalRequirements at listed
  obtain ⟨person, _, actual⟩ := List.mem_flatMap.mp listed
  have one : amount Bool [(true, 1)] true = 1 := by decide +kernel
  change cell ∈ [(person, .necessity, true, amount Bool [(true, 1)] true)] at actual
  rw [one] at actual
  exact ⟨person, List.mem_singleton.mp actual⟩

private theorem opening_floor (origin : Raw) (members : List Bool) :
    Material.OriginalNeedFloor checkInput origin opening members period := by
  intro cell listed
  obtain ⟨person, rfl⟩ := native_cell origin members cell listed
  cases person <;> decide +kernel

def materialAt (periods : Nat) : Raw := (repeatPeriod checkInput opening period).currentAt periods

theorem original_material_guard (origin : Raw) (members : List Bool) (periods : Nat) :
    Review.Guarded.Checks checkInput origin (materialAt periods) members period := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · exact productive_period_keeps_original_need_floor checkInput time_independent reserve_insensitive opening
      period gain gain_nonnegative origin members paid_gain opening_valid (opening_floor origin members) periods
  · exact productive_shared_period_generates_every_paid_period checkInput time_independent reserve_insensitive
      opening period gain gain_nonnegative members paid_gain (opening_shared members) periods

theorem material_keeps_stocks_and_rows (periods : Nat) :
    (∀ person good, (materialAt periods).stock person good = opening.stock person good + (periods : ℚ) * gain person good) ∧
      (materialAt periods).claims = opening.claims ∧ (materialAt periods).technology = opening.technology :=
  productive_period_exact_resources checkInput time_independent reserve_insensitive opening period
    gain gain_nonnegative paid_gain opening_valid periods

theorem material_pays_each_necessity (periods : Nat) (person : Bool) :
    (1 : ℚ) ≤ Material.actualUse checkInput (materialAt periods) period person .necessity true := by
  apply (original_material_guard opening [person] periods).2.1 (person, .necessity, true, 1)
  have one : amount Bool [(true, 1)] true = 1 := by decide +kernel
  change (person, Use.necessity, true, (1 : ℚ)) ∈
    [(person, Use.necessity, true, amount Bool [(true, 1)] true)]
  rw [one]
  exact List.mem_singleton_self _

theorem material_successor (periods : Nat) : material.next (materialAt periods) period = materialAt (periods + 1) := rfl

theorem material_clock (periods : Nat) : (materialAt periods).clock = 4 + (periods : ℚ) := by
  induction periods with
  | zero =>
    change (4 : ℚ) = 4 + (0 : ℕ)
    norm_num
  | succ periods prior =>
    rw [← material_successor]
    change (materialAt periods).clock + max 0 (1 : ℚ) = _
    rw [prior, max_eq_right zero_le_one, Nat.cast_add, Nat.cast_one]
    exact add_assoc _ _ _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable
