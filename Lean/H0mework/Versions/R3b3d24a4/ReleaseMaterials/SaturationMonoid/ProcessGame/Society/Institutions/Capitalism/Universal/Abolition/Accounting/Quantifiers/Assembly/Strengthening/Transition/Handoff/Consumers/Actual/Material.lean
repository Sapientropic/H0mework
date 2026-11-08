import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.PaidSource
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Routing

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Actual

open Source.Program Innovation PublicFunction Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Abolition.Accounting.Quantifiers Quantifiers.Joint
open Material.Continuation

noncomputable section

abbrev Raw := RawCurrent Bool Bool Unit Unit
abbrev Command := Request Bool Bool Bool Unit Unit
abbrev publicLaw := Physical.Public.interpreter input
abbrev checkInput := Public.Scope.checkInput input

def production : Command := ⟨true, [], false, [], .produce true⟩
def provision : Command := ⟨true, [], false, [], .transfer true false [(true, 1)]⟩
def life (person : Bool) : Command := ⟨person, [], false, [], .use person [(true, 1)] .necessity⟩
def service : Command := ⟨true, [], false, [], .use true [(false, 1)] .external⟩
def period : RawEvent Bool Bool Bool Unit Unit := [production, provision, life false, life true, service]

def proposal : Handoff.Proposal Bool Bool Bool Unit Unit := ⟨[], (period, period)⟩

def opening : Raw where
  stock := fun person good => if good then if person then 16 else 0 else if person then 109 else 117
  claims := fun _ _ _ => 0
  technology := ()
  clock := 4
  round := 4

abbrev firstRaw := publicLaw.next opening period
abbrev secondRaw := publicLaw.next firstRaw period

private theorem old_row_was_open : ¬ Current.productivePaid seed grossClaim shared := by
  intro paid
  have remaining := paid (false, false) original_positive_scope
  rw [productive_remaining] at remaining
  norm_num at remaining

private theorem live_law : actualLaw seed = publicLaw := rfl

local macro "read_paid_source" : tactic => `(tactic|
  simp only [Planning.primitiveItems, Planning.primitiveAnalysis, Planning.grossCredits,
    Planning.primitiveAfter, Planning.primitiveReadings, Planning.initialWork,
    Planning.Menu.plantPlan, Planning.Menu.materialPlan, Planning.Menu.productionPrefix,
    Planning.Menu.fundedNeeds, Planning.Menu.fundNeedsFrom, Planning.Menu.needsWord, Planning.Menu.needCells,
    Planning.Menu.bills, Planning.Menu.grossFrom, Planning.Menu.productiveFrom, Planning.Menu.dose,
    Planning.Menu.relevantGoods, Planning.Menu.required, Planning.Menu.recipeNet, Planning.Menu.command,
    Planning.Menu.settlements, Allocation.Kernel.after, Allocation.Kernel.net, Allocation.Kernel.productiveCredit,
    Allocation.Kernel.gross, Allocation.Kernel.reservation, Allocation.Kernel.incoming, Allocation.Kernel.grossCharged,
    Allocation.room, Allocation.first, live_law, shared_raw, productive_scope, gross_scope, productive_remaining,
    gross_remaining, productive_declared, gross_declared, live_roster, original_financial_tail, cohort,
    old_row_was_open, false_and, if_false, List.foldl_cons, List.foldl_nil])

theorem source_reads_the_paid_opening : source.raw = opening := by
  rw [source_is_the_original_paid_material_cut]
  unfold oldPayment
  read_paid_source
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;> decide +kernel
  · funext instrument debtor creditor
    cases instrument
    cases debtor <;> cases creditor <;> decide +kernel
  · exact Subsingleton.elim _ _
  · decide +kernel
  · decide +kernel

private theorem all_parties (person : Bool) : person ∈ [false, true] := by
  cases person <;> simp

private theorem original_floor_for_census (raw origin : Raw) (members : List Bool)
    (paid : Material.OriginalNeedFloor checkInput opening raw [false, true] period) :
    Material.OriginalNeedFloor checkInput origin raw members period := by
  intro cell listed
  obtain ⟨person, _, due⟩ := List.mem_flatMap.mp listed
  exact paid cell (List.mem_flatMap.mpr ⟨person, all_parties person, due⟩)

private theorem all_finite_checks (raw : Raw) (cut : raw = opening ∨ raw = firstRaw) :
    Material.ActualAndIndependent checkInput raw period ∧
    Exit.Necessity.AllNeedsPaid publicLaw raw [false, true] period ∧
    Material.OriginalNeedFloor checkInput opening raw [false, true] period ∧
    Balance.FiniteChecks .accumulating publicLaw raw period := by
  rcases cut with rfl | rfl <;> exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

private theorem period_checks (raw : Raw) (members : List Bool) (cut : raw = opening ∨ raw = firstRaw) :
    Material.PeriodChecks checkInput raw members period := by
  have checked := all_finite_checks raw cut
  refine ⟨checked.1, fun person _ => checked.2.1 person (all_parties person),
    Material.Migration.finiteShared_noFreshControl checkInput raw period (fun _ _ _ _ _ _ => rfl),
    ?_, trivial⟩
  intro person _
  have same : (publicLaw.next raw period).technology = raw.technology := Subsingleton.elim _ _
  change Material.TechniqueDominates (publicLaw.technique raw.technology person)
    (publicLaw.technique (publicLaw.next raw period).technology person)
  rw [same]
  exact ⟨fun _ _ => le_rfl, fun _ _ => le_rfl, fun _ _ => le_rfl⟩

theorem original_guard (origin raw : Raw) (members : List Bool) (cut : raw = opening ∨ raw = firstRaw) :
    Abolition.Review.Guarded.Checks checkInput origin raw members period :=
  ⟨Balance.checked_word_is_nonfinancial .accumulating publicLaw raw period (all_finite_checks raw cut).2.2.2,
    original_floor_for_census raw origin members (all_finite_checks raw cut).2.2.1,
    period_checks raw members cut⟩

theorem original_migration_checks (origin : Raw) (members : List Bool) :
    Abolition.Root.Actual.Migration.Checks checkInput origin opening members proposal.pair := by
  have front := original_guard origin opening members (Or.inl rfl)
  have back := original_guard origin firstRaw members (Or.inr rfl)
  refine ⟨⟨fun item actual => (front.2.2.1 item actual).1, front.2.2.2.1, front.2.1⟩,
    front.2.2.1, front.2.2.2.2.2.1, ?_⟩
  exact ⟨back.2.2, back.2.1, (all_finite_checks firstRaw (Or.inr rfl)).2.2.2,
    Or.inr (fun _ _ _ _ _ _ => rfl)⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Actual
