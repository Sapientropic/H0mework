import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.Opening
import H0mework.Versions.R71cb159f.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.Consumers.OriginalInventory
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Consumers.OriginalRecipe
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Consumers.Frontier

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.OriginalConsumer

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Material
open Capitalism.Universal.Abolition.Material.Continuation
open Conflict.Consumers.Evolving (compact sourceInput)
open Clearance Joint Joint.OriginalExchange Joint.SourceReserve
open TerminalPeace.Supply (personalWord)
open Supply.Consumers (refillWord)
open Reparation.Actual (Occurrence)

noncomputable section

def menu (victimApproves : Bool) : ProductionMenu Bool Bool Bool Unit Unit :=
  ⟨[OriginalRecipe.offer], fun _ _ person => person || victimApproves⟩

abbrev picked (victimApproves : Bool) : ProductionChoice (menu victimApproves) :=
  some ⟨0, Nat.zero_lt_one⟩

def quiet : Replies Bool Bool Bool Unit Unit :=
  ⟨fun _ _ _ _ => false, fun _ _ _ _ => false⟩

def addresses : List (Bool × Bool) := [(false, false), (false, true), (true, false), (true, true)]

theorem covers (address : Bool × Bool) : address ∈ addresses := by
  rcases address with ⟨person, good⟩
  cases person <;> cases good <;> decide

private theorem read_both (word : Original.Word) (person : Bool) :
    person ∈ productionRoster Original.seed loss word (picked true) :=
  production_roster_keeps_original_bearers Original.seed loss word _ (OriginalService.each_original_bearer_remains_listed loss person)

private theorem sign (word : Original.Word) : ProductionApproved Original.seed loss word (picked true) :=
  fun person _ => by cases person <;> rfl

private theorem refuse (word : Original.Word) : ¬ ProductionApproved Original.seed loss word (picked false) := by
  intro approved
  have denied := approved false (production_roster_keeps_original_bearers Original.seed loss word _
    (OriginalService.each_original_bearer_remains_listed loss false))
  exact Bool.false_ne_true denied

private theorem live_recipe (vote : Bool) (word : Original.Word) (ready : ReadyEntry loss word)
    (approved : ProductionApproved Original.seed loss word (picked vote)) :
    productionInput Original.seed loss word (picked vote) = OriginalRecipe.programme := by
  rw [production_at_an_authorized_cut _ _ _ _ ready approved, sourceInput]
  rfl

private theorem possible_programme (vote : Bool) (word : Original.Word) :
    productionInput Original.seed loss word (picked vote) = OriginalRecipe.programme ∨
      productionInput Original.seed loss word (picked vote) = compact := by
  classical
  by_cases available : ReadyEntry loss word ∧ ProductionApproved Original.seed loss word (picked vote)
  · exact Or.inl (live_recipe vote word available.1 available.2)
  · exact Or.inr ((production_without_authority_reads_the_old_programme _ _ _ _ available).trans sourceInput)

def codeAt (vote : Bool) (word : Original.Word) :
    RepeatCode (productionInput Original.seed loss word (picked vote)) (prefixRaw loss word) where
  production := refillWord
  personal := personalWord
  timing := by
    rcases possible_programme vote word with same | same <;> rw [same] <;>
      exact ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  reserve := by
    rcases possible_programme vote word with same | same <;> rw [same] <;>
      exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  registration := by
    rcases possible_programme vote word with same | same <;> rw [same] <;>
      exact fun _ _ _ _ _ registered => registered
  duration := by
    rcases possible_programme vote word with same | same <;> rw [same] <;>
      exact fun _ _ _ _ => rfl

private theorem starts (word : Original.Word) :
    ProductionStartsWith (picked true) (codeAt true word).production :=
  ⟨rfl, TerminalPeace.Supply.grow false, List.mem_cons_self, false, rfl⟩

private theorem period_at (roster : List Bool) (contains : ∀ p : Bool, p ∈ roster) :
    Supply.Period OriginalRecipe.programme (originalRaw loss) (prefixRaw loss paidPrefix) roster refillWord := by
  have checked := OriginalRecipe.paidAt (originalRaw loss) (prefixRaw loss paidPrefix) [false, true] refillWord
    (by rw [paid_raw]; decide +kernel)
  have floor (need : Original.Raw) (paid : OriginalNeedFloor OriginalRecipe.programme need
      (prefixRaw loss paidPrefix) [false, true] refillWord) :
      OriginalNeedFloor OriginalRecipe.programme need (prefixRaw loss paidPrefix) roster refillWord := by
    intro cell present
    obtain ⟨person, _, entry⟩ := List.mem_flatMap.mp present
    exact paid cell (List.mem_flatMap.mpr ⟨person, by cases person <;> simp, entry⟩)
  refine ⟨?_, floor _ checked.originalFloor, floor _ checked.currentFloor, checked.positiveClock⟩
  intro item present
  have owned := checked.own item present
  exact ⟨owned.operation, contains _, owned.noConsent, owned.valid⟩

private theorem no_recipe_issue (roster : List Bool) (contains : ∀ p : Bool, p ∈ roster)
    (code : RepeatCode OriginalRecipe.programme (prefixRaw loss paidPrefix))
    (production : code.production = refillWord) (personal : code.personal = personalWord)
    (issue : RecipeIssue OriginalRecipe.programme (originalRaw loss) (prefixRaw loss paidPrefix) roster code) :
    False := by
  have register : Supply.Registered OriginalRecipe.programme (prefixRaw loss paidPrefix) refillWord :=
    revision_registers_its_pilot _ _ _
  cases issue with
  | production error =>
    cases error with
    | unregistered request listed absent => exact absent (register request (production ▸ listed))
    | unpaid error => exact error.refutes _ _ _ _ _ (production.symm ▸ period_at roster contains)
  | personal error =>
    obtain ⟨person, _, error⟩ := error
    cases error with
    | unregistered request listed absent =>
      apply absent
      apply register
      have item : request ∈ personalWord person := congrArg (fun word => request ∈ word person) personal ▸ listed
      cases person <;> simp [refillWord, personalWord] at item ⊢ <;> grind
    | unpaid error =>
      apply error.refutes _ _ _ _ _
      rw [personal]
      apply OriginalRecipe.paidAt
      rw [paid_raw]
      cases person <;> decide +kernel
  | imbalance error =>
    apply error.refutes _ _ _ _
    rw [production, paid_raw]
    decide +kernel
  | stalled error =>
    have grows : 0 < Balance.gain OriginalRecipe.programme.law (prefixRaw loss paidPrefix) refillWord false true := by
      rw [paid_raw]
      decide +kernel
    exact (not_lt_of_ge (production ▸ error false true)) grows

def checkedOpening (vote : Bool) :
    OpeningResult loss replies [grow] quiet (menu vote) :=
  compileWithMenu loss replies [grow] quiet (menu vote) addresses covers (fun _ => picked vote) (codeAt vote)

private theorem accepted_recipe_has_no_failure (word : Original.Word) (same : word = paidPrefix)
    (ready : ReadyEntry loss word)
    (issue : RecipeIssue (productionInput Original.seed loss word (picked true)) (originalRaw loss)
      (prefixRaw loss word) (productionRoster Original.seed loss word (picked true)) (codeAt true word)) :
    False := by
  subst word
  have transfer (input : ProgrammeSource.Input Bool Bool Bool Unit Unit) (installed : input = OriginalRecipe.programme)
      (code : RepeatCode input (prefixRaw loss paidPrefix))
      (failed : RecipeIssue input (originalRaw loss) (prefixRaw loss paidPrefix)
        (productionRoster Original.seed loss paidPrefix (picked true)) code) :
      code.production = refillWord → code.personal = personalWord → False := by
    subst input
    intro exactWord personal
    exact no_recipe_issue _ (read_both paidPrefix) code exactWord personal failed
  exact transfer _ (live_recipe true paidPrefix ready (sign paidPrefix)) _ issue rfl rfl

private def Expected (vote : Bool) (result : OpeningResult loss replies [grow] quiet (menu vote)) : Prop :=
  match result with
  | .opened opening => vote = true ∧ opening.word = paidPrefix ∧
      opening.entry.current.programme = OriginalRecipe.programme ∧ opening.entry.recipe.move.word = refillWord
  | .unapproved landed _ _ => vote = false ∧ landed.word = paidPrefix ∧ WholeCleared loss replies landed.word
  | _ => False

set_option maxHeartbeats 1100000 in
private theorem selected_is_the_original_paid_opening (vote : Bool) : Expected vote (checkedOpening vote) := by
  have nonempty : [grow] ≠ [] := List.cons_ne_nil _ _
  unfold checkedOpening compileWithMenu
  simp only [dif_neg nonempty, dif_pos credit_first]
  cases inspectInputs replies start start (openingDrain loss) (community := Original.community) with
  | inl failed =>
    have valid : Occurrence.EligibleFrom Original.community replies start start (openingDrain loss) :=
      original_drain_exact.symm ▸ drain_safe true
    exact (failed.refutes replies start valid).elim
  | inr safe =>
    obtain ⟨begun, landed, closed, production, paid, same⟩ := the_native_portfolio_pays_six safe.down nonempty
    simp only [production, paid]
    cases inspectSourceStock loss addresses covers landed.word with
    | inl failed =>
      have keeps : ProtectsNeeds loss landed.word :=
        same.symm ▸ all_paid_positions_keep_needs paidPrefix List.prefix_rfl
      exact (failed.refutes loss keeps).elim
    | inr stocked =>
      cases vote with
      | false =>
        simp only [Id.run, dif_neg (refuse landed.word)]
        exact ⟨rfl, same, a_completed_portfolio_clears_every_original_row loss replies landed closed⟩
      | true =>
        simp only [Id.run, dif_pos (sign landed.word), dif_pos (starts landed.word)]
        cases checkRecipe (productionInput Original.seed loss landed.word (picked true)) (originalRaw loss)
            (prefixRaw loss landed.word) (productionRoster Original.seed loss landed.word (picked true))
            (codeAt true landed.word) with
        | inl failed => exact (accepted_recipe_has_no_failure landed.word same landed.ready failed).elim
        | inr recipe => exact ⟨rfl, same, live_recipe true _ landed.ready (sign _), recipe.property⟩

set_option maxHeartbeats 1000000 in
/-- The original six-unit address is fully paid before the checked recipe
generates the first actual living round on its own resident. -/
theorem the_original_six_are_paid_before_the_actual_peace_round :
    ∃ opening, checkedOpening true = .opened opening ∧ opening.word = paidPrefix ∧
      let before := opening.entry.current
      let round := dispatch quiet before .renew
      round.visit.read.commands = refillWord ∧ round.visit.read.effect.isAccepted = true ∧
      round.next.ledger = (Installation.Live.publish before.ledger round.visit.read true).state ∧
      round.next.ledger.stack.balances.map Prod.fst = [loss] ∧
      (∀ row ∈ round.next.ledger.stack.balances, row.2.remaining = 0) ∧
      (∀ person : Bool, ∃ word,
        Supply.Registered round.visit.read.programme before.physical.raw word ∧
        Supply.Period round.visit.read.programme (originalRaw loss) before.physical.raw [person] word) ∧
      (∀ policy start bound, ∃ n ≥ start, bound < (history quiet before policy n).physical.raw.clock) := by
  have exactResult := selected_is_the_original_paid_opening true
  cases selected : checkedOpening true with
  | opened opening =>
    rw [selected] at exactResult
    obtain ⟨_, same, _, commands⟩ := exactResult
    let before := opening.entry.current
    let round := dispatch quiet before .renew
    have command : round.visit.read.commands = refillWord :=
      (productiveRound_reads_selected_production before .renew .renewed before.programme before.recipe).2.2.2.trans
        ((before.recipe.moveAt_word before.physical.raw before.reserved).trans commands)
    refine ⟨opening, rfl, same, command, round.realWrite, round.ledgerNext, ?_, ?_, ?_, opening.fixed.cofinal⟩
    · rw [round.rows, opening.entry.every_old_address_is_retained]
      change ((Reparation.Actual.run Original.seed Original.community Original.born).stack.balances.map Prod.fst) = _
      rw [Original.at_its_birth_the_whole_ledger_opens_six]
      rfl
    · rw [round.rows]
      exact opening.fixed.oldPaid
    · intro person
      exact round.exit person (production_roster_keeps_original_bearers _ _ _ _
        (OriginalService.each_original_bearer_remains_listed loss person))
  | unapproved _ _ _ =>
    rw [selected] at exactResult
    cases exactResult.1
  | _ => rw [selected] at exactResult; exact exactResult.elim

/-- A declined production change leaves the same real compensation in
place and creates no revised peaceful opening. -/
theorem the_original_victim_can_refuse_the_new_recipe_after_receipt :
    ∃ landed choice refused,
      checkedOpening false = .unapproved landed choice refused ∧ landed.word = paidPrefix ∧
      WholeCleared loss replies landed.word ∧ Occurrence.Unbounded.ActualWrite replies loss landed.word := by
  have exactResult := selected_is_the_original_paid_opening false
  cases selected : checkedOpening false with
  | unapproved landed choice refused =>
    rw [selected] at exactResult
    exact ⟨landed, choice, refused, rfl, exactResult.2.1, exactResult.2.2,
      Occurrence.Unbounded.an_eligible_word_has_its_actual_whole_write replies loss _ landed.safe⟩
  | opened _ =>
    rw [selected] at exactResult
    exact (Bool.false_ne_true exactResult.1).elim
  | _ => rw [selected] at exactResult; exact exactResult.elim

#print axioms the_original_six_are_paid_before_the_actual_peace_round
#print axioms the_original_victim_can_refuse_the_new_recipe_after_receipt

end

run_cmd Lean.modifyEnv fun env =>
  let names := ["the_original_six_are_paid_before_the_actual_peace_round",
    "the_original_victim_can_refuse_the_new_recipe_after_receipt"]
  names.foldl (fun env name => Lean.LibrarySuggestions.nameDenyListExt.addEntry env name) env

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.OriginalConsumer
