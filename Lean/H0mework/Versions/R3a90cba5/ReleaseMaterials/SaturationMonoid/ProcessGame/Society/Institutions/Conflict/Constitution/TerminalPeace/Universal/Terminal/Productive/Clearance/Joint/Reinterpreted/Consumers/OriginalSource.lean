import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Production
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Consumers.Frontier
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Consumers.OriginalRecipe
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Menu.Unbounded.Nonattainment.Balance

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Material
open Capitalism.Universal.Abolition.Material.Continuation
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable)
open Reparation.Actual (Occurrence)
open Quantities.Execution (endAt endAt_append primitiveScript the_first_exhausted_native_cut_is_the_original_paid_drain)
open Joint.OriginalExchange (at_original claim original_drain_exact)
open Conflict.Consumers.Evolving (compact sourceInput issue)
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual (source_parameters)
open private native_indices from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material.Shortage
open FixedPoint (reviseProgramme RevisionAnswers RevisionApproval)
open FixedPoint.OpenPeace.Operational (RepeatCode RecipeConditions)
open Supply.Consumers (refillWord)
open TerminalPeace.Supply (localTechnique personalWord)
open private accounting_portfolio from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Menu.Unbounded.Nonattainment.Balance

noncomputable section

abbrev loss := Original.occurrence
abbrev front : Original.Word := [none]
abbrev nativeAnswers := Occurrence.Unbounded.Nonattainment.answers

theorem original_native_cut : endAt Original.seed (anchor loss front) = Original.cut :=
  at_original

theorem original_native_inputs_pass :
    Occurrence.Eligible nativeAnswers loss front ∧ ReadyEntry loss front := by
  refine ⟨⟨⟨ExposureGuard.no_material_is_admitted _ _ _ _ Original.levy_native_has_no_second_item,
    Boundary.Actual.no_material_write_has_no_damage _ _ _ Original.levy_native_has_no_second_item⟩, trivial⟩, ?_⟩
  change Ready (endAt Original.seed (anchor loss front)) ∧ ReviewAvailable (endAt Original.seed (anchor loss front))
  rw [original_native_cut]
  exact ⟨Original.ready, Original.review⟩

theorem the_unsettled_original_cut_is_generated :
    ∃ before, enter loss nativeAnswers front = .ok before ∧ before.programme = compact ∧
      before.physical.raw = Original.snapshot 111 113 ∧ before.ledger.stack.balances = [(loss, Original.balance)] := by
  obtain ⟨before, actual, ledger, physical, programme⟩ :=
    enters_when_the_original_prefix_is_admitted loss nativeAnswers front
      original_native_inputs_pass.1 original_native_inputs_pass.2
  refine ⟨before, actual, programme.trans sourceInput, ?_, ?_⟩
  · rw [physical, original_native_cut]
    exact Original.cut_raw
  · rw [ledger]
    exact accounting_portfolio

private theorem original_need_cut : originalRaw loss = Original.snapshot 111 113 := by
  have exact := (the_first_exhausted_native_cut_is_the_original_paid_drain
    (endAt Original.seed (Occurrence.history loss))).2.1
  change (endAt (endAt Original.seed (Occurrence.history loss)) (openingDrain loss)).raw = originalRaw loss at exact
  rw [original_drain_exact, ← endAt_append, original_native_cut, Original.cut_raw] at exact
  exact exact.symm

theorem both_original_parties_have_standing (person : Bool) : person ∈ people loss front := by
  apply List.mem_dedup.mpr
  apply ExposureGuard.every_original_member_is_a_bearer
  let quote := Conflict.Consumers.Evolving.Original.source
  let history := anchor loss front
  have same : endAt quote (primitiveScript [issue] ++ history) = endAt Original.seed history := by
    rw [endAt_append]
    rfl
  have params := native_indices quote (primitiveScript [issue] ++ history)
  rw [same] at params
  have input := (Quantities.Execution.endAt_input Original.seed history).trans sourceInput
  apply Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.PublicCensus.every_old_member_keeps_current_standing
  rw [input, params.1, params.2.1, params.2.2.1, params.2.2.2.1, params.2.2.2.2,
    source_parameters.1, source_parameters.2.1, source_parameters.2.2.1,
    source_parameters.2.2.2.1, source_parameters.2.2.2.2]
  cases person <;> decide +kernel

/-- The new mill returns the original stock and adds a meal and two
units of the material that the old liability names. -/
def offer : ProductionOffer Bool Bool Bool Unit Unit :=
  ⟨fun technology person =>
    let prior := localTechnique technology person
    { prior with outputs := prior.outputs ++ [(false, 2)] }, refillWord, []⟩

def revised := reviseProgramme compact offer

def reviseReplies (victim : Bool) : RevisionAnswers Bool Bool Bool Unit Unit :=
  fun _ _ _ person => person || victim

def codeFor (input : ProgrammeSource.Input Bool Bool Bool Unit Unit) (same : input = revised)
    (raw : Original.Raw) : RepeatCode input raw where
  production := refillWord
  personal := personalWord
  timing := by rw [same]; exact ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  reserve := by rw [same]; exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  registration := by rw [same]; exact fun _ _ _ _ _ registered => registered
  duration := by rw [same]; exact fun _ _ _ _ => rfl

def repeatAt (before : Current loss front) (same : before.programme = compact) :
    RepeatCode (reviseProgramme before.programme offer) before.physical.raw :=
  codeFor _ (congrArg (fun input => reviseProgramme input offer) same) _

def passes (roster : List Bool) (word : RawEvent Bool Bool Bool Unit Unit) (raw : Original.Raw) : Bool :=
  match Supply.inspect revised (Original.snapshot 111 113) raw roster word with
  | .inl _ => false
  | .inr _ => true

private theorem paidAt (raw : Original.Raw) (roster : List Bool) (word : RawEvent Bool Bool Bool Unit Unit)
    (passed : passes roster word raw = true) : Supply.Period revised (originalRaw loss) raw roster word := by
  rw [original_need_cut]
  unfold passes at passed
  cases selected : Supply.inspect revised (Original.snapshot 111 113) raw roster word with
  | inl => rw [selected] at passed; cases passed
  | inr paid => exact paid.down

private theorem roundAt (raw : Original.Raw) (paid : Supply.Period revised (originalRaw loss) raw [false, true] refillWord) :
    Supply.Period revised (originalRaw loss) raw (people loss front) refillWord := by
  have all (need : Original.Raw) (floor : OriginalNeedFloor revised need raw [false, true] refillWord) :
      OriginalNeedFloor revised need raw (people loss front) refillWord := by
    intro cell present
    obtain ⟨p, _, entry⟩ := List.mem_flatMap.mp present
    exact floor cell (List.mem_flatMap.mpr ⟨p, by cases p <;> simp, entry⟩)
  refine ⟨?_, all _ paid.originalFloor, all _ paid.currentFloor, paid.positiveClock⟩
  intro item original
  have own := paid.own item original
  exact ⟨own.operation, both_original_parties_have_standing _, own.noConsent, own.valid⟩

theorem checksFor (input : ProgrammeSource.Input Bool Bool Bool Unit Unit) (same : input = revised)
    (raw : Original.Raw) (shared : passes [false, true] refillWord raw = true)
    (personal : ∀ person, passes [person] (personalWord person) raw = true)
    (balanced : Balance.FiniteChecks .accumulating revised.law raw refillWord)
    (grows : 0 < Balance.gain revised.law raw refillWord true false) :
    RecipeConditions input (originalRaw loss) raw (people loss front) (codeFor input same raw) := by
  subst input
  have registered : Supply.Registered revised raw refillWord :=
    FixedPoint.revision_registers_its_pilot compact offer _
  refine ⟨⟨registered, roundAt raw (paidAt raw [false, true] refillWord shared)⟩, ?_,
    balanced, ⟨true, false, grows⟩⟩
  intro person _
  refine ⟨?_, paidAt raw [person] (personalWord person) (personal person)⟩
  intro req listed
  change req ∈ personalWord person at listed
  apply registered
  cases person <;> simp [refillWord, personalWord] at listed ⊢ <;> grind

theorem the_new_trial_checks (before : Current loss front) (same : before.programme = compact)
    (raw : before.physical.raw = Original.snapshot 111 113) :
    RecipeConditions (reviseProgramme before.programme offer) (originalRaw loss) before.physical.raw (people loss front)
      (repeatAt before same) := by
  apply checksFor
  · rw [raw]
    decide +kernel
  · intro person
    rw [raw]
    cases person <;> decide +kernel
  · rw [raw]
    decide +kernel
  · rw [raw]
    decide +kernel

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer
