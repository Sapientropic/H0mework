import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Cycle
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Consumers.Stocked
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material.Shortage

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.OriginalService

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Material (OriginalNeedFloor actualUse)
open Capitalism.Universal.Abolition.Root.Registered
open TerminalPeace.Supply (Stocked revisedInput physical)
open Supply.Consumers (the_original_ordered_period_is_paid the_original_personal_period_is_paid)
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt endAt_append endAt_input primitiveScript)
open Conflict.Consumers.Evolving (W issue compact sourceInput)
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual (source_parameters)
open Runtime.Viability (Move Path RetimeStableAt)
open private native_indices from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material.Shortage

open private authorized_inventory_is_the_physical_inventory from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Native

noncomputable section

def proposal : ProductionOffer Bool Bool Bool Unit Unit :=
  ⟨TerminalPeace.Supply.localTechnique, TerminalPeace.Supply.renewalWord, []⟩

/-- Each reply is read on its own lane at the identified ledger visit. -/
def menuAt (history : Original.Word) (answers : Bool → Bool) :
    ProductionMenu Bool Bool Bool Unit Unit := by
  classical
  exact ⟨[proposal], fun past _ person => if past = history then answers person else false⟩

def choiceAt (history : Original.Word) (answers : Bool → Bool) :
    ProductionChoice (menuAt history answers) :=
  some ⟨0, Nat.zero_lt_one⟩

private def production : ProgrammeSource.Input Bool Bool Bool Unit Unit :=
  { compact with
    law := { compact.law with technique := TerminalPeace.Supply.localTechnique }
    localAttempts := fun raw => compact.localAttempts raw ++ (TerminalPeace.Supply.renewalWord ++ []) }

private theorem same_programme
    (loss : Reparation.Actual.Occurrence Original.seed Original.community)
    (word : Original.Word) (replies : Bool → Bool) (ready : ReadyEntry loss word)
    (approved : ProductionApproved Original.seed loss word (choiceAt (Occurrence.history loss ++ word) replies)) :
    productionInput Original.seed loss word (choiceAt (Occurrence.history loss ++ word) replies) = production := by
  unfold choiceAt at approved ⊢
  rw [production_at_an_authorized_cut _ _ _ _ ready approved, sourceInput]
  rfl

theorem each_original_bearer_remains_listed (loss : Reparation.Actual.Occurrence Original.seed Original.community)
    (bearer : Bool) : bearer ∈ originalBearers loss := by
  apply ExposureGuard.every_original_member_is_a_bearer
  let quote := Conflict.Consumers.Evolving.Original.source
  let history := Occurrence.history loss
  have exactCut : endAt quote (primitiveScript [issue] ++ history) = endAt Original.seed history := by
    rw [endAt_append]
    rfl
  have params := native_indices quote (primitiveScript [issue] ++ history)
  rw [exactCut] at params
  have input := (endAt_input Original.seed history).trans sourceInput
  apply Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.PublicCensus.every_old_member_keeps_current_standing
  rw [input, params.1, params.2.1, params.2.2.1, params.2.2.2.1, params.2.2.2.2,
    source_parameters.1, source_parameters.2.1, source_parameters.2.2.1,
    source_parameters.2.2.2.1, source_parameters.2.2.2.2]
  cases bearer <;> decide +kernel

theorem approval_reads_both_independent_replies
    (loss : Reparation.Actual.Occurrence Original.seed Original.community)
    (word : Original.Word) (answers : Bool → Bool) :
    ProductionApproved Original.seed loss word (choiceAt (Occurrence.history loss ++ word) answers) ↔
      ∀ person, answers person = true := by
  classical
  let past := Occurrence.history loss ++ word
  let choice := choiceAt past answers
  change (∀ person ∈ productionRoster Original.seed loss word choice,
    (if past = past then answers person else false) = true) ↔ _
  constructor
  · intro checked person
    have accepted := checked person (production_roster_keeps_original_bearers Original.seed loss word choice
      (each_original_bearer_remains_listed loss person))
    simpa using accepted
  · intro signed person _
    simpa using signed person

private theorem registered (raw : Original.Raw) (word : W)
    (offered : ∀ request ∈ word, request ∈ TerminalPeace.Supply.renewalWord) :
    Supply.Registered production raw word := by
  intro request listed
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ (offered request listed)))

private theorem valid_under_original_policy {raw : Original.Raw} {request : Conflict.Consumers.Evolving.R}
    (lawful : revisedInput.law.Valid raw request) : production.law.Valid raw request :=
  ⟨⟨lawful.1.1, rfl⟩, lawful.2⟩

private theorem production_execution {origin raw : Original.Raw} {people : List Bool} {word : W}
    (paid : Supply.Period revisedInput origin raw people word) :
    production.law.execute raw 0 word = physical.execute raw 0 word := by
  have same := authorized_inventory_is_the_physical_inventory revisedInput raw word 0
    (fun item listed => (paid.own item listed).valid)
  have actual (item : Original.Item) (listed : item ∈ (physical.execute raw 0 word).items) :
      revisedInput.law.Valid item.before item.request := by
    apply (paid.own item ?_).valid
    change item ∈ (revisedInput.law.execute raw 0 word).items
    rwa [← same]
  exact PublicFunction.execute_physical_of_authorized production.law raw 0 word
    (fun item listed => PublicFunction.valid_physical revisedInput.law _ _ (actual item listed))
    (fun item listed => valid_under_original_policy (actual item listed))

private theorem the_paid_recipe_keeps_original_policy {origin raw : Original.Raw} {people admitted : List Bool} {word : W}
    (samePeople : ∀ person, person ∈ people ↔ person ∈ admitted)
    (paid : Supply.Period revisedInput origin raw admitted word) :
    Supply.Period production origin raw people word := by
  have same := authorized_inventory_is_the_physical_inventory revisedInput raw word 0
    (fun item listed => (paid.own item listed).valid)
  have inventory : production.law.rawItems raw word = revisedInput.law.rawItems raw word :=
    congrArg ExecutionResult.items ((production_execution paid).trans same)
  have uses (person : Bool) (purpose : Use) (good : Bool) :
      actualUse production raw word person purpose good =
        actualUse revisedInput raw word person purpose good := by
    unfold actualUse
    rw [inventory]
    apply congrArg List.sum
    apply List.map_congr_left
    intro item listed
    have valid := (paid.own item listed).valid
    have inherited := valid_under_original_policy valid
    simp only [RawLaw.actualDebit, if_pos inherited, if_pos valid]
    rfl
  have floor (atCut : Original.Raw) (check : OriginalNeedFloor revisedInput atCut raw admitted word) :
      OriginalNeedFloor production atCut raw people word := by
    intro cell listed
    obtain ⟨person, member, due⟩ := List.mem_flatMap.mp listed
    rw [uses]
    exact check cell (List.mem_flatMap.mpr ⟨person, (samePeople person).mp member, due⟩)
  refine ⟨?_, floor origin paid.originalFloor, floor raw paid.currentFloor, paid.positiveClock⟩
  intro item listed
  rw [inventory] at listed
  have own := paid.own item listed
  exact ⟨own.operation, (samePeople _).mpr own.member, own.noConsent, valid_under_original_policy own.valid⟩

private def firstMove (origin raw : Original.Raw) (people : List Bool) (covers : ∀ person, person ∈ people)
    (funded : Stocked raw) : Move production origin people raw where
  word := TerminalPeace.Supply.renewalWord
  registered := registered _ _ (fun _ listed => listed)
  paid := the_paid_recipe_keeps_original_policy (fun person => ⟨fun _ => by cases person <;> decide,
    fun _ => covers person⟩) (the_original_ordered_period_is_paid origin raw funded false)
  personal := by
    intro person _
    refine ⟨TerminalPeace.Supply.personalWord person, registered _ _ ?_,
      the_paid_recipe_keeps_original_policy (fun _ => Iff.rfl)
        (the_original_personal_period_is_paid origin raw person (funded person).1 (funded person).2)⟩
    intro request listed
    cases person
    · exact List.mem_append_left _ listed
    · exact List.mem_append_right _ listed

private theorem whole_pilot_returns_its_material_and_advances
    (origin raw : Original.Raw) (people : List Bool) (covers : ∀ person, person ∈ people) (funded : Stocked raw) :
    (firstMove origin raw people covers funded).next = raw.retime (raw.clock + 1) (raw.round + 1) := by
  change production.law.next raw TerminalPeace.Supply.renewalWord = _
  unfold RawLaw.next
  have paid : Supply.Period revisedInput origin raw [false, true] TerminalPeace.Supply.renewalWord :=
    the_original_ordered_period_is_paid origin raw funded false
  rw [production_execution paid, TerminalPeace.Supply.the_renewal_inventory_is_exact raw funded]
  change { raw with clock := raw.clock + max 0 1, round := raw.round + 1 } = _
  rw [max_eq_right zero_le_one]
  rfl

private theorem timing : production.law.TimeIndependent :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

private theorem retimeStable (raw : Original.Raw) : RetimeStableAt production raw :=
  ⟨fun _ _ => rfl, fun _ _ _ registered => registered⟩

/-- The funded experiment is one actual material cycle. Its costs are
paid again on each copy, after the previous original successor. -/
theorem the_original_carriers_fund_the_pilot
    (loss : Reparation.Actual.Occurrence Original.seed Original.community)
    (word : Original.Word) (replies : Bool → Bool) (raw : Original.Raw)
    (funded : Stocked raw) (ready : ReadyEntry loss word)
    (approved : ProductionApproved Original.seed loss word (choiceAt (Occurrence.history loss ++ word) replies)) :
    let choice := choiceAt (Occurrence.history loss ++ word) replies
    let people := productionRoster Original.seed loss word choice
    ∃ pilot : Move (productionInput Original.seed loss word choice) (originalRaw loss) people raw,
      ProductionStartsWith choice pilot.word ∧
      Runtime.Viability.Live (productionInput Original.seed loss word choice) (originalRaw loss) people pilot.next := by
  let choice := choiceAt (Occurrence.history loss ++ word) replies
  let people := productionRoster Original.seed loss word choice
  dsimp only
  rw [same_programme _ _ _ ready approved]
  have covers (person : Bool) : person ∈ people :=
    production_roster_keeps_original_bearers Original.seed loss word choice
      (each_original_bearer_remains_listed loss person)
  let pilot := firstMove (originalRaw loss) raw people covers funded
  let cycle : Path production (originalRaw loss) people raw 1 pilot.next :=
    .cons pilot (.nil _)
  have exactNext := whole_pilot_returns_its_material_and_advances (originalRaw loss) raw people covers funded
  refine ⟨pilot, ⟨rfl, TerminalPeace.Supply.grow false, List.mem_cons_self, false, rfl⟩,
    cycle.cycle_restarts timing (cycle.retimeStable_of_source retimeStable) (by decide) ?_⟩
  have clock := congrArg (fun current : Original.Raw => current.clock) exactNext
  have round := congrArg (fun current : Original.Raw => current.round) exactNext
  rw [clock, round]
  exact exactNext

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.OriginalService
