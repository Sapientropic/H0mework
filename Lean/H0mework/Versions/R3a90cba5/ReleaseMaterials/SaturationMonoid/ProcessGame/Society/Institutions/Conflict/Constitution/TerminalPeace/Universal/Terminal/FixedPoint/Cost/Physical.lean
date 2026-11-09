import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Visit

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Material (OriginalNeedFloor actualUse originalRequirements)
open Reparation.Actual (StateAt)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

open private authorized_inventory_is_the_physical_inventory from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Native

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

local notation "Raw" => RawCurrent Party Good Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Item" => ExecutionItem Party Good Port Technology Instrument

/-- The charge is a physical use by the signer herself. No part of the
request can name a substitute bearer or declare an incoming credit. -/
def reviewRequest (payer : Party) (port : Port) (goods : Bundle Good) :
    Request Party Good Port Technology Instrument :=
  ⟨payer, [], port, [], .use payer goods .external⟩

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (raw : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)
  (payer : Party) (port : Port) (goods : Bundle Good)

abbrev chargedWord : Word := word ++ [reviewRequest payer port goods]

def reviewItem : Item :=
  ⟨word.length, (input.law.execute raw 0 word).final, reviewRequest payer port goods⟩

abbrev afterCharge : Raw := input.law.next raw (chargedWord word payer port goods)

theorem charged_items :
    input.law.rawItems raw (chargedWord word payer port goods) =
      input.law.rawItems raw word ++ [reviewItem input raw word payer port goods] := by
  simp only [RawLaw.rawItems, chargedWord, RawLaw.execute_append, RawLaw.execute, reviewItem,
    Nat.zero_add]

private theorem review_debit_at (who : Party) (good : Good) :
    flowAt (locate payer goods) who good = if who = payer then amount Good goods good else 0 := by
  induction goods with
  | nil => simp [locate, flowAt, amount]
  | cons lot rest earlier =>
    simp only [locate, List.map_cons, flowAt, amount, List.sum_cons] at earlier ⊢
    by_cases same : who = payer
    · subst who
      simp only [Prod.mk.injEq, true_and, if_true] at earlier ⊢
      rw [earlier]
    · have different : (payer, lot.1) ≠ (who, good) := fun eq => same (congrArg Prod.fst eq).symm
      simp only [if_neg same, if_neg different, earlier, zero_add]

variable {input raw word payer port goods}

theorem charged_actual_debit
    (legal : input.law.Valid (reviewItem input raw word payer port goods).before (reviewRequest payer port goods)) :
    input.law.actualDebit (reviewItem input raw word payer port goods).before
      (reviewItem input raw word payer port goods).request = locate payer goods ∧
    input.law.actualCredit (reviewItem input raw word payer port goods).before
      (reviewItem input raw word payer port goods).request = [] := by
  change input.law.actualDebit _ (reviewRequest payer port goods) = _ ∧
    input.law.actualCredit _ (reviewRequest payer port goods) = _
  rw [RawLaw.actualDebit, RawLaw.actualCredit, if_pos legal, if_pos legal]
  exact ⟨rfl, rfl⟩

theorem afterCharge_stock
    (legal : input.law.Valid (reviewItem input raw word payer port goods).before (reviewRequest payer port goods))
    (who : Party) (good : Good) :
    (afterCharge input raw word payer port goods).stock who good = (input.law.next raw word).stock who good -
      (if who = payer then amount Good goods good else 0) := by
  unfold afterCharge RawLaw.next chargedWord
  rw [RawLaw.execute_append]
  change (input.law.step (reviewItem input raw word payer port goods).before
    (reviewRequest payer port goods)).stock who good = _
  rw [RawLaw.step, if_pos legal]
  change (input.law.next raw word).stock who good - flowAt (locate payer goods) who good + 0 = _
  rw [add_zero, review_debit_at]
  rfl

theorem afterCharge_other_coordinates
    (legal : input.law.Valid (reviewItem input raw word payer port goods).before (reviewRequest payer port goods)) :
    let charged := afterCharge input raw word payer port goods
    let peaceful := input.law.next raw word
    charged.claims = peaceful.claims ∧ charged.technology = peaceful.technology ∧
      charged.clock = peaceful.clock ∧ charged.round = peaceful.round := by
  unfold afterCharge RawLaw.next chargedWord
  rw [RawLaw.execute_append]
  have paid : input.law.step (input.law.execute raw 0 word).final (reviewRequest payer port goods) =
      input.law.paidStep (input.law.execute raw 0 word).final (reviewRequest payer port goods) :=
    if_pos legal
  simp only [RawLaw.execute, paid]
  exact ⟨rfl, rfl, trivial, trivial⟩

theorem afterCharge_is_posted_deduction
    (legal : input.law.Valid (reviewItem input raw word payer port goods).before (reviewRequest payer port goods)) :
    afterCharge input raw word payer port goods = (input.law.next raw word).addReserve
      (fun who good => -(if who = payer then amount Good goods good else 0)) := by
  obtain ⟨claims, technology, clock, round⟩ := afterCharge_other_coordinates legal
  apply RawCurrent.ext
  · funext who good
    exact (afterCharge_stock legal who good).trans (sub_eq_add_neg _ _)
  · exact claims
  · exact technology
  · exact clock
  · exact round

theorem charged_amount_nonnegative
    (legal : input.law.Valid (reviewItem input raw word payer port goods).before (reviewRequest payer port goods))
    (good : Good) : 0 ≤ amount Good goods good := by
  have nonnegative : NonnegativeBundle (Party × Good) (locate payer goods) := legal.2.2.2.1
  have flow : 0 ≤ flowAt (locate payer goods) payer good := amount_nonnegative _ nonnegative _
  rwa [review_debit_at, if_pos rfl] at flow

theorem charged_use_unchanged (who : Party) (purpose : Use) (good : Good) (necessary : purpose ≠ .external) :
    actualUse input raw (chargedWord word payer port goods) who purpose good =
      actualUse input raw word who purpose good := by
  unfold actualUse
  rw [charged_items]
  simp [reviewItem, reviewRequest, Ne.symm necessary]

omit [DecidableEq Party] [DecidableEq Instrument] in
private theorem requirement_is_not_external {baseline : Raw} {people : List Party}
    {cell : Party × Use × Good × ℚ} (listed : cell ∈ originalRequirements input baseline people) :
    cell.2.1 ≠ .external := by
  obtain ⟨_, _, requirements⟩ := List.mem_flatMap.mp listed
  rcases List.mem_append.mp requirements with need | maintenance
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp need
    simp
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp maintenance
    simp

variable {origin : RawCurrent Party Good Technology Instrument} {people : List Party}

theorem charged_needs_are_exact (paid : Supply.Period input origin raw people word) :
    OriginalNeedFloor input origin raw people (chargedWord word payer port goods) ∧
    OriginalNeedFloor input raw raw people (chargedWord word payer port goods) := by
  constructor
  · intro cell listed
    rw [charged_use_unchanged cell.1 cell.2.1 cell.2.2.1 (requirement_is_not_external listed)]
    exact paid.originalFloor cell listed
  · intro cell listed
    rw [charged_use_unchanged cell.1 cell.2.1 cell.2.2.1 (requirement_is_not_external listed)]
    exact paid.currentFloor cell listed

/-- A charge has a separate disposition from the original living supply.
An external fee never stands in for a service action. -/
theorem charged_word_is_not_a_supply_period :
    ¬ Supply.Period input origin raw people (chargedWord word payer port goods) := by
  intro wouldBeSupply
  have listed : reviewItem input raw word payer port goods ∈
      input.law.rawItems raw (chargedWord word payer port goods) := by
    rw [charged_items]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have own := (wouldBeSupply.own _ listed).operation
  simp [reviewItem, reviewRequest, Supply.OwnOperation,
    Capitalism.Universal.Exit.AutonomousProduction.SelfOperation] at own

private theorem charged_authorization (paid : Supply.Period input origin raw people word)
    (legal : input.law.Valid (reviewItem input raw word payer port goods).before (reviewRequest payer port goods)) :
    ∀ item ∈ input.law.rawItems raw (chargedWord word payer port goods),
      input.law.Valid item.before item.request ∧ item.request.consents = [] := by
  intro item listed
  rw [charged_items] at listed
  rcases List.mem_append.mp listed with prior | final
  · exact ⟨(paid.own item prior).valid, (paid.own item prior).noConsent⟩
  · rw [List.mem_singleton.mp final]
    exact ⟨legal, rfl⟩

variable (before : Runtime.Native Party Good Port Technology Instrument)

theorem charged_native_write
    (paid : Supply.Period input origin before.raw people word)
    (legal : input.law.Valid (reviewItem input before.raw word payer port goods).before (reviewRequest payer port goods)) :
    let written := Physical.Public.compile input before (.execute (chargedWord word payer port goods))
    written.isAccepted = true ∧
      written.execution = input.law.execute before.raw 0 (chargedWord word payer port goods) ∧
      written.next = {before with raw := afterCharge input before.raw word payer port goods} := by
  let commands : Word := chargedWord word payer port goods
  have authorized := charged_authorization paid legal
  have literal : (commands.map fun request => request.resign request.signer) = commands := by
    conv => rhs; rw [← List.map_id commands]
    apply List.map_congr_left
    intro request listed
    have original : request ∈ (input.law.rawItems before.raw commands).map ExecutionItem.request := by
      rwa [RawLaw.rawItems, RawLaw.inventory_requests_exact]
    obtain ⟨item, present, same⟩ := List.mem_map.mp original
    rw [← same]
    exact Request.resign_self _ (authorized item present).2
  have selected : Physical.Public.wordAt before (.execute commands) = some commands := congrArg some literal
  have written := authorized_inventory_is_the_physical_inventory input before.raw commands 0
    (fun item listed => (authorized item listed).1)
  change let compiled := Physical.Public.compile input before (.execute commands)
    compiled.isAccepted = true ∧ compiled.execution = input.law.execute before.raw 0 commands ∧
      compiled.next = {before with raw := input.law.next before.raw commands}
  dsimp only
  cases Physical.Public.compile input before (.execute commands) with
  | accepted actual original _ =>
    rw [selected] at original
    cases Option.some.inj original
    refine ⟨rfl, written, ?_⟩
    change {before with raw := (Physical.Public.interpreter input).next before.raw commands} = _
    unfold RawLaw.next
    rw [written]
    rfl
  | refused actual original item listed failed =>
    rw [selected] at original
    cases Option.some.inj original
    change item ∈ ((Physical.Public.interpreter input).execute before.raw 0 commands).items at listed
    rw [written] at listed
    exact (failed (PublicFunction.valid_physical _ _ _ (authorized item listed).1)).elim
  | metadata empty =>
    rw [selected] at empty
    cases empty

variable {Community : Type} [DecidableEq Community]

theorem charged_items_have_no_damage (community : Party → Community)
    (paid : Supply.Period input origin raw people word)
    (legal : input.law.Valid (reviewItem input raw word payer port goods).before (reviewRequest payer port goods)) :
    ∀ item ∈ input.law.rawItems raw (chargedWord word payer port goods),
      ∀ address, Reparation.loss input.law community item address = 0 := by
  intro item listed address
  rw [charged_items] at listed
  rcases List.mem_append.mp listed with prior | final
  · exact (paid.own item prior).opens_no_coercive_loss community address
  · rw [List.mem_singleton.mp final]
    unfold Reparation.loss
    split
    · rename_i cross
      have distinct : address.1 ≠ payer := by
        intro same
        exact cross.1 (congrArg community (same.trans cross.2.1))
      have debit := (charged_actual_debit legal).1
      have credit := (charged_actual_debit legal).2
      rw [debit, credit, review_debit_at, if_neg distinct]
      simp [flowAt, amount]
    · rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint
