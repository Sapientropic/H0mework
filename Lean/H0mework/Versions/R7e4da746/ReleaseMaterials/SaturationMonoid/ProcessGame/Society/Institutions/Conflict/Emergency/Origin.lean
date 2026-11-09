import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Enforcement

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port (State Party Technology) Instrument
local notation "Raw" => RawCurrent Party Good (State Party Technology) Instrument
local notation "Word" => RawEvent Party Good Port (State Party Technology) Instrument
local notation "Item" => ExecutionItem Party Good Port (State Party Technology) Instrument
local notation "Base" => RawLaw Party Good Port Technology Instrument
local notation "J" => Scope (Party := Party) (Good := Good) (Port := Port)
local notation "Script" => List (Option (Compile.RawInput Party Good Port (State Party Technology) Instrument))

def OriginalAuthority (source : C) (history : Script) : Prop :=
  ∀ item ∈ Quantities.Execution.inventory source history,
    source.native.input.law.Valid item.before item.request

inductive AuthorityDecision (source : C) (history : Script)
  | authorized (authority : OriginalAuthority source history)
  | refused (item : Item) (original : item ∈ Quantities.Execution.inventory source history)
      (unlicensed : ¬ source.native.input.law.Valid item.before item.request)

/-- The source retains a physical item even when its installed authority
refuses that item. -/
def inspectAuthority (source : C) (history : Script) : AuthorityDecision source history :=
  match Capitalism.Universal.Abolition.Material.inspectList
      (fun item : Item => source.native.input.law.Valid item.before item.request)
      (Quantities.Execution.inventory source history) with
  | .clear all => .authorized all
  | .failure item original unlicensed => .refused item original unlicensed

theorem originalAuthority_of_paid_word {source : C} {word : Word} (paid : Root.Paid source word) :
    OriginalAuthority source (Quantities.Execution.primitiveScript word) := by
  intro item listed
  rw [Quantities.Execution.primitive_inventory paid.trace 0] at listed
  obtain ⟨original, inside, rfl⟩ := List.mem_map.mp listed
  exact paid.authorized original inside

theorem OriginalAuthority.append {source : C} {past suffix : Script}
    (first : OriginalAuthority source past)
    (later : OriginalAuthority (Quantities.Execution.endAt source past) suffix) :
    OriginalAuthority source (past ++ suffix) := by
  intro item listed
  rw [Quantities.Execution.inventory_append] at listed
  rcases List.mem_append.mp listed with inPast | inSuffix
  · exact first item inPast
  · have same := Quantities.Execution.endAt_input source past
    have paid := later item inSuffix
    change (Quantities.Execution.endAt source past).native.input.law.Valid item.before item.request at paid
    rwa [same] at paid

variable [DecidableEq Technology]

theorem authorized_word_keeps_technology (base : Base) (scope : J) (start : Raw)
    (index : Nat) (word : Word)
    (authorized : ∀ item ∈ ((law base scope).execute start index word).items,
      (law base scope).Valid item.before item.request) :
    ((law base scope).execute start index word).final.technology.technology = start.technology.technology ∧
      ∀ item ∈ ((law base scope).execute start index word).items,
        item.before.technology.technology = start.technology.technology := by
  induction word generalizing start index with
  | nil => exact ⟨rfl, fun _ missing => (List.not_mem_nil missing).elim⟩
  | cons req rest ih =>
    let live := law base scope
    have accepted := authorized ⟨index, start, req⟩ List.mem_cons_self
    have step : (live.step start req).technology.technology = start.technology.technology := by
      rw [RawLaw.step, if_pos accepted]
      cases operation : req.operation
      case revise operator target =>
        have policy := accepted.1.2
        cases mark : target.last with
        | none => simp [law, RawLaw.operationAllowed, RawPolicy.eval, operation, mark] at policy
        | some command =>
          simp only [law, RawLaw.operationAllowed, RawPolicy.eval, operation, mark, decide_eq_true_eq] at policy
          rw [RawLaw.paidStep, operation, policy.2.2.2.2.1]
          cases command <;> simp only [advance]
          split <;> rfl
      all_goals simp only [RawLaw.paidStep, operation]
    obtain ⟨final, all⟩ := ih (live.step start req) (index + 1)
      (fun item member => authorized item (List.mem_cons_of_mem _ member))
    refine ⟨final.trans step, ?_⟩
    intro item listed
    rcases List.mem_cons.mp listed with head | later
    · subst item
      rfl
    · exact (all item later).trans step

private theorem physical_fold_keeps_technology
    (input : Capitalism.Universal.Root.ProgrammeSource.Input Party Good Port (State Party Technology) Instrument)
    (base : Base) (scope : J) (lawExact : input.law = law base scope)
    (start : Actual.Current (Party := Party) (Good := Good) (Port := Port)
      (Technology := State Party Technology) (Instrument := Instrument))
    (code : List (Compile.RawInput Party Good Port (State Party Technology) Instrument))
    (authorized : ∀ item ∈ Optimality.Programme.items input start code, input.law.Valid item.before item.request) :
    (Optimality.Programme.run input start code).raw.technology.technology = start.raw.technology.technology := by
  induction code generalizing start with
  | nil => rfl
  | cons proposal tail ih =>
    let result := Physical.Public.compile input start proposal
    have first : ∀ item ∈ result.execution.items, input.law.Valid item.before item.request :=
      fun item listed => authorized item (List.mem_append_left _ listed)
    have later := ih result.next (fun item listed => authorized item (List.mem_append_right _ listed))
    refine later.trans ?_
    cases exactResult : result with
    | refused => rfl
    | metadata => rfl
    | accepted word selected physical =>
      rw [exactResult] at first
      have same : (law base scope).execute start.raw 0 word =
          (Physical.Public.interpreter input).execute start.raw 0 word := by
        rw [← lawExact]
        exact PublicFunction.execute_physical_of_authorized input.law start.raw 0 word physical first
      have kept := (authorized_word_keeps_technology base scope start.raw 0 word (by
        intro item member
        have original : item ∈ ((Physical.Public.interpreter input).execute start.raw 0 word).items :=
          same ▸ member
        have allowed := first item original
        rwa [lawExact] at allowed)).1
      have frozen := (congrArg (fun result => result.final.technology.technology) same).symm.trans kept
      cases proposal <;> exact frozen

theorem an_authorized_original_history_cannot_move_a_protected_address
    {source : C} {base : Base} {scope : J} (original : Installed source base scope)
    (history : Script) (authority : OriginalAuthority source history) :
    (Quantities.Execution.endAt source history).raw.technology.technology = source.raw.technology.technology := by
  have literal := Quantities.Execution.physical_is_the_folded_actual_end source history
  have inventory := Quantities.Execution.material_is_the_folded_actual_inventory source history
  have unchanged := physical_fold_keeps_technology source.native.input base scope original
    (Evolving.Epoch.Source.originalState source.native) (Quantities.Execution.programme source history)
    (by rwa [inventory])
  exact (congrArg (fun state => state.raw.technology.technology) literal).symm.trans unchanged

theorem no_relabel_of_an_original_protected_address_after_expiry
    {source : C} {base : Base} {scope : J} (original : Installed source base scope)
    (history : Script) (authority : OriginalAuthority source history)
    (expired : scope.task.deadline < (Quantities.Execution.endAt source history).raw.clock) :
    let cut := Quantities.Execution.endAt source history
    ∀ word : Word, ∀ item : Item, item ∈ (law base scope).rawItems cut.raw word →
      Ordinary item.request → ∀ debit : (Party × Good) × ℚ,
        debit ∈ base.debit (eraseCurrent item.before) (eraseRequest item.request) →
        base.stockPort source.raw.technology.technology debit.1.1 debit.1.2 = scope.service →
        ¬ Root.Paid cut word := by
  intro cut word item listed ordinary debit charged sourceAddress paid
  have installed := original.along history
  have actual := original_execution installed paid
  have authorized : ∀ candidate ∈ (law base scope).rawItems cut.raw word,
      (law base scope).Valid candidate.before candidate.request := by
    intro candidate member
    have checked := paid.authorized candidate (by unfold RawLaw.rawItems; rwa [actual])
    rw [show cut.native.input.law = law base scope from installed] at checked
    exact checked
  have frozen := (authorized_word_keeps_technology base scope cut.raw 0 word authorized).2 item listed
  have current := an_authorized_original_history_cannot_move_a_protected_address original history authority
  have protectedUse : base.stockPort item.before.technology.technology debit.1.1 debit.1.2 = scope.service := by
    rw [frozen, show cut.raw.technology.technology = _ from current]
    exact sourceAddress
  exact no_material_relabel_after_expiry installed expired [] word item listed ordinary debit charged protectedUse paid

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency
