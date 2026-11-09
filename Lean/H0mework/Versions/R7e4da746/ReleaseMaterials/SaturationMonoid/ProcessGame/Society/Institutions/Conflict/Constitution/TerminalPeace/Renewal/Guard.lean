import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Supply.Rule
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Incidence

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Renewal

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

abbrev Native := Capitalism.Universal.Abolition.Root.Actual.Current
  (Party := Bool) (Good := Bool) (Port := Bool) (Technology := Unit) (Instrument := Unit)
abbrev Request := Compile.RawInput Bool Bool Bool Unit Unit

abbrev readAction (before : Native) (request : Request) :=
  Physical.Public.compile Supply.revisedInput before request

abbrev Replies (before : Native) (request : Request) :=
  Fin (readAction before request).execution.items.length → Bool → Bool

def foodPaid (items : List Original.Item) (person : Bool) : ℚ :=
  (items.map fun item =>
    match item.request.operation with
    | .use bearer _ kind =>
      if bearer = person ∧ kind = .necessity then
        flowAt (Supply.physical.actualDebit item.before item.request) person true else 0
    | _ => 0).sum

def samePrincipal (before after : Original.Raw) : Prop :=
  ∀ payer ∈ ([false, true] : List Bool), ∀ holder ∈ ([false, true] : List Bool),
    after.claims () payer holder = before.claims () payer holder

instance (before after : Original.Raw) : Decidable (samePrincipal before after) := by
  unfold samePrincipal
  infer_instance

theorem samePrincipal.matrix {before after : Original.Raw} (same : samePrincipal before after) :
    after.claims = before.claims := by
  funext instrument payer holder
  cases instrument
  exact same payer (by cases payer <;> decide) holder (by cases holder <;> decide)

def isProduction (item : Original.Item) : Bool :=
  match item.request.operation with
  | .produce _ => true
  | _ => false

/-- Any advancing material word pays the two original living cells once
from its actual items. Production also needs its own physical period. -/
def paidCrossing (before after : Original.Raw) (items : List Original.Item) : Prop :=
  (after.clock = before.clock ∧ ∀ item ∈ items, isProduction item = false) ∨
    (after.clock = before.clock + 1 ∧ ∀ person ∈ ([false, true] : List Bool), 1 ≤ foodPaid items person)

instance (before after : Original.Raw) (items : List Original.Item) : Decidable (paidCrossing before after items) := by
  unfold paidCrossing
  infer_instance

theorem paidCrossing.clock_mono {before after : Original.Raw} {items : List Original.Item}
    (paid : paidCrossing before after items) : before.clock ≤ after.clock := by
  rcases paid with ⟨same, _⟩ | ⟨later, _⟩
  · rw [same]
  · rw [later]
    linarith

theorem paidCrossing.every_advance_pays_each_person {before after : Original.Raw} {items : List Original.Item}
    (paid : paidCrossing before after items) (advances : before.clock < after.clock) (person : Bool) :
    1 ≤ foodPaid items person := by
  rcases paid with ⟨same, _⟩ | ⟨_, payment⟩
  · exact ((ne_of_lt advances) same.symm).elim
  · exact payment person (by cases person <;> decide)

def AllowedItem (item : Original.Item) : Prop :=
  Supply.revisedLaw.Valid item.before item.request ∧
    (∀ payer ∈ ([false, true] : List Bool), ∀ good ∈ ([false, true] : List Bool),
      Reparation.loss Supply.physical Original.community item (payer, item.request.signer, good) = 0) ∧
    (∀ payer ∈ ([false, true] : List Bool), ∀ holder ∈ ([false, true] : List Bool),
      Supply.physical.actualClaimDelta item.before item.request () payer holder = 0)

instance (item : Original.Item) : Decidable (AllowedItem item) := by
  unfold AllowedItem
  infer_instance

theorem AllowedItem.no_damage {item : Original.Item} (allowed : AllowedItem item)
    (key : Reparation.Key Bool Bool) :
    Reparation.loss Supply.physical Original.community item key = 0 := by
  by_cases same : item.request.signer = key.2.1
  · rcases key with ⟨payer, signer, good⟩
    change item.request.signer = signer at same
    subst signer
    exact allowed.2.1 payer (by cases payer <;> decide) good (by cases good <;> decide)
  · unfold Reparation.loss
    exact if_neg (fun coercive => same coercive.2.1)

variable (before : Native) (request : Request)

local notation "Result" => readAction before request
local notation "Items" => ExecutionResult.items (Physical.Public.ResultAt.execution Result)
local notation "Position" => Fin (List.length Items)

instance (raw : Original.Raw) : Decidable (Supply.Stocked raw) :=
  decidable_of_iff (∀ person ∈ ([false, true] : List Bool),
      18 ≤ raw.stock person false ∧ 0 ≤ raw.stock person true) <| by
    constructor
    · exact fun checked person => checked person (by cases person <;> decide)
    · exact fun stocked person _ => stocked person

def OwnAt (answers : Replies before request) (position : Position) : Prop :=
  let item := (Items)[position]
  AllowedItem item ∧ answers position item.request.signer = true ∧
    Supply.Stocked item.before ∧ Supply.Stocked (Supply.physical.step item.before item.request)

instance (answers : Replies before request) (position : Position) : Decidable (OwnAt before request answers position) := by
  unfold OwnAt
  infer_instance

structure Admission (answers : Replies before request) : Prop where
  selected : (Result).isAccepted = true
  owns : ∀ position, OwnAt before request answers position
  principal : samePrincipal before.raw (Result).next.raw
  stocked : Supply.Stocked (Result).next.raw
  pays : paidCrossing before.raw (Result).next.raw Items

inductive Refusal (answers : Replies before request)
  | noPhysicalWrite (missing : (Result).isAccepted ≠ true)
  | item (position : Position) (denied : ¬ OwnAt before request answers position)
  | finance (changed : ¬ samePrincipal before.raw (Result).next.raw)
  | inventory (short : ¬ Supply.Stocked (Result).next.raw)
  | crossing (failed : ¬ paidCrossing before.raw (Result).next.raw Items)

/-- A raw proposal receives its disposition from the physical compiler
and the first original-position authority check. -/
def inspect (answers : Replies before request) :
    Refusal before request answers ⊕ PLift (Admission before request answers) :=
  if physical : (Result).isAccepted = true then
    match Capitalism.Universal.Abolition.Material.inspectList (OwnAt before request answers)
        (List.finRange (List.length Items)) with
    | .failure position _ denied => .inl (.item position denied)
    | .clear owns =>
      if principal : samePrincipal before.raw (Result).next.raw then
        if stocked : Supply.Stocked (Result).next.raw then
          if paid : paidCrossing before.raw (Result).next.raw Items then
            .inr ⟨⟨physical, fun position => owns position (List.mem_finRange _), principal, stocked, paid⟩⟩
          else .inl (.crossing paid)
        else .inl (.inventory stocked)
      else .inl (.finance principal)
  else .inl (.noPhysicalWrite physical)

theorem Refusal.refutes {answers : Replies before request} (issue : Refusal before request answers) :
    ¬ Admission before request answers := by
  intro checked
  cases issue with
  | noPhysicalWrite failed => exact failed checked.selected
  | item position denied => exact denied (checked.owns position)
  | finance changed => exact changed checked.principal
  | inventory short => exact short checked.stocked
  | crossing failed => exact failed checked.pays

theorem inspect_covers_all_admitted_original_effects {answers : Replies before request}
    (admitted : Admission before request answers) :
    ∃ selected, inspect before request answers = .inr selected := by
  cases inspect before request answers with
  | inl refused => exact (refused.refutes _ _ admitted).elim
  | inr selected => exact ⟨selected, rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Renewal
