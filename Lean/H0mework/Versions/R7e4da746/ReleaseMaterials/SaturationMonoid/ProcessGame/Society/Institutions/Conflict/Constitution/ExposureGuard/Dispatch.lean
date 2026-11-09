import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Check

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)
open Reparation.Actual (SourceAuthority)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port Technology Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port Technology Instrument
local notation "Item" => ExecutionItem Party Good Port Technology Instrument

variable {seed : Root.Cut Party Good Port Technology Instrument}
  (roster : List Party) (answers : OwnerAnswers seed)
  (past : Reparation.Actual.Script Party Good Port Technology Instrument)
  (input : Reparation.Actual.Input Party Good Port Technology Instrument)

def Admitted : Prop :=
  SourceAuthority (endAt seed past) [input] ∧ Authorized roster answers past input

inductive Failure where
  | authority (item : Item) (present : item ∈ originalItems (seed := seed) past input)
      (invalid : ¬ (endAt seed past).native.input.law.Valid item.before item.request)
  | owner (denied : Denial roster answers past input)

theorem Failure.refutes (failed : Failure roster answers past input) :
    ¬ Admitted roster answers past input := by
  intro lawful
  cases failed with
  | authority item present invalid => exact invalid (lawful.1 item present)
  | owner denied => exact denied.refutes _ _ _ _ lawful.2

def inspectAdmission : Failure roster answers past input ⊕ PLift (Admitted roster answers past input) :=
  match inspect roster answers past input with
  | .inl denied => .inl (.owner denied)
  | .inr accepted =>
    match Capitalism.Universal.Abolition.Material.inspectList
      (fun item : Item => (endAt seed past).native.input.law.Valid item.before item.request)
      (originalItems (seed := seed) past input) with
    | .failure item listed denied => .inl (.authority item listed denied)
    | .clear lawful => .inr ⟨⟨lawful, accepted.down⟩⟩

abbrev stop : Input := some .stopReview

inductive Dispatch where
  | forward (admitted : Admitted roster answers past input)
  | stopOriginal (failed : Failure roster answers past input)
      (empty : originalItems (seed := seed) past stop = [])
  | held (failed : Failure roster answers past input)
      (forcedBody : originalItems (seed := seed) past stop ≠ [])

def dispatch : Dispatch roster answers past input :=
  match inspectAdmission roster answers past input with
  | .inr admitted => .forward admitted.down
  | .inl issue =>
    if empty : (originalItems (seed := seed) past stop).length = 0 then
      .stopOriginal issue (List.eq_nil_of_length_eq_zero empty)
    else .held issue (fun noItems => empty (congrArg List.length noItems))

def Dispatch.selected : Dispatch roster answers past input → Word
  | .forward _ => [input]
  | .stopOriginal _ _ => [stop]
  | .held _ _ => []

theorem no_material_is_admitted (empty : originalItems (seed := seed) past input = []) :
    Admitted roster answers past input := by
  constructor
  · intro item listed
    change item ∈ originalItems (seed := seed) past input at listed
    rw [empty] at listed
    exact (List.not_mem_nil listed).elim
  · intro position
    have inside : position.val < 0 := Nat.lt_of_lt_of_eq position.isLt (congrArg List.length empty)
    exact (Nat.not_lt_zero _ inside).elim

theorem the_dispatcher_forwards_every_original_admitted_input (lawful : Admitted roster answers past input) :
    (dispatch roster answers past input).selected _ _ _ _ = [input] := by
  unfold dispatch
  cases inspectAdmission roster answers past input with
  | inr _ => rfl
  | inl issue => exact (issue.refutes _ _ _ _ lawful).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard
