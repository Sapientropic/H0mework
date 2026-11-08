import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Review.Payment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange (nativeAccount)
open PublicFunction.Mandate

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port (State Party Technology) Instrument
local notation "Word" => RawEvent Party Good Port (State Party Technology) Instrument
local notation "Item" => ExecutionItem Party Good Port (State Party Technology) Instrument
local notation "Base" => RawLaw Party Good Port Technology Instrument
local notation "J" => Scope (Party := Party) (Good := Good) (Port := Port)
local notation "script" => Quantities.Execution.primitiveScript

/-- The native route reads the actual two inventory positions and each
original debit independently of the raw result. Both reviews belong to the
same whole write and preserve the complete inherited finance book. -/
structure NativeReview (base : Base) (scope : J) (cut : C) (first second : Party) (tail : Word) : Prop where
  positions :
    let head := request scope cut.raw first .review
    let middle := (law base scope).step cut.raw head
    let independent := request scope middle second .review
    (Quantities.Execution.inventory cut (script (reviewWord base scope cut first second tail))).take 2 =
      [⟨0, cut.raw, head⟩, ⟨0, middle, independent⟩]
  debits :
    let active := Physical.Public.interpreter cut.native.input
    let head := request scope cut.raw first .review
    let middle := (law base scope).step cut.raw head
    let independent := request scope middle second .review
    active.actualDebit cut.raw head = locate first scope.revisionCost ∧
      active.actualDebit middle independent = locate second scope.revisionCost
  finance : HEq (nativeAccount (Root.terminal cut (reviewWord base scope cut first second tail)))
    (nativeAccount cut)
  ledger : Quantities.Recorded cut (script (reviewWord base scope cut first second tail))

theorem native_review {cut : C} {base : Base} {scope : J}
    (original : Installed cut base scope) {first second : Party} {tail : Word}
    (safe : LocalTail tail) (paid : Root.Paid cut (reviewWord base scope cut first second tail)) :
    NativeReview base scope cut first second tail := by
  have read := original_execution original paid
  constructor
  · rw [Quantities.Execution.primitive_inventory paid.trace 0, read]
    rfl
  · have physical := paid.trace.every_original_instruction_has_its_actual_guards 0
    rw [read] at physical
    let head := request scope cut.raw first .review
    let middle := (law base scope).step cut.raw head
    let independent := request scope middle second .review
    have firstValid := (physical (⟨0, cut.raw, head⟩ : Item) List.mem_cons_self).1
    have secondValid := (physical (⟨1, middle, independent⟩ : Item)
      (List.mem_cons_of_mem _ List.mem_cons_self)).1
    change (Physical.Public.interpreter cut.native.input).actualDebit cut.raw head = _ ∧
      (Physical.Public.interpreter cut.native.input).actualDebit middle independent = _
    simp only [RawLaw.actualDebit]
    rw [if_pos firstValid, if_pos secondValid]
    change cut.native.input.law.debit cut.raw head = _ ∧ cut.native.input.law.debit middle independent = _
    rw [original]
    exact ⟨rfl, rfl⟩
  · exact Root.nonfinancial_trace_keeps_the_entire_native_book paid.trace
      (nonfinancial_review_word base scope cut first second safe)
  · exact paid.whole.toRecorded

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency
