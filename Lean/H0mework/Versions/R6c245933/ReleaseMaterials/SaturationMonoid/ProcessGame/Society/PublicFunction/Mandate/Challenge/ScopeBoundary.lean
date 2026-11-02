import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Programme
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed

/-! Boundary receipts are decoded from a scope's own source execution.
They carry no disposition or authority over an earlier scope. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.ScopeBoundary

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Mandate.Lifecycle
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (base : RawLaw Party Good Port Technology Instrument)

structure Source where
  scope : Scope (Party := Party) (Good := Good) (Port := Port)
  bound : BoundSource base scope
  inputs : List (RawEvent Party Good Port (State Party Technology) Instrument)

variable {base} (source : Source base)
abbrev I := OutstandingSource.History.input source.bound.source source.inputs
abbrev current (ordinal : Nat) := OutstandingSource.History.currentAt source.bound.source source.inputs ordinal
def wordAt (ordinal : Nat) := ProgrammeSource.rawEvent (I source) (ProgrammeHistory.visitAt (I source) ordinal).current
abbrev Item (ordinal : Nat) := {item // item ∈ (law base source.scope).rawItems (current source ordinal) (wordAt source ordinal)}

structure Refusal (ordinal : Nat) where
  private mk ::
  item : Item source ordinal
  operator : Party
  target : State Party Technology
  command : Command Party
  operation : item.val.request.operation = .revise operator target
  marked : target.last = some command
  authentic : Observed.Authentic source.scope item.val.before item.val.request operator target command
  refused : ¬ (law base source.scope).Valid item.val.before item.val.request
  boundary : IsBoundary command

inductive Receipt where
  | private paid (ordinal : Nat)
      (actual : ActualCommand base source.scope (current source ordinal) (wordAt source ordinal))
      (boundary : IsBoundary actual.command)
  | private refused (ordinal : Nat) (actual : Refusal source ordinal)

def Receipt.ordinal : Receipt source → Nat
  | .paid ordinal .. | .refused ordinal .. => ordinal
def Receipt.command : Receipt source → Command Party
  | .paid _ actual _ => actual.command
  | .refused _ actual => actual.command
def Receipt.accepted : Receipt source → Bool
  | .paid .. => true | .refused .. => false
def Receipt.item (receipt : Receipt source) : Item source (receipt.ordinal source) :=
  match receipt with
  | .paid _ actual _ => actual.item
  | .refused _ actual => actual.item

def read (ordinal : Nat) (item : Item source ordinal) : Option (Receipt source) :=
  match recognize base source.scope (current source ordinal) (wordAt source ordinal) item with
  | some actual => if boundary : IsBoundary actual.command then some (.paid ordinal actual boundary) else none
  | none => match operation : item.val.request.operation with
    | .revise operator target => match marked : target.last with
      | none => none
      | some command =>
        if refused : ¬ (law base source.scope).Valid item.val.before item.val.request then
          if boundary : IsBoundary command then
            if authentic : Observed.Authentic source.scope item.val.before item.val.request operator target command then
              some (.refused ordinal ⟨item,operator,target,command,operation,marked,authentic,refused,boundary⟩)
            else none
          else none
        else none
    | _ => none

def receiptsAt (ordinal : Nat) :=
  ((law base source.scope).rawItems (current source ordinal) (wordAt source ordinal)).attach.filterMap (read source ordinal)
def receipts (start count : Nat) := ((List.range count).map (fun offset => start + offset)).flatMap (receiptsAt source)

theorem Receipt.acceptance_is_actual (receipt : Receipt source) :
    receipt.accepted source = true ↔ (law base source.scope).Valid (receipt.item source).val.before (receipt.item source).val.request := by
  cases receipt
  next ordinal actual boundary => exact ⟨fun _ => actual.accepted,fun _ => rfl⟩
  next ordinal actual =>
    simp only [Receipt.accepted,Bool.false_eq_true,Receipt.item]
    exact ⟨False.elim,actual.refused⟩

theorem Receipt.running (receipt : Receipt source) : 0 < receipt.ordinal source := by
  by_contra notRunning
  have zero := Nat.eq_zero_of_not_pos notRunning
  have empty : wordAt source 0 = [] := (OutstandingSource.History.actual_frame source.bound.source source.inputs 0).2
  let raw := (receipt.item source).val
  have member : raw ∈ (law base source.scope).rawItems (current source (receipt.ordinal source)) (wordAt source (receipt.ordinal source)) :=
    (receipt.item source).property
  rw [zero,empty] at member
  exact List.not_mem_nil member

theorem Receipt.item_is_in_the_actual_submission (receipt : Receipt source) :
    (receipt.item source).val ∈ (I source).law.rawItems
      (OutstandingSource.History.actualExecution source.bound.source source.inputs (receipt.ordinal source - 1)).before
      (OutstandingSource.History.actualExecution source.bound.source source.inputs (receipt.ordinal source - 1)).submitted := by
  have ordinal : receipt.ordinal source - 1 + 1 = receipt.ordinal source := by have := receipt.running source; omega
  change (receipt.item source).val ∈ source.bound.source.seed.law.rawItems
    (current source (receipt.ordinal source - 1 + 1)) (wordAt source (receipt.ordinal source - 1 + 1))
  rw [ordinal,source.bound.law_exact]
  exact (receipt.item source).property

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.ScopeBoundary
