import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Containment
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Fold

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.NativeDefence

open Capitalism.Universal.Root Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root
open Capitalism.Universal.Abolition.Root.Registered
open Conflict.Consumers (Party Command Word controller creditor exposed issue settle destroy levy)
open Space

noncomputable section

/-- The exposed community controls the shutoff after the emergency opens.
Closing it spends the local maintainer's own stock. -/
def law : RawLaw Party Unit Party Bool Unit := {
  Conflict.Consumers.law with
  revisionPort := fun emergency => if emergency then exposed else controller
  revisionCost := fun old new => if old = new then [] else [((), if new then 2 else 1)]
  necessities := fun _ person => if person = exposed then [((), 1)] else []
  mandatoryMaintenance := fun _ person => if person = exposed then [((), 1)] else []
}

def initial : RawCurrent Party Unit Bool Unit := {
  Conflict.Consumers.initial with stock := fun person _ =>
    if person = exposed then 20 else if person = creditor then 1 else 10
}

def input : ProgrammeSource.Input Party Unit Party Bool Unit where
  law := law
  initial := initial
  instructions := [issue]

def count := Macro.Ingress.cut input 0 8

abbrev Cursor := Physical.Cursor Party Unit Party Bool Unit
abbrev Book := (Epoch.Finance.process input 0 count).GeneratedState
abbrev Frame := Cursor × Book

def opening : Frame := ⟨Physical.initial, (Epoch.Finance.settleCommitted input 0 count).after⟩

def nativeTag (current : Frame) (request : Command) : Epoch.Interface.Tag input 0 count :=
  .actual 0 0 (Physical.receive current.1 (.primitive request))

def step (current : Frame) (request : Command) : Frame :=
  let tag := nativeTag current request
  ⟨Physical.next (Physical.receive current.1 (.primitive request)),
    Epoch.Finance.consumeVisit input 0 count tag
      (Epoch.Interface.root input 0 count tag).initialVisit current.2⟩

def advance (current : Frame) : Word → Frame
  | [] => current
  | request :: rest => advance (step current request) rest

def raw (current : Frame) := (Physical.stateAt input 0 count 0 0 current.1.past).raw

def conflict : Word := [destroy, levy, settle]
def attacked := advance opening conflict

def shutoff : Command := ⟨exposed, [], exposed, [], .revise exposed false⟩
def defended := advance attacked [shutoff]

def life : Command := ⟨exposed, [], exposed, [], .use exposed [((), 1)] .necessity⟩
def maintain : Command := ⟨exposed, [], exposed, [], .use exposed [((), 1)] .maintenance⟩
def exit := advance defended [life, maintain]

theorem actual_foreign_debit_and_local_gate_closure :
    (sourceCrossings law (raw opening, conflict) id).boundaryCertificates.length = 1 ∧
      law.Valid (raw attacked) levy ∧
      law.Valid (raw attacked) shutoff ∧
      ¬ Permission law (raw defended) levy ∧
      (sourceCrossings law (raw attacked, [shutoff]) id).boundaryCertificates.length = 0 ∧
      (raw attacked).stock exposed () = 14 ∧ (raw defended).stock exposed () = 13 := by
  decide +kernel

theorem original_independent_exit_floor_is_paid_from_the_defensive_successor :
    law.Valid (raw defended) life ∧ law.Valid (raw (advance defended [life])) maintain ∧
      law.actualDebit (raw defended) life = [((exposed, ()), 1)] ∧
      law.actualDebit (raw (advance defended [life])) maintain = [((exposed, ()), 1)] ∧
      (raw exit).stock exposed () = 11 ∧ (raw exit).claims = (raw attacked).claims := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  funext instrument issuer holder
  cases instrument
  fin_cases issuer <;> fin_cases holder <;> decide +kernel

theorem a_different_purpose_name_cannot_reopen_the_paid_defence (purpose : Party) :
    ¬ law.Valid (raw defended) {levy with purpose := purpose} := by
  apply a_closed_stock_port_refuses_every_request_charging_the_address _ _ _ exposed () 6
  · exact List.mem_cons_self
  · change law.allowed (raw defended).technology (law.stockPort (raw defended).technology exposed ()) controller = false
    decide +kernel
  · simp [levy, Conflict.Consumers.request]

def originalNativeRun (current : Frame) (word : Word) :
    (Epoch.Finance.process input 0 count).Run current.2.current (advance current word).2.current := by
  induction word generalizing current with
  | nil => exact .nil
  | cons request rest tail =>
      let tag := nativeTag current request
      let front := Epoch.Finance.consumeVisit_run input 0 count tag
        (Epoch.Interface.root input 0 count tag).initialVisit current.2
      exact front.concatRuns _ (tail (step current request))

theorem defence_and_exit_retain_the_original_native_history :
    attacked.2.current.slots.map (Epoch.Finance.slotClaim input 0 count) <+:
      exit.2.current.slots.map (Epoch.Finance.slotClaim input 0 count) ∧
    attacked.2.current.history <+: exit.2.current.history := by
  have trace := originalNativeRun attacked [shutoff, life, maintain]
  refine ⟨Epoch.Finance.run_retains_all_claims input 0 count trace, ?_⟩
  change attacked.2.current.history <+: (advance attacked [shutoff, life, maintain]).2.current.history
  rw [trace.history_eq]
  exact List.prefix_append _ _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.NativeDefence
