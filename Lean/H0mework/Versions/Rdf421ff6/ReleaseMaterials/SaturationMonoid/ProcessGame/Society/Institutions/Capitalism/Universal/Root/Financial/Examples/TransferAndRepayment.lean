import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Fold
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Principal

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Examples.TransferAndRepayment

open Source.Program ResponsibilityLifecycle

abbrev Party := Fin 3

def law : RawLaw Party Unit Unit Unit Unit where
  technique := fun _ _ => ⟨[], [], [], []⟩
  controller := fun _ _ => 0
  allowed := fun _ _ _ => true
  stockPort := fun _ _ _ => ()
  revisionPort := fun _ => ()
  revisionCost := fun _ _ => []
  settlementUnit := fun _ => ()
  settlementRate := fun _ => 1
  issuerPort := fun _ => ()
  necessities := fun _ _ => []
  mandatoryMaintenance := fun _ _ => []
  duration := fun _ => 1

def initial : RawCurrent Party Unit Unit Unit where
  stock := fun person _ => if person = 0 then 2 else 0
  claims := fun _ _ _ => 0
  technology := ()
  clock := 0
  round := 0

def request (signer : Party) (operation : Operation Party Unit Unit Unit) :
    Request Party Unit Unit Unit Unit := ⟨signer, [], (), [], operation⟩

def word : RawEvent Party Unit Unit Unit Unit :=
  [request 0 (.issue () 0 1 2), request 1 (.assign () 0 1 2 1),
   request 0 (.settle () 0 1 1), request 0 (.settle () 0 2 1)]

def input : ProgrammeSource.Input Party Unit Unit Unit Unit := ⟨law, initial, word, none, fun _ => [], none⟩

def final := accountAt input 2

theorem one_original_loan_slot : final.current.slots.length = 1 := by decide +kernel

theorem four_actual_lifecycle_events : final.current.history.length = 4 := by decide +kernel

theorem all_principal_actually_paid : outstanding input final.current = 0 := by decide +kernel

theorem material_reached_both_original_holders :
    (law.next initial word).stock 0 () = 0 ∧
    (law.next initial word).stock 1 () = 1 ∧
    (law.next initial word).stock 2 () = 1 := by decide +kernel

theorem admission_was_not_rewritten :
    ((final.current.slots.map (slotClaim input)).map (fun claim =>
      (claim.debtor, claim.holder, claim.quantity))) = [(0, 1, 2)] := by decide +kernel

theorem final_slot_is_terminal :
    ∃ archive, final.current.slots = [.terminal archive] := by
  let terminalStatus : ObligationSlot (vocabulary input) → Bool
    | .live _ => false
    | .terminal _ => true
  have terminal : final.current.slots.map terminalStatus = [true] := by decide +kernel
  cases slots : final.current.slots with
  | nil => simp [slots] at terminal
  | cons head tail =>
      cases tail with
      | cons _ _ => simp [slots] at terminal
      | nil =>
          cases head with
          | live _ => simp [slots, terminalStatus] at terminal
          | terminal archive => exact ⟨archive, rfl⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Examples.TransferAndRepayment
