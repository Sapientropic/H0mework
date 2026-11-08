import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Aggression
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.ExitFloor

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

local notation "Law" => RawLaw Party Good Port Technology Instrument
local notation "Raw" => RawCurrent Party Good Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Item" => ExecutionItem Party Good Port Technology Instrument
local notation "Req" => Request Party Good Port Technology Instrument

/-- The original command's policy and ports, separated from resource
exhaustion. Emptying the victim's stock cannot pass this guard by itself. -/
def Permission (law : Law) (current : Raw) (request : Req) : Prop :=
  law.operationAllowed current request = true ∧
    ∀ port ∈ law.requiredPorts current request,
      law.allowed current.technology port request.signer = true ∨
        law.controller current.technology port ∈ request.consents

instance (law : Law) (current : Raw) (request : Req) : Decidable (Permission law current request) := by
  unfold Permission
  infer_instance

omit [DecidableEq Instrument] in
theorem permission_of_valid (law : Law) (current : Raw) (request : Req)
    (valid : law.Valid current request) : Permission law current request :=
  ⟨valid.1.2, valid.2.1⟩

def ClosesPermission (law : Law) (attack : Req) (item : Item) : Prop :=
  Permission law item.before attack ∧ ¬ Permission law (law.step item.before item.request) attack

instance (law : Law) (attack : Req) (item : Item) :
    Decidable (ClosesPermission law attack item) := by
  unfold ClosesPermission
  infer_instance

/-- A permission change has a position in the actual instruction word. -/
theorem an_actual_instruction_closes_permission (law : Law) (attack : Req) (word : Word)
    (current : Raw) (index : Nat) (openBefore : Permission law current attack)
    (closedAfter : ¬ Permission law (law.execute current index word).final attack) :
    ∃ item ∈ (law.execute current index word).items, ClosesPermission law attack item := by
  induction word generalizing current index with
  | nil => exact (closedAfter openBefore).elim
  | cons request rest ih =>
      by_cases available : Permission law (law.step current request) attack
      · obtain ⟨item, later, effect⟩ := ih (law.step current request) (index + 1) available closedAfter
        exact ⟨item, List.mem_cons_of_mem _ later, effect⟩
      · exact ⟨⟨index, current, request⟩, List.mem_cons_self, openBefore, available⟩

omit [DecidableEq Instrument] in
/-- The original stock port applies to every command charging that address,
including a command with a different purpose name or operation shape. -/
theorem a_closed_stock_port_refuses_every_request_charging_the_address
    (law : Law) (current : Raw) (request : Req) (bearer : Party) (good : Good) (quantity : ℚ)
    (charged : ((bearer, good), quantity) ∈ law.debit current request)
    (closed : law.allowed current.technology (law.stockPort current.technology bearer good) request.signer = false)
    (noConsent : law.controller current.technology (law.stockPort current.technology bearer good) ∉ request.consents) :
    ¬ law.Valid current request := by
  intro valid
  have port : law.stockPort current.technology bearer good ∈ law.requiredPorts current request := by
    unfold RawLaw.requiredPorts
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem charged))
  rcases valid.2.1 _ port with allowed | consent
  · rw [closed] at allowed
    cases allowed
  · exact noConsent consent

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary
