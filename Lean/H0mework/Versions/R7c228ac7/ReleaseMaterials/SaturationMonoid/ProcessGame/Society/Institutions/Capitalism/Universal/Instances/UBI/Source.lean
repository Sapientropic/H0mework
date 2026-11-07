import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Retiming
import Mathlib.Tactic.NormNum

/-! Periodic public credit has purchasing power through actual redemption.
The member can redeem the issued claim personally, without employer or
official consent.  Public production supplies the real redemption leg; its
operator cannot appropriate that stock through an ordinary private use. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Instances.UBI

open Source.Program

abbrev Current := RawCurrent Bool Unit Unit Unit
abbrev Input := Request Bool Unit Unit Unit Unit

def policy (request : Input) : Bool := match request.operation with
  | .produce operator => !operator && !request.signer
  | .issue _ issuer recipient quantity => !issuer && recipient && decide (quantity = 1)
  | .assign _ issuer _ _ _ => !issuer
  | .settle _ debtor creditor _ => !debtor && creditor && request.signer
  | .use bearer _ .necessity => bearer && request.signer
  | .present => true
  | _ => false

def law : RawLaw Bool Unit Unit Unit Unit where
  technique := fun _ member => if member then ⟨[], [], [], []⟩ else
    ⟨[((), 1)], [((), 2)], [], []⟩
  controller := fun _ _ => false
  allowed := fun _ _ _ => true
  stockPort := fun _ _ _ => ()
  revisionPort := fun _ => ()
  revisionCost := fun _ _ => []
  settlementUnit := fun _ => ()
  settlementRate := fun _ => 1
  issuerPort := fun _ => ()
  necessities := fun _ member => if member then [((), 1)] else []
  mandatoryMaintenance := fun _ _ => []
  policy := .settlement ⟨false, true, 1⟩
  duration := fun _ => 1

theorem policy_code_exact (request : Input) :
    (SettlementPolicyCode.mk false true 1).eval request = policy request := by
  rcases request with ⟨signer, consents, purpose, gates, operation⟩
  cases operation with
  | produce operator => cases operator <;> cases signer <;> rfl
  | issue instrument issuer recipient quantity =>
      cases issuer <;> cases recipient <;> simp [SettlementPolicyCode.eval, policy]
  | assign instrument issuer sender recipient quantity => cases issuer <;> rfl
  | settle instrument debtor creditor quantity => cases debtor <;> cases creditor <;> cases signer <;> rfl
  | use bearer goods kind => cases kind <;> cases bearer <;> cases signer <;> rfl
  | transfer sender recipient goods => rfl
  | revise operator technology => rfl
  | present => rfl

theorem time_independent : law.TimeIndependent :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

def state (clock : ℚ) (round : Nat) : Current where
  stock := fun member _ => if member then 0 else 1
  claims := fun _ _ _ => 0
  technology := ()
  clock := clock
  round := round

def produce : Input := ⟨false, [], (), [], .produce false⟩
def grant : Input := ⟨false, [], (), [], .issue () false true 1⟩
def redeem : Input := ⟨true, [], (), [], .settle () false true 1⟩
def consume : Input := ⟨true, [], (), [], .use true [((), 1)] .necessity⟩

def body : List Input := [produce, grant, redeem, consume]
def program : RawProgram Bool Unit Unit Unit Unit := ⟨law, state 0 0, fun _ => body⟩

theorem redemption_is_personally_authorized : redeem.signer = true ∧ redeem.consents = [] := ⟨rfl, rfl⟩

theorem public_stock_has_no_private_use_authority (current : Current) (goods : Bundle Unit) :
    ¬ law.Valid current ⟨false, [], (), [], .use false goods .external⟩ := by
  intro accepted
  have impossible := accepted.1.2
  change false = true at impossible
  contradiction

theorem member_cannot_issue_public_money (current : Current) :
    ¬ law.Valid current ⟨true, [], (), [], .issue () false true 1⟩ := by
  intro accepted
  have impossible := accepted.1.1
  change true = false at impossible
  contradiction

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Instances.UBI
