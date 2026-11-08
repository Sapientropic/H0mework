import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Legacy
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Source

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers

open Source.Program Innovation ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Quantifiers.Joint
open Evolution.Ingress.Joint

noncomputable section

def shared := Evolution.Ingress.Joint.Material.shared seed grossClaim

theorem shared_raw : shared.raw = Quantifiers.Joint.Consumers.Compact.physicalSnapshot := by
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;> decide +kernel
  · funext instrument debtor holder
    cases instrument
    cases debtor <;> cases holder <;> decide +kernel
  · exact Subsingleton.elim _ _
  · decide +kernel
  · decide +kernel

theorem productive_remaining (key : Bool × Bool) :
    shared.productive key = if key = (false,false) then 18 else 0 := by
  rcases key with ⟨person, good⟩
  cases person <;> cases good <;> decide +kernel

theorem productive_scope :
    Responsibility.Family.positiveScope mechanism CompactSource.past nature CompactSource.response = [(false,false)] := by
  decide +kernel

theorem gross_scope : Entitlement.Duty.scope (window seed) = [(false,true,false)] := by decide +kernel

theorem gross_remaining (key : Bool × Bool × Bool) :
    shared.gross key = if key = (false,true,false) then 100 else 0 := by
  change Entitlement.Duty.quantity (window seed) key = _
  apply a_singleton_source_scope_retains_its_entire_original_quantity _ _ gross_scope
  unfold Entitlement.Source.demands Entitlement.Source.Window.legs
  unfold Entitlement.Source.Window.before Entitlement.Source.Window.word Entitlement.Source.Window.visit
    Entitlement.Source.Window.cursor Entitlement.Source.Window.frame window seed
  simp only [Financial.Installation.Cursor.lastExecutedVisit]
  decide +kernel

theorem live_roster : seed.current.members = [false,true] := by decide +kernel
theorem productive_declared : shared.productiveDeclared = true := by decide +kernel
theorem gross_declared : shared.grossDeclared = true := rfl
theorem cohort : Responsibility.controllerCohort mechanism CompactSource.past nature CompactSource.response = [true] := by
  decide +kernel

private abbrev oldAccount := (Financial.Installation.Cursor.next input
  (Financial.Installation.Runtime.cursorAt input 0 19)).account
private theorem slots_length : oldAccount.current.slots.length = 1 := by decide +kernel
private def oldSlot := oldAccount.current.slots.get ⟨0, by rw [slots_length]; decide⟩

private theorem single_slot {Slot : Type} (slots : List Slot) (length : slots.length = 1)
    (inside : 0 < slots.length) : slots = [slots.get ⟨0, inside⟩] := by
  cases slots with
  | nil => cases length
  | cons first rest =>
    cases rest with
    | nil => rfl
    | cons second rest => simp only [List.length_cons] at length; omega

private theorem old_slots : oldAccount.current.slots = [oldSlot] :=
  single_slot _ slots_length _

private theorem old_balance : Financial.slotBalance input oldSlot = Finsupp.single true 1 := by
  ext actor
  cases actor with
  | false => rw [Finsupp.single_eq_of_ne (by decide : false ≠ true)]; decide +kernel
  | true => rw [Finsupp.single_eq_same]; decide +kernel

private theorem old_debtor : (Financial.slotClaim input oldSlot).debtor = false := by decide +kernel

private theorem carried_balance (slot : ObligationSlot (Financial.vocabulary input)) :
    Epoch.Finance.slotBalance input 0 19 (Epoch.Finance.Legacy.slot input 0 19 slot) =
      Financial.slotBalance input slot := by cases slot <;> rfl

private theorem carried_claim (slot : ObligationSlot (Financial.vocabulary input)) :
    Epoch.Finance.slotClaim input 0 19 (Epoch.Finance.Legacy.slot input 0 19 slot) =
      .inl (Financial.slotClaim input slot) := by cases slot <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem original_financial_tail :
    Evolution.Ingress.Joint.Settlement.word seed =
      [⟨false,[],false,[],.settle () false true 1⟩] := by
  have account : Background.account seed = oldAccount := by
    have same := Background.the_actual_cursor_is_the_original_next_cursor seed
    change Background.cursor seed = Financial.Installation.Cursor.next input (oldFrame.cursor input) at same
    rw [cursor_eq] at same
    exact congrArg (fun cursor => cursor.account) same
  unfold Evolution.Ingress.Joint.Settlement.word Evolution.Ingress.Joint.Settlement.wordFrom Background.nativeAccount
  rw [Epoch.Finance.Legacy.generated_current, account]
  simp only [seed, Epoch.Finance.Legacy.state]
  rw [old_slots]
  simp only [List.map_cons,List.map_nil,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [carried_balance, old_balance, Finsupp.support_single true (by norm_num : (1 : ℚ) ≠ 0)]
  simp only [Finset.toList_singleton,List.filterMap_cons,List.filterMap_nil]
  norm_num only [Finsupp.single_eq_same,if_pos,zero_lt_one]
  simp only [Evolution.Ingress.Joint.Settlement.request,carried_claim,carried_balance,old_balance,
    Epoch.Finance.Claim.debtor,Epoch.Finance.Claim.instrument,old_debtor,Finsupp.single_eq_same]
  rw [show (Financial.slotClaim input oldSlot).instrument = () from Subsingleton.elim _ _]
  rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers
