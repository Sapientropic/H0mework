import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Consumers.Compact.Origin
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Unfolding.Current
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Source.Quantities
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Finance
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Settlement.Word

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Consumers.Compact

open Source.Program Innovation
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

def recordedRaw := law.next before originalWord
def recordedFamily := Responsibility.Family.State.declare productiveClaim (Responsibility.Family.State.atCursor productiveClaim recordedRaw)
def observedFamily := Responsibility.Family.State.advance productiveClaim recordedFamily (PublicFunction.physicalLaw law) []

theorem the_original_root_initial_cursor_is_its_actual_physical_successor :
    (Abolition.Accounting.Root.Source.initialState input native visit productiveClaim).raw = recordedRaw := by
  have sourced := Financial.Installation.Cursor.last_execution_returns_actual_physical_current input (native.cursor visit.current)
  change ProgrammeSource.rawCurrent input (Financial.Installation.Cursor.physicalVisit input
    (Financial.Installation.Cursor.next input (native.cursor visit.current))).current = _
  rw [← sourced,← origin.law,← origin.before,← origin.word]
  rfl

theorem the_existing_root_declaration_is_the_original_matrix :
    Abolition.Accounting.Root.Source.declared input native visit productiveClaim = recordedFamily :=
  congrArg (fun raw => Responsibility.Family.State.declare productiveClaim (Responsibility.Family.State.atCursor productiveClaim raw))
    the_original_root_initial_cursor_is_its_actual_physical_successor

theorem the_existing_productive_row_is_read_without_reset : productiveState seed = observedFamily := by
  unfold productiveState Global.Seed.current seed
  rw [Priority.Root.afterInputs,Completion.current_family_is_the_actual_observed_row]
  change Abolition.Accounting.Root.Source.observed input native visit productiveClaim [] = observedFamily
  unfold Abolition.Accounting.Root.Source.observed
  rw [the_existing_root_declaration_is_the_original_matrix]
  rfl

theorem the_live_interpreter_is_the_same_public_physical_law : actualLaw seed = PublicFunction.physicalLaw law := rfl

def shared := Current.declareGross seed grossClaim (Current.initial seed grossClaim)

theorem shared_raw : shared.raw = (PublicFunction.physicalLaw law).next recordedRaw [] := by
  change (productiveState seed).raw = _
  rw [the_existing_productive_row_is_read_without_reset]
  rfl

def physicalSnapshot : RawCurrent Bool Bool Unit Unit where
  stock := fun actor good => if good then if actor then 3 else 1 else if actor then 100 else 0
  claims := fun _ debtor creditor => if debtor = false ∧ creditor = true then 1 else 0
  technology := ()
  clock := 3
  round := 3

theorem shared_raw_readout : shared.raw = physicalSnapshot := by
  rw [shared_raw]
  apply RawCurrent.ext
  · funext actor good
    cases actor <;> cases good <;> decide +kernel
  · funext instrument debtor creditor
    cases instrument
    cases debtor <;> cases creditor <;> decide +kernel
  · exact Subsingleton.elim _ _
  · decide +kernel
  · decide +kernel

theorem shared_productive_remaining (key : Bool × Bool) :
    shared.productive key = if key = (false,false) then 18 else 0 := by
  change (productiveState seed).remaining key = _
  rw [the_existing_productive_row_is_read_without_reset]
  rcases key with ⟨actor,good⟩
  cases actor <;> cases good <;> decide +kernel

theorem shared_productive_declared : shared.productiveDeclared = true := by
  change (productiveState seed).declared = true
  rw [the_existing_productive_row_is_read_without_reset]
  rfl

theorem shared_productive_scope : Responsibility.Family.positiveScope mechanism past nature response = [(false,false)] := by
  decide +kernel

theorem shared_gross_declared : shared.grossDeclared = true := rfl

theorem shared_gross_scope : Entitlement.Duty.scope (window seed) = [(false,true,false)] := by decide +kernel

theorem shared_gross_remaining (key : Bool × Bool × Bool) :
    shared.gross key = if key = (false,true,false) then 100 else 0 := by
  change Entitlement.Duty.quantity (window seed) key = _
  apply a_singleton_source_scope_retains_its_entire_original_quantity _ _ shared_gross_scope
  rw [the_gross_source_has_only_its_original_hundred]
  norm_num

theorem live_roster : seed.current.members = [false,true] := by decide +kernel

theorem live_native_account : Evolution.Ingress.Joint.Background.account seed =
    (Financial.Installation.Cursor.next input (Financial.Installation.Runtime.cursorAt input 0 19)).account := by
  have originalNext := Evolution.Ingress.Joint.Background.the_actual_cursor_is_the_original_next_cursor seed
  change Evolution.Ingress.Joint.Background.cursor seed = Financial.Installation.Cursor.next input (original.cursor input) at originalNext
  rw [cursor_eq] at originalNext
  exact congrArg (fun cursor => cursor.account) originalNext

abbrev originalAccount := (Financial.Installation.Cursor.next input (Financial.Installation.Runtime.cursorAt input 0 19)).account

theorem original_slot_count : originalAccount.current.slots.length = 1 := by decide +kernel

def originalSlot := originalAccount.current.slots.get ⟨0,by rw [original_slot_count]; decide⟩

private theorem one_slot {α : Type} (entries : List α) (count : entries.length = 1) (bound : 0 < entries.length) :
    entries = [entries.get ⟨0,bound⟩] := by
  cases entries with
  | nil => cases count
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons next rest => simp only [List.length_cons] at count; omega

theorem original_slots : originalAccount.current.slots = [originalSlot] :=
  one_slot _ original_slot_count _

theorem original_balance : Financial.slotBalance input originalSlot = Finsupp.single true 1 := by
  ext actor
  cases actor with
  | false => rw [Finsupp.single_eq_of_ne (by decide : false ≠ true)]; decide +kernel
  | true => rw [Finsupp.single_eq_same]; decide +kernel

theorem original_debtor : (Financial.slotClaim input originalSlot).debtor = false := by decide +kernel

private theorem legacy_balance (slot : ResponsibilityLifecycle.ObligationSlot (Financial.vocabulary input)) :
    Abolition.Root.Epoch.Finance.slotBalance input 0 19 (Abolition.Root.Epoch.Finance.Legacy.slot input 0 19 slot) =
      Financial.slotBalance input slot := by
  cases slot <;> rfl

private theorem legacy_claim (slot : ResponsibilityLifecycle.ObligationSlot (Financial.vocabulary input)) :
    Abolition.Root.Epoch.Finance.slotClaim input 0 19 (Abolition.Root.Epoch.Finance.Legacy.slot input 0 19 slot) =
      .inl (Financial.slotClaim input slot) := by
  cases slot <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem original_financial_tail : Evolution.Ingress.Joint.Settlement.word seed =
    [⟨false,[],false,[],.settle () false true 1⟩] := by
  unfold Evolution.Ingress.Joint.Settlement.word Evolution.Ingress.Joint.Settlement.wordFrom
    Evolution.Ingress.Joint.Background.nativeAccount
  rw [Abolition.Root.Epoch.Finance.Legacy.generated_current]
  rw [live_native_account]
  simp only [seed,Abolition.Root.Epoch.Finance.Legacy.state]
  rw [original_slots]
  simp only [List.map_cons,List.map_nil,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [legacy_balance,original_balance]
  rw [Finsupp.support_single true (by norm_num : (1 : ℚ) ≠ 0)]
  simp only [Finset.toList_singleton,List.filterMap_cons,List.filterMap_nil]
  norm_num only [Finsupp.single_eq_same,if_pos,zero_lt_one]
  simp only [Evolution.Ingress.Joint.Settlement.request,legacy_claim,legacy_balance,original_balance,
    Abolition.Root.Epoch.Finance.Claim.debtor,Abolition.Root.Epoch.Finance.Claim.instrument,
    original_debtor,Finsupp.single_eq_same]
  have instrument : (Financial.slotClaim input originalSlot).instrument = () := Subsingleton.elim _ _
  rw [instrument]
  change ([⟨false,[],(actualLaw seed).issuerPort (),[],.settle () false true 1⟩] : RawEvent Bool Bool Bool Unit Unit) = _
  rw [the_live_interpreter_is_the_same_public_physical_law]
  rfl

theorem both_original_members_remain_in_the_live_roster (actor : Bool) : actor ∈ seed.current.members := by
  cases actor <;> decide +kernel

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Consumers.Compact
