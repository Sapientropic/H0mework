import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Installed.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Consumers.Compact.Execution

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Installed

open Capitalism.Universal.Source.Program Capitalism.Universal.Root Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Accounting Capitalism.Universal.Abolition.Accounting.Quantifiers Joint
open Capitalism.Universal.Abolition.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

def recordedRaw := active.next before originalWord
def recordedFamily := Responsibility.Family.State.declare productiveClaim
  (Responsibility.Family.State.atCursor productiveClaim recordedRaw)
def observedFamily := Responsibility.Family.State.advance productiveClaim recordedFamily (PublicFunction.physicalLaw active) []

private theorem original_raw : (Accounting.Root.Source.initialState input native visit productiveClaim).raw = recordedRaw := by
  have sourced := Financial.Installation.Cursor.last_execution_returns_actual_physical_current input (native.cursor visit.current)
  change ProgrammeSource.rawCurrent input (Financial.Installation.Cursor.physicalVisit input
    (Financial.Installation.Cursor.next input (native.cursor visit.current))).current = _
  rw [← sourced, ← origin.law, ← origin.before, ← origin.word]
  rfl

private theorem declared_original : Accounting.Root.Source.declared input native visit productiveClaim = recordedFamily :=
  congrArg (fun raw => Responsibility.Family.State.declare productiveClaim (Responsibility.Family.State.atCursor productiveClaim raw))
    original_raw

private theorem productive_original : productiveState seed = observedFamily := by
  unfold productiveState Global.Seed.current seed
  rw [Priority.Root.afterInputs, Completion.current_family_is_the_actual_observed_row]
  change Accounting.Root.Source.observed input native visit productiveClaim [] = observedFamily
  unfold Accounting.Root.Source.observed
  rw [declared_original]
  rfl

theorem physical_law : actualLaw seed = PublicFunction.physicalLaw active := rfl

def shared := Current.declareGross seed grossClaim (Current.initial seed grossClaim)

def snapshot : Raw where
  stock := fun person good => if good then if person then 3 else 1 else if person then 100 else 0
  claims := fun _ debtor creditor => if debtor = false ∧ creditor = true then 1 else 0
  technology := releasedTech
  clock := 3
  round := 3

theorem shared_raw : shared.raw = snapshot := by
  change (productiveState seed).raw = snapshot
  rw [productive_original]
  change (PublicFunction.physicalLaw active).next recordedRaw [] = _
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;> decide +kernel
  · funext instrument debtor creditor
    cases instrument
    cases debtor <;> cases creditor <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem productive_balance (key : Bool × Bool) :
    shared.productive key = if key = (false, false) then 18 else 0 := by
  change (productiveState seed).remaining key = _
  rw [productive_original]
  rcases key with ⟨person, good⟩
  cases person <;> cases good <;> decide +kernel

theorem productive_declared : shared.productiveDeclared = true := by
  change (productiveState seed).declared = true
  rw [productive_original]
  rfl

theorem productive_scope : Responsibility.Family.positiveScope mechanism past nature response = [(false, false)] := by
  decide +kernel

theorem gross_declared : shared.grossDeclared = true := rfl

theorem gross_scope : Entitlement.Duty.scope (window seed) = [(false, true, false)] := by decide +kernel

theorem gross_balance (key : Bool × Bool × Bool) :
    shared.gross key = if key = (false, true, false) then 100 else 0 := by
  change Entitlement.Duty.quantity (window seed) key = _
  apply a_singleton_source_scope_retains_its_entire_original_quantity _ _ gross_scope
  rw [gross_quantity]
  norm_num

theorem live_roster : seed.current.members = [false, true] := by decide +kernel

private abbrev account := (Financial.Installation.Cursor.next input (Financial.Installation.Runtime.cursorAt input 0 19)).account

private theorem live_native_account : Evolution.Ingress.Joint.Background.account seed = account := by
  have source := Evolution.Ingress.Joint.Background.the_actual_cursor_is_the_original_next_cursor seed
  change Evolution.Ingress.Joint.Background.cursor seed =
    Financial.Installation.Cursor.next input (original.cursor input) at source
  rw [cursor_eq] at source
  exact congrArg (fun cursor => cursor.account) source

private theorem slot_count : account.current.slots.length = 1 := by decide +kernel
private def slot := account.current.slots.get ⟨0, by rw [slot_count]; decide⟩

private theorem one_slot {α : Type} (entries : List α) (count : entries.length = 1) (bound : 0 < entries.length) :
    entries = [entries.get ⟨0, bound⟩] := by
  cases entries with
  | nil => cases count
  | cons first rest =>
    cases rest with
    | nil => rfl
    | cons next rest => simp only [List.length_cons] at count; omega

private theorem exact_slot : account.current.slots = [slot] :=
  one_slot _ slot_count _

private theorem slot_balance : Financial.slotBalance input slot = Finsupp.single true 1 := by
  ext actor
  cases actor with
  | false => rw [Finsupp.single_eq_of_ne (by decide : false ≠ true)]; decide +kernel
  | true => rw [Finsupp.single_eq_same]; decide +kernel

private theorem slot_debtor : (Financial.slotClaim input slot).debtor = false := by decide +kernel

private theorem legacy_balance (slot : ResponsibilityLifecycle.ObligationSlot (Financial.vocabulary input)) :
    Epoch.Finance.slotBalance input 0 19 (Epoch.Finance.Legacy.slot input 0 19 slot) = Financial.slotBalance input slot := by
  cases slot <;> rfl

private theorem legacy_claim (slot : ResponsibilityLifecycle.ObligationSlot (Financial.vocabulary input)) :
    Epoch.Finance.slotClaim input 0 19 (Epoch.Finance.Legacy.slot input 0 19 slot) = .inl (Financial.slotClaim input slot) := by
  cases slot <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem original_financial_tail : Evolution.Ingress.Joint.Settlement.word seed =
    [⟨false, [], .ordinary false, [], .settle () false true 1⟩] := by
  unfold Evolution.Ingress.Joint.Settlement.word Evolution.Ingress.Joint.Settlement.wordFrom
    Evolution.Ingress.Joint.Background.nativeAccount
  rw [Epoch.Finance.Legacy.generated_current]
  rw [live_native_account]
  simp only [seed, Epoch.Finance.Legacy.state]
  rw [exact_slot]
  simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [legacy_balance, slot_balance]
  rw [Finsupp.support_single true (by norm_num : (1 : ℚ) ≠ 0)]
  simp only [Finset.toList_singleton, List.filterMap_cons, List.filterMap_nil]
  norm_num only [Finsupp.single_eq_same, if_pos, zero_lt_one]
  simp only [Evolution.Ingress.Joint.Settlement.request, legacy_claim, legacy_balance, slot_balance,
    Epoch.Finance.Claim.debtor, Epoch.Finance.Claim.instrument, slot_debtor, Finsupp.single_eq_same]
  have instrument : (Financial.slotClaim input slot).instrument = () := Subsingleton.elim _ _
  rw [instrument]
  change ([⟨false, [], (actualLaw seed).issuerPort (), [], .settle () false true 1⟩] : List Req) = _
  rw [physical_law]
  rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Installed
