import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable.Source

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable

open Capitalism.Universal.Source.Program Capitalism.Universal.Root Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Accounting Capitalism.Universal.Abolition.Accounting.Quantifiers Joint
open Capitalism.Universal.Abolition.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Installed (Raw releasedTech)

noncomputable section

def shared := Current.declareGross seed grossClaim (Current.initial seed grossClaim)

def snapshot : Raw where
  stock := fun person good => if good then if person then 3 else 2 else if person then 100 else 0
  claims := fun _ _ _ => 0
  technology := releasedTech
  clock := 3
  round := 3

private def recorded := law.next mechanism.code.initial originalWord
private def declared := Responsibility.Family.State.declare productiveClaim
  (Responsibility.Family.State.atCursor productiveClaim recorded)

private theorem original_raw : (Accounting.Root.Source.initialState input original.native visit productiveClaim).raw = recorded := by
  have actual := Financial.Installation.Cursor.last_execution_returns_actual_physical_current input (original.native.cursor visit.current)
  change ProgrammeSource.rawCurrent input (Financial.Installation.Cursor.physicalVisit input
    (Financial.Installation.Cursor.next input (original.native.cursor visit.current))).current = _
  rw [← actual, ← origin.law, ← origin.before, ← origin.word]
  rfl

private theorem declared_original :
    Accounting.Root.Source.declared input original.native visit productiveClaim = declared :=
  congrArg (fun raw => Responsibility.Family.State.declare productiveClaim
    (Responsibility.Family.State.atCursor productiveClaim raw)) original_raw

private theorem productive_original : productiveState seed =
    Responsibility.Family.State.advance productiveClaim declared (PublicFunction.physicalLaw law) [] := by
  unfold productiveState Global.Seed.current seed
  rw [Priority.Root.afterInputs, Completion.current_family_is_the_actual_observed_row]
  change Accounting.Root.Source.observed input original.native visit productiveClaim [] = _
  unfold Accounting.Root.Source.observed
  rw [declared_original]
  rfl

theorem shared_raw : shared.raw = snapshot := by
  change (productiveState seed).raw = snapshot
  rw [productive_original]
  change (PublicFunction.physicalLaw law).next recorded [] = _
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;> decide +kernel
  · funext code debtor creditor
    cases code
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

theorem productive_scope :
    Responsibility.Family.positiveScope mechanism Installed.past nature Installed.response = [(false, false)] := by
  decide +kernel

theorem gross_declared : shared.grossDeclared = true := rfl

theorem gross_scope : Entitlement.Duty.scope (window seed) = [(false, true, false)] := by
  have calculated := congrArg (fun rows => (rows.map Prod.fst).dedup) original_gross_cells
  change _ = [(false, true, false)].dedup
  simpa only [Entitlement.Duty.scope, List.map_map, Function.comp_def, List.map_cons, List.map_nil]
    using calculated

theorem gross_balance (key : Bool × Bool × Bool) :
    shared.gross key = if key = (false, true, false) then 100 else 0 := by
  change Entitlement.Duty.quantity (window seed) key = _
  apply a_singleton_source_scope_retains_its_entire_original_quantity _ _ gross_scope
  rw [gross_quantity]
  norm_num

theorem live_roster : seed.current.members = [false, true] := by decide +kernel

theorem physical_law : actualLaw seed = PublicFunction.physicalLaw law := rfl

private theorem original_slots_empty :
    (Financial.Installation.Cursor.next input (Financial.Installation.Runtime.cursorAt input 0 count)).account.current.slots = [] := by
  apply List.length_eq_zero_iff.mp
  decide +kernel

theorem original_financial_tail : Evolution.Ingress.Joint.Settlement.word seed = [] := by
  have cursor := Evolution.Ingress.Joint.Background.the_actual_cursor_is_the_original_next_cursor seed
  change Evolution.Ingress.Joint.Background.cursor seed = Financial.Installation.Cursor.next input (original.cursor input) at cursor
  rw [cursor_eq] at cursor
  have originalAccount : Evolution.Ingress.Joint.Background.account seed =
      (Financial.Installation.Cursor.next input (Financial.Installation.Runtime.cursorAt input 0 count)).account :=
    congrArg (fun state => state.account) cursor
  unfold Evolution.Ingress.Joint.Settlement.word Evolution.Ingress.Joint.Settlement.wordFrom
    Evolution.Ingress.Joint.Background.nativeAccount
  rw [Epoch.Finance.Legacy.generated_current, originalAccount]
  simp only [seed, Epoch.Finance.Legacy.state, original_slots_empty, List.map_nil, List.flatMap_nil]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable
