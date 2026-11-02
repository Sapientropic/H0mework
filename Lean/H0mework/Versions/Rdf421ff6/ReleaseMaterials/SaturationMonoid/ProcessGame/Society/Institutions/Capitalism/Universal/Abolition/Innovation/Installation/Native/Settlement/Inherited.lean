import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Bootstrap.AccountInitial

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Inherited

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

def originalSlots := (Financial.Installation.Runtime.cursorAt input 0 count).account.current.slots.map
  (Epoch.Finance.Legacy.slot input 0 count)

def originalOwner? : Option (AdmittedObligation (Epoch.Finance.vocabulary input 0 count)) :=
  match originalSlots with
  | [.live obligation] => some obligation
  | _ => none

set_option maxHeartbeats 800000 in
private theorem original_found : originalOwner?.isSome = true := by
  with_unfolding_all decide +kernel

def originalOwner := originalOwner?.get original_found

theorem the_original_inherited_slot_is_the_same_live_owner_debt : originalSlots = [.live originalOwner] := by
  have returned : originalOwner? = some originalOwner := (Option.some_get original_found).symm
  unfold originalOwner? at returned
  split at returned
  · rename_i obligation source
    cases Option.some.inj returned
    exact source
  · cases returned

set_option maxHeartbeats 800000 in
theorem the_original_owner_keeps_its_exact_debtor_holder_and_residual :
    Epoch.Finance.Claim.debtor input 0 count originalOwner.content = 0 ∧
      Epoch.Finance.Claim.holder input 0 count originalOwner.content = 2 ∧
      originalOwner.residual = Finsupp.single (2 : Party) (1 : ℚ) := by
  constructor
  · with_unfolding_all rfl
  constructor
  · with_unfolding_all rfl
  · with_unfolding_all exact Financial.initialShare_eq_single input 2 1

theorem the_actual_root_starts_with_that_literal_inherited_native_slot (nature : RequestAt) :
    (actualPublicVisit nature 0).account.current.slots = [.live originalOwner] :=
  (the_first_actual_public_slots_are_the_original_pure_financial_cursor nature).trans
    the_original_inherited_slot_is_the_same_live_owner_debt

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Inherited
