import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Epoch.Consumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Actual

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.EpochHistory.Actual

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Innovation.Installation

noncomputable section

theorem every_original_innovation_public_visit_has_unique_contribution_origins (nature : RequestAt) (stage : Nat) :
    (origins input 0 count (actualPublicVisit nature stage).account).Nodup := by
  rw [Native.Settlement.every_actual_public_visit_is_its_original_source_account]
  exact the_registered_public_account_cannot_reregister_an_original_contribution input 0 count 0 0 0 count _ _

theorem every_original_innovation_public_suffix_bounds_the_whole_original_contribution
    (nature : RequestAt) (stage : Nat) (further : List InputAt)
    (index : Fin (actualPublicVisit nature stage).account.current.slots.length) :
    Source.receivedForOrigin input 0 count
      (Epoch.Finance.PublicPast.runFrom input 0 count 0 0 (firstOrigin nature).germ.snapshot.past
        (actualPublicVisit nature stage).snapshot.past further (actualPublicVisit nature stage).account)
      ((Epoch.Finance.slotClaim input 0 count ((actualPublicVisit nature stage).account.current.slots.get index)).origin input 0 count) ≤
      (Epoch.Finance.slotClaim input 0 count ((actualPublicVisit nature stage).account.current.slots.get index)).quantity input 0 count := by
  have source := Native.Settlement.every_actual_public_visit_is_its_original_source_account nature stage
  have inherited := congrArg (Epoch.Finance.PublicPast.foldFrom input 0 count 0 0
    (firstOrigin nature).germ.snapshot.past (actualPublicVisit nature stage).snapshot.past further) source
  have split := the_public_source_fold_splits_at_its_actual_prefix input 0 count 0 0
    (firstOrigin nature).germ.snapshot.past [] (actualPublicVisit nature stage).snapshot.past further
    (registeredBase input 0 count 0 count)
  simp only [List.nil_append] at split
  have target := inherited.trans split.symm
  have generated := the_registered_public_account_cannot_reregister_an_original_contribution input 0 count 0 0 0 count
    (firstOrigin nature).germ.snapshot.past ((actualPublicVisit nature stage).snapshot.past ++ further)
  have unique := (congrArg (fun account : (Epoch.Finance.process input 0 count).GeneratedState =>
    (origins input 0 count account).Nodup) target).mpr generated
  exact Source.a_source_unique_account_lifts_the_original_slot_bound input 0 count _ _ index unique

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.EpochHistory.Actual
