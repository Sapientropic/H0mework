import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Source.Cursor

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Consumers

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

/-- The free native constructor alone cannot justify a per-origin bound.
The actual source folds, rather than this API, supply nonrepetition. -/
theorem two_free_admissions_really_do_duplicate_the_same_origin
    (claim : Epoch.Finance.Claim input depth count) :
    ¬ (((((NativeResponsibilityProcess.GeneratedState.initial (Epoch.Finance.process input depth count)).step
      (Epoch.Finance.process input depth count) (.admit claim)).step
      (Epoch.Finance.process input depth count) (.admit claim)).current.slots.map
        (fun slot => (Epoch.Finance.slotClaim input depth count slot).origin input depth count))).Nodup := by
  cases claim with
  | inl original =>
      change ¬ [Epoch.Finance.Origin.original original.origin,
        (Epoch.Finance.Origin.original original.origin : Epoch.Finance.Origin input depth count)].Nodup
      simp only [List.nodup_cons,List.mem_singleton,not_true_eq_false,false_and,not_false_eq_true]
  | inr actual =>
      change ¬ [Epoch.Finance.Origin.epoch actual.origin,
        (Epoch.Finance.Origin.epoch actual.origin : Epoch.Finance.Origin input depth count)].Nodup
      simp only [List.nodup_cons,List.mem_singleton,not_true_eq_false,false_and,not_false_eq_true]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Contribution.Consumers
