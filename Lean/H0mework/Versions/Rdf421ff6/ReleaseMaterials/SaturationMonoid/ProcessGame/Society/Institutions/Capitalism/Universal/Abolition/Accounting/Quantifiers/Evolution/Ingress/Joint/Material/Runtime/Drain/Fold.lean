import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Fold

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Drain

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

theorem the_original_financial_consumption_is_its_same_ordered_fold
    (tag : Epoch.Interface.Tag input depth count) (visit : Epoch.Interface.Visit input depth count tag)
    (before : (Epoch.Finance.process input depth count).GeneratedState) :
    Epoch.Finance.consumeVisit input depth count tag visit before =
      (Epoch.Finance.inventory input depth count tag visit).foldl
        (fun state item => (Epoch.Finance.consume input depth count item state).next input depth count) before := by
  unfold Epoch.Finance.consumeVisit
  generalize Epoch.Finance.inventory input depth count tag visit = items
  induction items generalizing before with
  | nil => rfl
  | cons item rest later => exact later ((Epoch.Finance.consume input depth count item before).next input depth count)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Drain
