import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Native.Family
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Drain.Fold

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Native
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
open Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive
  (accountAfter tag visit oneItems events actualNativeRun)
noncomputable section

theorem the_original_sequential_account_is_its_ordered_actual_item_fold
    (history : List (Compile.RawInput Bool Bool Unit Nat Unit)) (requests : RawEvent Bool Bool Unit Nat Unit)
    (inherited : finance.GeneratedState) :
    accountAfter input 0 0 history requests inherited =
      (events input 0 0 history requests).foldl
        (fun state item => (Abolition.Root.Epoch.Finance.consume input 0 0 item state).next input 0 0) inherited := by
  induction requests generalizing history inherited with
  | nil => rfl
  | cons instruction tail later =>
      change accountAfter input 0 0 (history ++ [.primitive instruction]) tail
          (Abolition.Root.Epoch.Finance.consumeVisit input 0 0 (tag input 0 0 history instruction) (visit input 0 0 history instruction) inherited) = _
      rw [Evolution.Ingress.Joint.Material.Runtime.Drain.the_original_financial_consumption_is_its_same_ordered_fold]
      rw [later]
      simp only [events,List.foldl_append]
      rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Native
