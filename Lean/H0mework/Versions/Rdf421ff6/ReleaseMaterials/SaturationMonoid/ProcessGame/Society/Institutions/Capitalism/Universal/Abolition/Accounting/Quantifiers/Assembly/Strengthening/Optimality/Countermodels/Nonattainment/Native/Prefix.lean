import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Complete
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.Archives
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.Tail

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Native
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
open Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive
  (accountAfter tag visit oneItems events actualNativeRun)
noncomputable section

abbrev finance := Abolition.Root.Epoch.Finance.process input 0 0
def initialAccount := Abolition.Root.Epoch.Finance.inheritedAccount input 0 0
def originalAccount := accountAfter input 0 0 [] prefixWord initialAccount

def issueTag := tag input 0 0 [] issued
def issueVisit := visit input 0 0 [] issued
def issueItem : Abolition.Root.Epoch.Finance.ActualItem input 0 0 := ⟨issueTag,issueVisit,⟨0,by decide +kernel⟩⟩
private theorem found : (Abolition.Root.Epoch.Finance.readNewClaim input 0 0 issueItem).isSome = true := by decide +kernel
def originalClaim := (Abolition.Root.Epoch.Finance.readNewClaim input 0 0 issueItem).get found

theorem the_claim_is_owned_by_its_original_actual_item : originalClaim.origin = issueItem :=
  Abolition.Root.Epoch.Finance.readNewClaim_origin input 0 0 issueItem originalClaim (Option.some_get found).symm

theorem the_financial_source_is_the_original_public_physical_root :
    Abolition.Root.Epoch.Interface.ledgerRoot input 0 0 issueTag =
      Physical.Public.ledgerRoot input 0 0 0 0 []
        (Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.start [] issued) := rfl

def prefixRun : finance.Run initialAccount.current originalAccount.current := actualNativeRun input 0 0 [] prefixWord initialAccount

theorem original_debt_is_still_live_in_the_same_native_account :
    originalAccount.current.slots.length = 1 ∧
      Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ledgerClaims input 0 0 originalAccount.current () false true = 1 := by decide +kernel

theorem the_native_prefix_keeps_the_exact_original_claim :
    originalAccount.current.slots.map (Abolition.Root.Epoch.Finance.slotClaim input 0 0) = [.inr originalClaim] := by
  with_unfolding_all rfl

theorem the_physical_cut_is_the_same_original_source_suffix :
    before = Physical.Public.stateAt input 0 0 0 0 [] initialHistory :=
  Programme.the_comparison_programme_is_the_literal_original_source_suffix input initialHistory 0 0 0 0 [] []

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Native
