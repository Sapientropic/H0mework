import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Native.Complete
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Continuation.Installed
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource.Position

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Countermodels.Nonattainment
noncomputable section

@[irreducible] def originalWorld := Epoch.Finance.Future.world input 0 0
  (Epoch.Finance.Future.Installed.base input 0 0 0 0)
  (Epoch.Finance.Future.Installed.initial input 0 0 0 0) Native.prefixRun

@[irreducible] def family : Epoch.Finance.Future.Continuation.AccountFamily input 0 0 originalWorld Native.originalAccount := by
  unfold originalWorld
  exact Epoch.Finance.Future.Installed.accountFamily input 0 0 0 0 Native.prefixRun Native.originalAccount ⟨.nil⟩

def firstStart (n : Nat) :=
  Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.start initialHistory (upgrade n)

def frame (n : Nat) := Public.Frame.ordinary input 0 0 0 0 [] (firstStart n) family

theorem the_root_starts_with_the_literal_original_account (n : Nat) :
    (Canonical.visit input family (firstStart n)).current.account = Native.originalAccount := rfl

theorem the_root_keeps_the_original_physical_history (n : Nat) : (firstStart n).past = initialHistory := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
