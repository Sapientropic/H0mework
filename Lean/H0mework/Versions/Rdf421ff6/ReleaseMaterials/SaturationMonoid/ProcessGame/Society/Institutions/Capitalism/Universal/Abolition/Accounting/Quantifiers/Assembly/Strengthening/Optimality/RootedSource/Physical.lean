import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource.Initial
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource.RawStep

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger
open Countermodels.Nonattainment
noncomputable section

def history1 (n : Nat) := initialHistory ++ [.primitive (upgrade n)]
def history2 (n : Nat) := history1 n ++ [.primitive produce]
def history3 (n : Nat) := history2 n ++ [.primitive repay]

theorem the_first_physical_history_is_the_original_actual_upgrade (n : Nat) :
    Primitive.state input 0 0 (history1 n) = stage1 n := by
  change Physical.Public.stateAt input 0 0 0 0 [] (initialHistory ++ [.primitive (upgrade n)]) = _
  rw [Primitive.the_source_history_extends_by_this_same_primitive,
    ← Native.the_physical_cut_is_the_same_original_source_suffix]
  exact the_actual_upgrade_reaches_its_source_state n

theorem the_second_physical_history_is_the_original_actual_production (n : Nat) :
    Primitive.state input 0 0 (history2 n) = stage2 n := by
  change Physical.Public.stateAt input 0 0 0 0 [] (history1 n ++ [.primitive produce]) = _
  rw [Primitive.the_source_history_extends_by_this_same_primitive]
  change (Physical.Public.compile input (Primitive.state input 0 0 (history1 n)) (.primitive produce)).next = _
  rw [the_first_physical_history_is_the_original_actual_upgrade]
  exact the_actual_production_reaches_its_source_state n

theorem the_final_physical_history_is_the_original_actual_payment (n : Nat) :
    Primitive.state input 0 0 (history3 n) = stage3 n := by
  change Physical.Public.stateAt input 0 0 0 0 [] (history2 n ++ [.primitive repay]) = _
  rw [Primitive.the_source_history_extends_by_this_same_primitive]
  change (Physical.Public.compile input (Primitive.state input 0 0 (history2 n)) (.primitive repay)).next = _
  rw [the_second_physical_history_is_the_original_actual_production]
  exact the_actual_payment_reaches_its_source_state n

theorem the_final_history_is_the_same_original_programme (n : Nat) :
    history3 n = initialHistory ++ programme n := by
  simp only [history3,history2,history1,programme,word,List.map_cons,List.map_nil,List.append_assoc,
    List.cons_append,List.nil_append]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
