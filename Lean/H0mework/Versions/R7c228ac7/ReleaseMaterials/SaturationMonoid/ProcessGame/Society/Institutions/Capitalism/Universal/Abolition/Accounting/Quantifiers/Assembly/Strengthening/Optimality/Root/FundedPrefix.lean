import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Root.CommonPast
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Deployment.Canonical
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Complete

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Root

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program Innovation
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Evolution.Ingress.Joint Evolution.Ingress.Joint.Material
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))
  (enough : Quantifiers.Joint.Planning.Enough seed claim (shared seed claim))
  (reader : Macro.Raw.Reader seed.input seed.depth seed.count)

local notation "original" => Clearing.Deployment.Canonical.original seed claim enough reader

structure FundedOriginalTaskAt
    (resources : Runtime.Retirement.CompleteLedger.ArchiveNative.Conditions seed.input seed.depth seed.count
      (Clearing.Deployment.history original) (Clearing.Deployment.before original)) : Prop where
  actual_joint_root : Runtime.RootedJointPaymentAt seed claim
  original_needs_and_both_material_obligations_paid :
    type_of% ((Runtime.the_original_root_executes_its_joint_payment_and_complete_native_account seed claim).funded_original_payment enough)
  remaining_native_task : RootedNativeCostMinimumAt original resources
  complete_actual_cost_from_this_cut : ∀ reading rival,
    fullHistoryCost original reading (Cost.Canonical.programme original) ≤ fullHistoryCost original reading rival

/-- The real prefix paid the original P/G and both life/maintenance bills.
Its remaining native retirement is performed by the same root. -/
theorem the_real_paid_prefix_and_original_native_minimum_complete_one_source_task
    (resources : Runtime.Retirement.CompleteLedger.ArchiveNative.Conditions seed.input seed.depth seed.count
      (Clearing.Deployment.history original) (Clearing.Deployment.before original)) :
    FundedOriginalTaskAt seed claim enough reader resources where
  actual_joint_root := Runtime.the_original_root_executes_its_joint_payment_and_complete_native_account seed claim
  original_needs_and_both_material_obligations_paid :=
    (Runtime.the_original_root_executes_its_joint_payment_and_complete_native_account seed claim).funded_original_payment enough
  remaining_native_task := the_same_actual_root_attains_the_complete_native_retirement_minimum original resources
  complete_actual_cost_from_this_cut := the_actual_native_minimum_preserves_all_already_incurred_source_costs original

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Root
