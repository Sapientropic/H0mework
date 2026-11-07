import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Closure.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion.Complete

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Total

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program Innovation
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
open Evolution.Ingress.Joint Evolution.Ingress.Joint.Material

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

structure ActualFiniteCapitalClosedAt : Prop extends Completion.CapitalQuantifiersClosedAt seed claim where
  clears_every_actual_descendant : ∀ (enough : Quantifiers.Joint.Planning.Enough seed claim (shared seed claim))
    (reader : Macro.Raw.Reader seed.input seed.depth seed.count) (n : Nat)
    (resources : Closure.Resources (Closure.Source.current seed claim enough reader n)
      (Closure.Source.source_shape seed claim enough reader n)),
    Closure.CompleteAt (Closure.Source.current seed claim enough reader n)
      (Closure.Source.source_shape seed claim enough reader n) resources

theorem the_original_root_closes_its_quantifiers_and_clears_every_actual_native_descendant :
    ActualFiniteCapitalClosedAt seed claim where
  toCapitalQuantifiersClosedAt := Completion.the_original_root_closes_all_capital_quantifiers_and_generates_its_dynamic_future seed claim
  clears_every_actual_descendant := fun enough reader n resources =>
    Closure.Source.every_actual_descendant_clears_its_whole_native_ledger_in_a_source_finite_bound
      seed claim enough reader n resources

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Total
