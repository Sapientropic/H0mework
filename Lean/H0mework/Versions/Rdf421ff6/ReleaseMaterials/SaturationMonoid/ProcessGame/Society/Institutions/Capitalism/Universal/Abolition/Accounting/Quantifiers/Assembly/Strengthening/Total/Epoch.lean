import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Total.Finite
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Total.Epoch.AfterClearing
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Source.Initial
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Parameters
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion.Complete

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Total

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program Innovation
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
open Evolution Evolution.Ingress.Joint Evolution.Ingress.Joint.Material

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

structure ActualEpochCapitalClosedAt : Prop extends ActualFiniteCapitalClosedAt seed claim where
  original_native_account : ∀ (enough : Quantifiers.Joint.Planning.Enough seed claim (shared seed claim))
    (reader : Macro.Raw.Reader seed.input seed.depth seed.count),
    type_of% (Evolving.Epoch.Source.initial_native_account_is_literal
      (Evolving.Source.initial seed claim enough reader))
  every_actual_epoch : ∀ (enough : Quantifiers.Joint.Planning.Enough seed claim (shared seed claim))
    (reader : Macro.Raw.Reader seed.input seed.depth seed.count) (n : Nat),
    Evolving.Epoch.Current.ClosedAt (Evolving.Epoch.History.currentAt
      (Evolving.Epoch.Source.initial (Evolving.Source.initial seed claim enough reader)) n)
  original_source_parameters : ∀ (enough : Quantifiers.Joint.Planning.Enough seed claim (shared seed claim))
    (reader : Macro.Raw.Reader seed.input seed.depth seed.count) (n : Nat),
    type_of% (Evolving.Epoch.History.parameters
      (Evolving.Epoch.Source.initial (Evolving.Source.initial seed claim enough reader)) n)
  no_capital_regeneration : ∀ (enough : Quantifiers.Joint.Planning.Enough seed claim (shared seed claim))
    (reader : Macro.Raw.Reader seed.input seed.depth seed.count) (n : Nat),
    Global.NoCapital (Evolving.Epoch.History.currentAt
      (Evolving.Epoch.Source.initial (Evolving.Source.initial seed claim enough reader)) n).native.handlerFace.rootRead
  every_clearing_endpoint : ∀ {input : ProgrammeSource.Input Party Good Port Technology Instrument} {depth count : Nat}
    {fallback : Macro.Raw.Reader input depth count} (source : Clearing.Position input depth count fallback)
    (binding : Evolving.Epoch.Binding source.native)
    (resources : Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ArchiveNative.Conditions
      input depth count (Clearing.Deployment.history source) (Clearing.Deployment.before source)),
    ActualEpochAfterClearingAt source binding resources

theorem the_original_capital_root_retains_its_whole_ledger_through_every_actual_epoch :
    ActualEpochCapitalClosedAt seed claim where
  toActualFiniteCapitalClosedAt :=
    the_original_root_closes_its_quantifiers_and_clears_every_actual_native_descendant seed claim
  original_native_account := fun enough reader => Evolving.Epoch.Source.initial_native_account_is_literal
    (Evolving.Source.initial seed claim enough reader)
  every_actual_epoch := fun enough reader n =>
    Evolving.Epoch.History.every_actual_epoch_reads_its_live_control_and_closes_its_whole_ledger
      (Evolving.Epoch.Source.initial (Evolving.Source.initial seed claim enough reader)) n
  original_source_parameters := fun enough reader n => Evolving.Epoch.History.parameters
    (Evolving.Epoch.Source.initial (Evolving.Source.initial seed claim enough reader)) n
  no_capital_regeneration := fun enough reader n =>
    Evolving.NativeCurrent.the_actual_root_interpreter_excludes_every_capital_relation
      (Evolving.Epoch.History.currentAt
        (Evolving.Epoch.Source.initial (Evolving.Source.initial seed claim enough reader)) n).native
  every_clearing_endpoint := fun source binding resources =>
    the_original_whole_clearing_resumes_its_same_actual_legal_epoch source binding resources

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Total
