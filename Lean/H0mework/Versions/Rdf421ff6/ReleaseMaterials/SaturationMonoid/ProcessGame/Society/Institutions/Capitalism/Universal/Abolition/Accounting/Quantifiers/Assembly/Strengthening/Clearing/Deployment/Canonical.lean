import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Deployment.Root
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Source.Current

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Deployment.Canonical

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation Evolution Evolution.Ingress.Joint Evolution.Ingress.Joint.Material
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

attribute [local irreducible] Execution.Selected.items Joint.Planning.selected Joint.Planning.actualNext Joint.Current.advance

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Joint.window seed))
  (enough : Joint.Planning.Enough seed claim (shared seed claim))
  (reader : Macro.Raw.Reader seed.input seed.depth seed.count)

def original : Position seed.input seed.depth seed.count reader where
  start := (Evolving.Source.initial seed claim enough reader).start
  frame := (Evolving.Source.initial seed claim enough reader).frame
  visit := (Evolving.Source.initial seed claim enough reader).visit
  actual := (Evolving.Source.initial seed claim enough reader).actual
  paid := (Evolving.Source.initial seed claim enough reader).bodyPaid
  authority := (Evolving.Source.initial seed claim enough reader).authority
  rows := (Evolving.Source.initial seed claim enough reader).rows
  ready := Evolving.Source.initial_has_no_pending_native_work seed claim enough reader

theorem the_entry_is_the_original_completed_runtime :
    (original seed claim enough reader).native = Evolving.Source.initial seed claim enough reader := rfl

theorem the_entry_keeps_the_literal_original_native_account :
    (original seed claim enough reader).actual.actual.account =
      (Runtime.Resumption.completedActual seed claim enough).actual.account := rfl

theorem the_original_completed_runtime_really_consumes_the_generic_full_ledger_producer
    (resources : Runtime.Retirement.CompleteLedger.ArchiveNative.Conditions seed.input seed.depth seed.count
      (Deployment.history (original seed claim enough reader)) (Deployment.before (original seed claim enough reader))) :
    CompleteAt (original seed claim enough reader) resources :=
  the_original_current_clears_its_entire_native_ledger_and_continues _ resources

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Deployment.Canonical
