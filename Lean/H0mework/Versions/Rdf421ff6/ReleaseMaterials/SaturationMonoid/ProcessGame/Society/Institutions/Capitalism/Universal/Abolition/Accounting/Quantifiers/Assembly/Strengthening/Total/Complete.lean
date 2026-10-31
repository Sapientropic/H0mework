import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Total.Epoch
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Total.Cofinal

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

/-- The original quantifier theorem, actual native clearing and legal epochs,
and the whole-ledger compiler for any source-emitted cofinal occurrence. -/
structure CapitalLineStrengthenedAt : Prop extends ActualEpochCapitalClosedAt seed claim where
  every_source_cofinal_registration : ∀ {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    (root : SourceNativeLivingRootClosure N V)
    (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot),
    ActualCofinalRegistrationClosedAt root boundary

theorem the_original_root_closes_the_full_strengthened_capital_quantifiers :
    CapitalLineStrengthenedAt seed claim where
  toActualEpochCapitalClosedAt :=
    the_original_capital_root_retains_its_whole_ledger_through_every_actual_epoch seed claim
  every_source_cofinal_registration := fun root boundary =>
    the_original_cofinal_event_generates_its_whole_registration_or_exact_refusal root boundary

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Total
