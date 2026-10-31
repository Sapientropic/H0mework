import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Current
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Resumption.Completed

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld DebtActivationLedger
open Source.Program Innovation Quantifiers.Joint Evolution Evolution.Ingress.Joint Evolution.Ingress.Joint.Material
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

attribute [local irreducible] Execution.Selected.items Planning.selected Planning.actualNext Current.advance

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))
  (enough : Planning.Enough seed claim (Material.shared seed claim))

local notation "F" => Runtime.Resumption.nativeFrame seed claim enough
local notation "visit₀" => Runtime.Resumption.completedVisit seed claim
local notation "actual₀" => Runtime.Resumption.completedActual seed claim enough

def rowsOnAccount
    (account : (Epoch.Finance.process seed.input seed.depth seed.count).GeneratedState)
    (tail : Epoch.Finance.Future.Continuation.NativeTail seed.input seed.depth seed.count
      (Background.nativeAccount seed) account) :
    PaidRowsAt (Admission.N seed claim) ((Runtime.Resumption.family seed claim enough).support account tail) where
  productive := oldEntry (law := Gross.law seed claim) (state? := some (Runtime.Resumption.paidState seed claim))
    (debtEntry (N := Background.world seed) (law := Productive.law seed claim)
      ((Background.family seed).support account tail) (.current (Runtime.Resumption.paidState seed claim)))
  gross := debtEntry (N := ExtendedNetwork (Background.world seed) (Productive.law seed claim)) (law := Gross.law seed claim)
    (((Background.family seed).support account tail),some (.current (Runtime.Resumption.paidState seed claim)))
      (Runtime.Resumption.paidState seed claim)
  productive_zero := (Runtime.Resumption.the_fixed_historical_rows_have_no_remaining_budget seed claim enough).1
  gross_zero := (Runtime.Resumption.the_fixed_historical_rows_have_no_remaining_budget seed claim enough).2
  different_claims := by intro impossible; cases impossible

/-- Both views are read at the actually completed native cursor, never at the
pre-payment seed or a backwards Productive projection. -/
def initialRows : PaidRowsAt (F).N ((F).sourceSupport (visit₀).current) := by
  change PaidRowsAt (F).N ((F).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
    ((F).root.emitted (visit₀).current))
  rw [(F).support_exact (visit₀).current (actual₀).actual (actual₀).aligned]
  exact rowsOnAccount seed claim enough (actual₀).actual.account (actual₀).actual.native

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Source
