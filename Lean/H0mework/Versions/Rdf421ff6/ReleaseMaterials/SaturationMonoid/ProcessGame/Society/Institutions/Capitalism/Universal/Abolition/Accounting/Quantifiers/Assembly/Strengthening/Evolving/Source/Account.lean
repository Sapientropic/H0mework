import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Source.Complete
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Finance

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

variable (reader : Macro.Raw.Reader seed.input seed.depth seed.count)



attribute [local irreducible] NativeCurrent.advance NativeCurrent.selected

/-- The witness is the original live native account, before invoking the new
body. Both readouts and the generated successor factor through that GS. -/
theorem the_first_actual_body_keeps_the_already_completed_financial_account :
    ∃ originalGS : type_of% (NativeCurrent.nativeGS (initial seed claim enough reader)),
      originalGS = NativeCurrent.nativeGS (initial seed claim enough reader) ∧
      HEq originalGS (Execution.Selected.after seed claim) ∧
      HEq (NativeCurrent.nativeGS (NativeCurrent.advance (initial seed claim enough reader))) originalGS :=
  ⟨NativeCurrent.nativeGS (initial seed claim enough reader),rfl,
    initial_account_heq seed claim enough reader,
    NativeCurrent.raw_next_keeps_the_literal_native_GS (initial seed claim enough reader)
      (the_completed_source_has_no_pending_native_work seed claim enough reader)⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Source
