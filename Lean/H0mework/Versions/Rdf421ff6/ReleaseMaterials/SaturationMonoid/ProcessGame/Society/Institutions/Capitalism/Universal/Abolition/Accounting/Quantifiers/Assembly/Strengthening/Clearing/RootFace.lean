import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.PositionStep
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Handler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Evolving.NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

def nativeAccountFace : SourceNativeRootSemanticFaceAt current.full.root current.visit where
  projection := .component Public.Inquiry.Projection.nativeAccount
  active := current.actual
  classifier_eq := Public.Inquiry.the_unique_source_active_is_selected current.frame .nativeAccount _ current.actual

theorem the_financial_readout_is_the_same_current_root_account :
    (nativeAccountFace current).rootRead = current.actual.actual.account := rfl

theorem the_ready_root_really_compiles_its_next_raw_action
    (ready : ¬ Public.Inquiry.HasWork current.frame current.actual.actual) :
    (Factory.Direct.state current.frame current.reader current.visit current.actual current.authority).compileInquiry PUnit.unit =
      .actualAction (Factory.Direct.rawCore current.frame current.reader current.visit current.actual current.authority ready) := by
  change Factory.Direct.compileUnit current.frame current.reader current.visit current.actual current.authority = _
  unfold Factory.Direct.compileUnit
  rw [dif_neg ready]
  rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing
