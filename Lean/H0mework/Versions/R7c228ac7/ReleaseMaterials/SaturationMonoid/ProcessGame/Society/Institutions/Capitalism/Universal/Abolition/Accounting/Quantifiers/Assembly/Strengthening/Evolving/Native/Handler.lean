import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Current

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Evolution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

namespace NativeCurrent
variable (current : NativeCurrent (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))


/-- The active interpreter is read from the fresh query coface of this exact
root occurrence, rather than inferred from a package field. -/
def handlerFace : SourceNativeRootSemanticFaceAt (full current).root current.visit where
  projection := .component Public.Inquiry.Projection.publicLaw
  active := current.actual
  classifier_eq := Public.Inquiry.the_unique_source_active_is_selected current.frame .publicLaw _ current.actual

theorem handlerFace_reads_the_actual_handler : (handlerFace current).rootRead = handlerLaw current := rfl

theorem the_actual_root_interpreter_excludes_every_capital_relation : Global.NoCapital (handlerFace current).rootRead :=
  Global.publicLawNoCapital _

end NativeCurrent
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving
