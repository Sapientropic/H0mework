import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Source.Read
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Birth

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

namespace Current

def ordinary : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) where
  native := current.native.ordinary
  binding := {
    value := current.binding.value
    faceAt := current.binding.faceAt
    typeAt := current.binding.typeAt
    readAt := current.binding.readAt }

variable (registered : Public.Accounting.Registration current.native.input current.native.depth current.native.count
  current.native.prefixLimit current.native.renewalLimit current.native.oldPast current.native.start current.native.actual.actual)

def bornFace (visit : SourceNativeTemporalVisitAt (current.native.birth registered).full.root.toAuthoritativeRoot.toLedgerRoot) :
    SourceNativeRootSemanticFaceAt (current.native.birth registered).full.root visit where
  projection := .inherited (.component current.controlFace.projection)
  active := current.controlFace.active
  classifier_eq := current.controlFace.classifier_eq

def birth : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) where
  native := current.native.birth registered
  binding := {
    value := current.binding.value
    faceAt := fun visit _ _ => bornFace current registered visit
    typeAt := fun _ _ _ => current.binding.typeAt current.native.visit current.native.actual current.native.bodyPaid
    readAt := fun _ _ _ => current.binding.readAt current.native.visit current.native.actual current.native.bodyPaid }

end Current
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch
