import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Control
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Current

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

structure Binding (native : NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) : Type 4 where
  value : Control (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
  faceAt : (visit : SourceNativeTemporalVisitAt native.full.root.toAuthoritativeRoot.toLedgerRoot) →
    (actual : Public.Inquiry.ActualAt native.frame visit.current) → (paid : actual.actual.bodyPaid = true) →
    SourceNativeRootSemanticFaceAt native.full.root visit
  typeAt : ∀ visit actual paid, (faceAt visit actual paid).Restriction =
    Control (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
  readAt : ∀ visit actual paid, cast (typeAt visit actual paid) (faceAt visit actual paid).rootRead = value

structure Current : Type 4 where
  native : NativeCurrent (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
  binding : Binding native

namespace Current
variable (current : Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))

def controlFace := current.binding.faceAt current.native.visit current.native.actual current.native.bodyPaid

def control : Control (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
  cast (current.binding.typeAt current.native.visit current.native.actual current.native.bodyPaid) current.controlFace.rootRead

theorem control_is_the_actual_root_coordinate : current.control = current.binding.value :=
  current.binding.readAt _ _ _

end Current
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch
