import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Advance

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Current

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

variable (reader : Macro.Raw.Reader current.native.input current.native.depth current.native.count)

/-- Source-owned query-code installation preserves the original active
control face, physical cut, complete account and sealed causal authority. -/
def queryNative : NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) where
  input := current.native.input
  depth := current.native.depth
  count := current.native.count
  prefixLimit := current.native.prefixLimit
  renewalLimit := current.native.renewalLimit
  oldPast := current.native.oldPast
  start := current.native.start
  frame := current.native.full
  reader := reader
  visit := current.native.visit
  actual := current.native.sourceActual
  bodyPaid := current.native.bodyPaid
  authority := current.native.authority.withProjectionCoface (Public.Inquiry.component current.native.full reader)
  rows := current.native.rows

def queryFace (visit : SourceNativeTemporalVisitAt (queryNative current reader).full.root.toAuthoritativeRoot.toLedgerRoot)
    (actual : Public.Inquiry.ActualAt (queryNative current reader).frame visit.current)
    (paid : actual.actual.bodyPaid = true) :
    SourceNativeRootSemanticFaceAt (queryNative current reader).full.root visit where
  projection := .inherited (current.binding.faceAt visit ⟨actual.actual,actual.aligned⟩ paid).projection
  active := (current.binding.faceAt visit ⟨actual.actual,actual.aligned⟩ paid).active
  classifier_eq := (current.binding.faceAt visit ⟨actual.actual,actual.aligned⟩ paid).classifier_eq

def requery : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) where
  native := queryNative current reader
  binding := {
    value := current.binding.value
    faceAt := queryFace current reader
    typeAt := fun visit actual paid => current.binding.typeAt visit ⟨actual.actual,actual.aligned⟩ paid
    readAt := fun visit actual paid => current.binding.readAt visit ⟨actual.actual,actual.aligned⟩ paid }

theorem requery_keeps_control_and_complete_account :
    (current.requery reader).control = current.control ∧
      (current.requery reader).native.actual.actual.account = current.native.actual.actual.account := by
  constructor
  · rw [control_is_the_actual_root_coordinate,control_is_the_actual_root_coordinate]
    rfl
  · rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Current
