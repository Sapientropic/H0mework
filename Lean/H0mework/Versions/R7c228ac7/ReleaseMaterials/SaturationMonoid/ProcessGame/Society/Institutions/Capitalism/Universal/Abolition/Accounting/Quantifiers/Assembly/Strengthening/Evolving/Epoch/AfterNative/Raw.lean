import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.AfterNative.Reader
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Raw

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Current

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

variable (complete : ¬ Public.Inquiry.HasWork current.native.frame current.native.actual.actual)

/-- A native subsystem may execute its own original query grammar. Its raw
write freezes the source control restriction and does not consume meta code. -/
def nativeRawFace (visit : SourceNativeTemporalVisitAt (current.native.raw complete).full.root.toAuthoritativeRoot.toLedgerRoot) :
    SourceNativeRootSemanticFaceAt (current.native.raw complete).full.root visit where
  projection := Factory.Direct.oldProjection current.native.full current.native.sourceActual current.native.reader current.controlFace.projection
  active := current.controlFace.active
  classifier_eq := current.controlFace.classifier_eq

def afterNativeRaw : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) where
  native := current.native.raw complete
  binding := {
    value := current.binding.value
    faceAt := fun visit _ _ => nativeRawFace current complete visit
    typeAt := fun _ _ _ => current.binding.typeAt current.native.visit current.native.actual current.native.bodyPaid
    readAt := fun _ _ _ => current.binding.readAt current.native.visit current.native.actual current.native.bodyPaid }

def afterNativePrimitive := (afterNativeRaw current complete).ordinary

theorem afterNativePrimitive_is_the_original_two_native_writes :
    (afterNativePrimitive current complete).native = (current.native.raw complete).ordinary := rfl

theorem the_source_control_is_inherited_through_native_execution :
    (afterNativePrimitive current complete).control = current.control := by
  rw [control_is_the_actual_root_coordinate,control_is_the_actual_root_coordinate]
  rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Current
