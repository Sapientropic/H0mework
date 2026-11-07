import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Source.Read

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Transition

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

def bare := Factory.Direct.recordedFrame current.native.full current.native.sourceActual current.executionReader
def phaseFrame := Source.phaseFrame (bare current) current.afterControl
def fullFrame := Public.Inquiry.installedFrame (phaseFrame current) current.native.reader
abbrev root := (fullFrame current).root
abbrev initial := (root current).toAuthoritativeRoot.toRoot.initialVisit

def first := (fullFrame current).successor (initial current).current

def firstVisit : SourceNativeTemporalVisitAt (root current).toAuthoritativeRoot.toLedgerRoot :=
  (SourceNativeTemporalVisitAt.finite (initial current)).next (first current).next_eq

theorem first_is_the_literal_body :
    (first current).targetCurrent = Factory.Direct.bodyNext current.native.full current.native.sourceActual :=
  Factory.Direct.first_target_is_the_actual_selected_body current.native.full current.native.sourceActual current.executionReader

def actual : Public.Inquiry.ActualAt (phaseFrame current) (first current).targetCurrent :=
  ⟨Factory.Direct.bodyNext current.native.full current.native.sourceActual,
    (first_is_the_literal_body current) ▸ rfl⟩

theorem first_body_is_paid : (actual current).actual.bodyPaid = true := rfl

theorem the_material_target_is_the_same_actual_public_result :
    Public.Accounting.physical current.native.input current.native.depth current.native.count current.native.prefixLimit
      current.native.renewalLimit current.native.oldPast
      (Factory.Direct.selectedStart current.native.full current.native.sourceActual current.executionReader)
      (actual current).actual = current.physicalResult.next :=
  Factory.Direct.the_new_body_is_the_current_readers_actual_public_result current.native.full current.native.sourceActual current.executionReader

theorem first_owns_the_generated_control :
    cast (Source.face_type (bare current) current.afterControl current.native.reader
      (firstVisit current) (actual current) (first_body_is_paid current))
      (Source.face (bare current) current.afterControl current.native.reader
        (firstVisit current) (actual current) (first_body_is_paid current)).rootRead =
      current.afterControl := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Transition
