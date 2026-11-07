import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Transition.Target

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Transition

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

variable (complete : ¬ Public.Inquiry.HasWork current.native.frame current.native.actual.actual)

def visit := (generated current complete).target.targetVisit

theorem nextEntry_is_the_installed_source_row :
    (generated current complete).target.targetEntry =
      (fullFrame current).entry (visit current complete).current :=
  Factory.Direct.the_next_row_is_the_same_installed_entry current.native.full current.native.visit
    current.native.sourceActual current.executionReader

def nativeNext : NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) where
  input := current.native.input
  depth := current.native.depth
  count := current.native.count
  prefixLimit := current.native.prefixLimit
  renewalLimit := current.native.renewalLimit
  oldPast := current.native.oldPast
  start := Factory.Direct.selectedStart current.native.full current.native.sourceActual current.executionReader
  frame := phaseFrame current
  reader := current.native.reader
  visit := visit current complete
  actual := actual current
  bodyPaid := first_body_is_paid current
  authority := nextEntry_is_the_installed_source_row current complete ▸ (generated current complete).target.targetAuthority
  rows := afterSequential (generated current complete) current.native.rows

def next : Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) where
  native := nativeNext current complete
  binding := {
    value := current.afterControl
    faceAt := Source.face (bare current) current.afterControl current.native.reader
    typeAt := Source.face_type (bare current) current.afterControl current.native.reader
    readAt := Source.face_reads (bare current) current.afterControl current.native.reader }

theorem next_reads_the_written_control : (next current complete).control = current.afterControl :=
  (next current complete).control_is_the_actual_root_coordinate

theorem next_state_reads_the_same_actual_material_target :
    (next current complete).raw = current.physicalResult.next.raw :=
  congrArg (fun state => state.raw) (the_material_target_is_the_same_actual_public_result current)

theorem next_snapshot_keeps_the_one_actual_effective_input :
    (next current complete).native.actual.snapshot.past = current.native.actual.snapshot.past ++
      [Public.Scope.executionRaw current.native.input current.native.depth current.native.count current.native.prefixLimit
        current.native.renewalLimit current.native.oldPast current.native.actual.snapshot current.executionRaw] := rfl

theorem body_is_not_replayed_or_financially_reset :
    (nativeNext current complete).actual.actual.account = current.native.actual.actual.account ∧
      (nativeNext current complete).actual.actual.position = 0 ∧
      (nativeNext current complete).actual.actual.bodyPaid = true := ⟨rfl,rfl,rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Transition
