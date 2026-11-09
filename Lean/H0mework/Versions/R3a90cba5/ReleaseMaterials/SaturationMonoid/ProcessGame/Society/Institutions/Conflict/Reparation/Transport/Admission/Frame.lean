import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.AdmissionShape
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Sequential

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Admission

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Root.Registered.Macro
open Public.Accounting.Born
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld DebtActivationLedger

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "Native" => Evolving.NativeCurrent (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

abbrev Registration (native : Native) := Public.Accounting.Registration native.input native.depth native.count
  native.prefixLimit native.renewalLimit native.oldPast native.start native.actual.actual

variable {law : DebtActivationLaw} {joint : WorldRelationNetwork}
  {native : Evolving.NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {shape : Shape law native.frame.N joint} {phase : law.DebtState} {wait : law.TransportAt phase phase}
  (current : Resident shape phase wait) (registered : Registration native)

abbrev finance := Public.Accounting.Born.law native.actual.actual registered
abbrev pending : (finance registered).DebtState := .pending
abbrev financialStep := Public.Accounting.Born.firstStep native.actual.actual registered
abbrev nextNative := native.birth registered
abbrev nextShape := shape.under (finance registered)

theorem original_birth_support :
    sourceSupport (nextNative registered) =
      (structuralTarget native, some (financialStep registered).target) := by
  let prior := native.frame.family
  let original := native.actual.actual
  let first := Source.firstSuccessor prior original registered
  have atTarget := congrArg (fun occurrence => occurrence.1)
    (Source.occurrence_eq_emitted prior original registered first.targetOccurrence)
  have joint := Action.first_support_is_the_same_source_admission native.full native.visit
    original native.actual.aligned registered
  have base := congrArg (fun occurrence => occurrence.1) (native.frame.target_occurrence native.visit.current)
  exact atTarget.symm.trans (joint.trans (congrArg (fun s => (s, some (financialStep registered).target)) base))

theorem joined_support :
    (shape.support (structuralTarget native) phase, some (financialStep registered).target) =
      (nextShape (shape := shape) registered).support (sourceSupport (nextNative registered)) phase :=
  (congrArg (fun s => (nextShape (shape := shape) registered).support s phase)
    (original_birth_support registered)).symm

abbrev held (_current : Resident shape phase wait) := heldWrite native shape phase wait native.visit.current
abbrev joined := Whole.jointStep (held current) (shape.repair (sourceSupport native) phase)
  (financialStep registered).step

def frame : Frame (nextNative registered) (nextShape (shape := shape) registered) phase where
  initialSupport := (current.support, some (pending registered))
  initialFinite := Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Finiteness.active_finite
    (pending registered) current.finite
  initialWrite := (joined current registered).rebase
    (congrArg (fun support => (support, some (pending registered))) current.support_eq.symm)
    (joined_support (shape := shape) (phase := phase) registered)
  writes := true

abbrev firstOwner := oldEntry (law := finance registered) (state? := some (pending registered)) current.entry

private theorem oldEntry_heq {N : WorldRelationNetwork} {F : DebtActivationLaw}
    {s t : N.Support} (same : s = t) (f : Option F.DebtState)
    (left : OpenResponsibilityAt N s) (right : OpenResponsibilityAt N t) (entries : HEq left right) :
    HEq (oldEntry (law := F) (state? := f) left) (oldEntry (law := F) (state? := f) right) := by
  cases same
  rw [eq_of_heq entries]

private theorem repair_reindex {N M : WorldRelationNetwork} {R : DebtActivationLaw}
    (view : Shape R N M) {a b : N.Support} (same : a = b) (r : R.DebtState) :
    HEq (view.repair a r) (view.repair b r) := by cases same; rfl

theorem firstOwner_lands_on_repair :
    ((frame current registered).initialWrite.val.destination (firstOwner current registered)).1 =
      (nextShape (shape := shape) registered).repair (sourceSupport (nextNative registered)) phase := by
  let stage := pending registered
  let initial := congrArg (fun support => (support, some stage)) current.support_eq.symm
  let last := joined_support (shape := shape) (phase := phase) registered
  let original := shape.repair (sourceSupport native) phase
  have sourceEq := oldEntry_heq (F := finance registered) current.support_eq (some stage)
    current.entry original current.repair_eq
  have wrote := destination_congr initial.symm last.symm
    (frame current registered).initialWrite.val (joined current registered).val
    (Whole.rebase_destination initial last (joined current registered))
    (firstOwner current registered) (oldEntry original) sourceEq
  have repair : ((joined current registered).val.destination (oldEntry original)).1 =
      oldEntry (shape.repair (structuralTarget native) phase) := by
    change oldEntry ((held current).val.destination original).1 = _
    exact congrArg (fun row => oldEntry (law := finance registered)
      (state? := some (financialStep registered).target) row)
      (shape.lift_destination_repair (.inr wait)
        (History.nativeWrite (input := native.input) native.frame native.visit.current).val
        (native.frame.entry native.visit.current))
  have reading := shape.extendedRows_repair (finance registered) (structuralTarget native)
    (some (financialStep registered).target) phase
  exact eq_of_heq (wrote.trans ((heq_of_eq repair).trans
    ((heq_of_eq reading.symm).trans (repair_reindex (nextShape (shape := shape) registered)
      (original_birth_support registered).symm phase))))

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Admission
