import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Capture.Contract
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Core

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction PublicFunction.Repayment
open Source.ProgrammeControl Source.ProgrammeControl.Kernel
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

abbrev priorVisit (source : C) (ordinal : Nat) := ProgrammeHistory.visitAt source.native.input ordinal
abbrev priorRaw (source : C) (ordinal : Nat) :=
  ProgrammeSource.rawCurrent source.native.input (priorVisit source ordinal).current
abbrev priorWord (source : C) (ordinal : Nat) :=
  ProgrammeSource.rawEvent source.native.input (priorVisit source ordinal).current

/-- The earlier dependency is a paid role on the original root prefix.
Only the role loses authority at the public cut. The actors remain the
original signers and claim bearers. -/
structure PriorDependency (source : C) where
  ordinal : Nat
  executed : ordinal ≤ Financial.Installation.Cursor.lastExecutedIndex source.native.input
    (Financial.Installation.Runtime.cursorAt source.native.input source.native.depth source.native.count)
  control : CapitalRelationKernel source.native.input.law (priorRaw source ordinal) (priorWord source ordinal)

namespace PriorDependency

def recipient {current : C} (role : PriorDependency current) : Party :=
  match role with
  | ⟨_, _, kernel⟩ => kernel.proposal.access.recipient

def port {current : C} (role : PriorDependency current) : Port :=
  match role with
  | ⟨_, _, kernel⟩ => kernel.proposal.access.port

def controller {current : C} (role : PriorDependency current) : Party :=
  match role with
  | ⟨_, _, kernel⟩ =>
      current.native.input.law.controller kernel.proposal.access.access.val.before.technology kernel.proposal.access.port

def position {current : C} (role : PriorDependency current)
    (issuer : Party) (instrument : Instrument) : Position Party Instrument :=
  ⟨instrument, issuer, role.recipient⟩

theorem original_controller_is_a_distinct_actor {current : C} (role : PriorDependency current) :
    role.controller ≠ role.recipient := by
  rcases role with ⟨ordinal, _, kernel⟩
  exact private_phase_separates_controller current.native.input.law _ _ _
    (CapitalRelationKernel.original_control_and_reproduced_phase current.native.input.law
      (priorRaw current ordinal) (priorWord current ordinal) kernel).2.2.1

theorem the_old_permission_cannot_control_any_current_independent_service {current : C} (role : PriorDependency current)
    (script : List (Option (Compile.RawInput Party Good Port Technology Instrument))) :
    ¬ PrivatePhase (Physical.Public.interpreter (Execution.endAt current script).native.input)
      (Execution.endAt current script).raw role.port role.recipient := by
  intro restored
  have no : true = false := restored.2
  cases no

theorem the_original_recipient_has_its_joint_exit_amount_domain
    {current : C} (role : PriorDependency current) (issuer : Party) (instrument : Instrument)
    (task : PublicTaskSpec Party Good) (count : Nat) :
    Bounds.Compiled.Minimum current
      (fun plan => compile current (role.position issuer instrument)
        (Capture.expand current (role.position issuer instrument) count plan))
      (Capture.inspectExit current (role.position issuer instrument) task count) principal :=
  Capture.the_original_root_resolves_exit_amounts_after_its_actual_exposure current
    (role.position issuer instrument) task count

end PriorDependency

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant
