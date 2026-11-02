import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Root.Face
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Capital.InitialPeriod
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Adaptive.Effects

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  {origin : Functions.Revision.Context (input := input) (review := review)
    depth count prefixLimit renewalLimit sourceDepth sourceCount}
  {admission : Functions.Revision.InitialAdmissionAt origin}

/-- The body and its affected members are read from the actual initial
public execution and its original occurrence, before any later plan. -/
abbrev MigrationChecks (origin : Functions.Revision.Context (input := input) (review := review)
    depth count prefixLimit renewalLimit sourceDepth sourceCount)
    (admission : Functions.Revision.InitialAdmissionAt origin) : Prop :=
  Material.PeriodChecks (Macro.Public.Scope.checkInput input)
    (Capital.firstBody origin admission).1 (Capital.originalMembers origin)
    (Capital.firstBody origin admission).2

def actualMigrationDecision (origin : Functions.Revision.Context (input := input) (review := review)
    depth count prefixLimit renewalLimit sourceDepth sourceCount)
    (admission : Functions.Revision.InitialAdmissionAt origin) :=
  Material.checkPeriod (Macro.Public.Scope.checkInput input)
    (Capital.firstBody origin admission).1 (Capital.originalMembers origin)
    (Capital.firstBody origin admission).2

variable (frame : Macro.Public.Runtime.Frame origin admission)

/-- All three certificates are generated outputs. The financial certificate
comes from the already installed face; migration is checked on the actual
old-member body; continuation is compiled at this frame's current cut. -/
structure AbolitionWitness where
  private mk ::
  financial : Dividend.Financial.Checks input depth count prefixLimit renewalLimit
    origin.germ.snapshot.past frame.snapshot
  rootRead : Dividend.Root.installedAssessment frame = .accepted financial
  migration : MigrationChecks origin admission
  migrationRead : actualMigrationDecision origin admission = .accepted migration
  future : Functions.Revision.Adaptive.Plan input depth count prefixLimit renewalLimit
    origin.germ.snapshot.past frame.snapshot
  futureRead : Functions.Revision.Adaptive.compile input depth count prefixLimit renewalLimit
    origin.germ.snapshot.past frame.snapshot = .accepted future

inductive AbolitionResidual : Type
  | financial
      (issue : Dividend.Financial.Issue input depth count prefixLimit renewalLimit
        origin.germ.snapshot.past frame.snapshot)
      (rootRead : Dividend.Root.installedAssessment frame = .rejected issue)
  | migration
      (financial : Dividend.Financial.Checks input depth count prefixLimit renewalLimit
        origin.germ.snapshot.past frame.snapshot)
      (rootRead : Dividend.Root.installedAssessment frame = .accepted financial)
      (issue : Material.PeriodIssue (Macro.Public.Scope.checkInput input)
        (Capital.firstBody origin admission).1 (Capital.originalMembers origin)
        (Capital.firstBody origin admission).2)
      (migrationRead : actualMigrationDecision origin admission = .rejected issue)
  | future
      (financial : Dividend.Financial.Checks input depth count prefixLimit renewalLimit
        origin.germ.snapshot.past frame.snapshot)
      (rootRead : Dividend.Root.installedAssessment frame = .accepted financial)
      (migration : MigrationChecks origin admission)
      (migrationRead : actualMigrationDecision origin admission = .accepted migration)
      (obstruction : Functions.Revision.Adaptive.Obstruction input depth count prefixLimit renewalLimit
        origin.germ.snapshot.past frame.snapshot)
      (futureRead : Functions.Revision.Adaptive.compile input depth count prefixLimit renewalLimit
        origin.germ.snapshot.past frame.snapshot = .obstructed obstruction)

inductive AbolitionDisposition : Type
  | abolished (witness : AbolitionWitness frame)
  | residual (failure : AbolitionResidual frame)

/-- No destination, successful future, audit result or replacement account
is supplied to this producer. Every branch retains its literal source read. -/
def abolitionDisposition : AbolitionDisposition frame :=
  match rootRead : Dividend.Root.installedAssessment frame with
  | .rejected issue => .residual (.financial issue rootRead)
  | .accepted financial =>
      match migrationRead : actualMigrationDecision origin admission with
      | .rejected issue => .residual (.migration financial rootRead issue migrationRead)
      | .accepted migration =>
          match futureRead : Functions.Revision.Adaptive.compile input depth count prefixLimit renewalLimit
              origin.germ.snapshot.past frame.snapshot with
          | .obstructed obstruction =>
              .residual (.future financial rootRead migration migrationRead obstruction futureRead)
          | .accepted future =>
              .abolished ⟨financial, rootRead, migration, migrationRead, future, futureRead⟩

theorem AbolitionResidual.refutes_its_exact_original_check (failure : AbolitionResidual frame) :
    match failure with
    | .financial _ _ => ¬ Dividend.Financial.Checks input depth count prefixLimit renewalLimit
        origin.germ.snapshot.past frame.snapshot
    | .migration _ _ _ _ => ¬ MigrationChecks origin admission
    | .future _ _ _ _ _ _ =>
        ∀ word ∈ Functions.Revision.Adaptive.candidates input depth count prefixLimit renewalLimit
          origin.germ.snapshot.past frame.snapshot,
          ¬ Functions.Revision.Adaptive.Checks input depth count prefixLimit renewalLimit
            origin.germ.snapshot.past frame.snapshot word := by
  cases failure with
  | financial issue _ => exact issue.refutes _ _ _ _ _ _ _
  | migration _ _ issue _ => exact issue.refutes _ _ _ _
  | future _ _ _ _ obstruction _ => exact obstruction.excluded

theorem AbolitionResidual.excludes_a_success_witness (failure : AbolitionResidual frame) :
    ¬ Nonempty (AbolitionWitness frame) := by
  rintro ⟨witness⟩
  cases failure with
  | financial issue rootRead => cases rootRead.symm.trans witness.rootRead
  | migration _ _ issue migrationRead => cases migrationRead.symm.trans witness.migrationRead
  | future _ _ _ _ obstruction futureRead => cases futureRead.symm.trans witness.futureRead

theorem AbolitionWitness.the_installed_read_is_the_literal_root_snapshot
    (witness : AbolitionWitness frame) :
    frame.snapshotRead.fullAccount = .accepted witness.financial := witness.rootRead

theorem AbolitionWitness.the_actual_migration_keeps_independence_life_capacity_and_no_new_control
    (witness : AbolitionWitness frame) :
    Material.ActualAndIndependent (Macro.Public.Scope.checkInput input)
        (Capital.firstBody origin admission).1 (Capital.firstBody origin admission).2 ∧
      Exit.Necessity.AllNeedsPaid (Physical.Public.interpreter input)
        (Capital.firstBody origin admission).1 (Capital.originalMembers origin)
        (Capital.firstBody origin admission).2 ∧
      Material.NoFreshControl (Macro.Public.Scope.checkInput input)
        (Capital.firstBody origin admission).1 (Capital.firstBody origin admission).2 ∧
      Material.ProductionRetained (Macro.Public.Scope.checkInput input)
        (Capital.firstBody origin admission).1 (Capital.originalMembers origin)
        (Capital.firstBody origin admission).2 :=
  ⟨witness.migration.1, witness.migration.2.1, witness.migration.2.2.1, witness.migration.2.2.2.1⟩

theorem AbolitionWitness.the_future_checks_every_current_standing
    (witness : AbolitionWitness frame) :
    Macro.Public.Scope.Checks input depth count prefixLimit renewalLimit origin.germ.snapshot.past
      frame.snapshot (Functions.Revision.Adaptive.executable witness.future.rawWord) := witness.future.checked

theorem AbolitionWitness.each_original_member_has_actual_life_and_maintenance
    (witness : AbolitionWitness frame) (person : Party) (present : person ∈ Capital.originalMembers origin) :
    Exit.Necessity.BundlePaid (Physical.Public.interpreter input)
        (Capital.firstBody origin admission).1 (Capital.firstBody origin admission).2 person
        ((Physical.Public.interpreter input).necessities (Capital.firstBody origin admission).1 person) .necessity ∧
      Exit.Necessity.BundlePaid (Physical.Public.interpreter input)
        (Capital.firstBody origin admission).1 (Capital.firstBody origin admission).2 person
        ((Physical.Public.interpreter input).mandatoryMaintenance (Capital.firstBody origin admission).1 person) .maintenance :=
  witness.migration.2.1 person present

theorem AbolitionWitness.the_current_future_is_actually_executable_and_pays_every_member
    (witness : AbolitionWitness frame) :
    (Physical.Public.resultAt input depth count prefixLimit renewalLimit origin.germ.snapshot.past
        (Physical.receive frame.snapshot (.execute witness.future.rawWord))).isAccepted = true ∧
      ∀ person ∈ Epoch.Interface.Actors.PublicCensus.parties input depth count prefixLimit renewalLimit
          origin.germ.snapshot.past frame.snapshot,
        Exit.Necessity.BundlePaid (Physical.Public.interpreter input)
            (Functions.Revision.Adaptive.actualState input depth count prefixLimit renewalLimit
              origin.germ.snapshot.past frame.snapshot).raw
            (Functions.Revision.Adaptive.executable witness.future.rawWord) person
            (input.law.necessities (Functions.Revision.Adaptive.actualState input depth count prefixLimit renewalLimit
              origin.germ.snapshot.past frame.snapshot).raw person) .necessity ∧
          Exit.Necessity.BundlePaid (Physical.Public.interpreter input)
            (Functions.Revision.Adaptive.actualState input depth count prefixLimit renewalLimit
              origin.germ.snapshot.past frame.snapshot).raw
            (Functions.Revision.Adaptive.executable witness.future.rawWord) person
            (input.law.mandatoryMaintenance (Functions.Revision.Adaptive.actualState input depth count prefixLimit renewalLimit
              origin.germ.snapshot.past frame.snapshot).raw person) .maintenance :=
  ⟨Functions.Revision.Adaptive.the_actual_public_period_is_accepted
      input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot witness.future,
    Functions.Revision.Adaptive.the_selected_word_pays_every_current_member
      input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot witness.future⟩

theorem AbolitionWitness.the_full_account_has_no_loser_and_has_strict_gain
    (witness : AbolitionWitness frame) :
    (∀ person good, 0 ≤ Dividend.Financial.delta input depth count prefixLimit renewalLimit
      origin.germ.snapshot.past frame.snapshot person good) ∧
      ∃ person good, 0 < Dividend.Financial.delta input depth count prefixLimit renewalLimit
        origin.germ.snapshot.past frame.snapshot person good :=
  ⟨Dividend.Financial.all_original_bearers_and_goods_keep_their_full_account_share
      input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot witness.financial,
    Dividend.Financial.one_original_bearer_and_unit_has_strict_full_account_gain
      input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot witness.financial⟩

#print axioms abolitionDisposition
#print axioms AbolitionResidual.refutes_its_exact_original_check
#print axioms AbolitionResidual.excludes_a_success_witness
#print axioms AbolitionWitness.the_installed_read_is_the_literal_root_snapshot
#print axioms AbolitionWitness.the_actual_migration_keeps_independence_life_capacity_and_no_new_control
#print axioms AbolitionWitness.the_future_checks_every_current_standing
#print axioms AbolitionWitness.each_original_member_has_actual_life_and_maintenance
#print axioms AbolitionWitness.the_current_future_is_actually_executable_and_pays_every_member
#print axioms AbolitionWitness.the_full_account_has_no_loser_and_has_strict_gain

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly
