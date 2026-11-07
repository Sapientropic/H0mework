import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Role
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers.Completed

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers

open Source.Program Source.ProgrammeControl Source.ProgrammeControl.Kernel PublicFunction.Repayment
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource)
open Innovation.Contribution.Pricing.Consumers.Actual (task source_input_is_the_original_registered_input source_parameters)

noncomputable section

namespace OriginalRole

abbrev original := Accounting.Quantifiers.Joint.Consumers.Compact.input
abbrev KernelAt (input : ProgrammeSource.Input Bool Bool Bool Unit Unit) :=
  CapitalRelationKernel input.law
    (ProgrammeSource.rawCurrent input (ProgrammeHistory.visitAt input 1).current)
    (ProgrammeSource.rawEvent input (ProgrammeHistory.visitAt input 1).current)

private abbrev originalBefore := ProgrammeSource.rawCurrent original (ProgrammeHistory.visitAt original 1).current
private abbrev originalWord := ProgrammeSource.rawEvent original (ProgrammeHistory.visitAt original 1).current

private def need := itemAt original.law originalBefore originalWord ⟨2, by decide +kernel⟩
private def issuance := itemAt original.law originalBefore originalWord ⟨0, by decide +kernel⟩
private def taking := itemAt original.law originalBefore originalWord ⟨3, by decide +kernel⟩

private def originalProposal : Kernel.Proposal original.law originalBefore originalWord :=
  ⟨⟨need, need, .used, false, false, true, true, true, []⟩,
    .claim issuance, ⟨taking, taking.val.request, false, []⟩⟩

private theorem originalChecks : originalProposal.Checks original.law originalBefore originalWord := by
  decide +kernel

private def control : KernelAt original :=
  (Kernel.compile original.law originalBefore originalWord originalProposal).get
    (by simp only [Kernel.compile, dif_pos originalChecks, Option.isSome_some])

def prior : PriorDependency lifeSource where
  ordinal := 1
  executed := by
    rw [source_input_is_the_original_registered_input, source_parameters.1, source_parameters.2.1]
    change 1 ≤ Financial.Installation.Cursor.lastExecutedIndex original
      (Financial.Installation.Runtime.cursorAt original 0 19)
    rw [Accounting.Quantifiers.Joint.Consumers.Compact.the_original_cause_and_financial_queue_are_fully_consumed.1]
  control := cast (congrArg KernelAt source_input_is_the_original_registered_input.symm) control

private def actors (input : ProgrammeSource.Input Bool Bool Bool Unit Unit) (kernel : KernelAt input) : Bool × Bool :=
  (kernel.proposal.access.recipient,
    input.law.controller kernel.proposal.access.access.val.before.technology kernel.proposal.access.port)

private theorem same_input_keeps_the_actual_parties {first second : ProgrammeSource.Input Bool Bool Bool Unit Unit}
    (same : first = second) (kernel : KernelAt first) :
    actors second (cast (congrArg KernelAt same) kernel) = actors first kernel := by
  cases same
  rfl

private theorem the_exact_original_dependency_reads_both_parties :
    prior.recipient = false ∧ prior.controller = true := by
  have same := same_input_keeps_the_actual_parties source_input_is_the_original_registered_input.symm control
  have known : actors original control = (false, true) := by
    simp only [actors, control, Kernel.compile, dif_pos originalChecks, Option.get_some]
    rfl
  have exactPair := same.trans known
  exact ⟨congrArg Prod.fst exactPair, congrArg Prod.snd exactPair⟩

theorem the_original_dependent_receives_the_exit_payment_from_the_old_actor_in_an_open_role
    (quantity : ℚ) (positive : 0 < quantity) (bounded : quantity ≤ 1) :
    prior.controller = true ∧ prior.recipient = false ∧
      Completed lifeSource (prior.position true ()) [] task (proposal quantity) := by
  have actors := the_exact_original_dependency_reads_both_parties
  refine ⟨actors.2, actors.1, ?_⟩
  have exactPosition : prior.position true () = position := by
    unfold PriorDependency.position
    rw [actors.1]
    rfl
  rw [exactPosition]
  exact every_positive_small_grant_executes_and_leaves_an_actual_exit_service quantity positive bounded

end OriginalRole

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers
