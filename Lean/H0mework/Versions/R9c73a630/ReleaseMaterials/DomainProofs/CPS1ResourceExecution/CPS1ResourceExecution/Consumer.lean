import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ResourceExecution.Machine
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ResourceExecution.Program

set_option autoImplicit false

namespace CPS1ResourceExecution

structure ResourceContract (plan : Program.Plan) : Prop where
  chargingBalance : ∀ stock species,
    stock.count species + (credit (execute plan.charges stock).fired).count species =
      (execute plan.charges stock).stock.count species +
        (debit (execute plan.charges stock).fired).count species
  elongationBalance : ∀ stock species,
    stock.count species + (credit (execute plan.elongationCore stock).fired).count species =
      (execute plan.elongationCore stock).stock.count species +
        (debit (execute plan.elongationCore stock).fired).count species
  chargingPotential : ∀ stock μ,
    speciesValue μ stock = speciesValue μ (execute plan.charges stock).stock +
      affinity μ (execute plan.charges stock).fired
  elongationPotential : ∀ stock μ,
    speciesValue μ stock = speciesValue μ (execute plan.elongationCore stock).stock +
      affinity μ (execute plan.elongationCore stock).fired
  chargingCut : ∀ stock missing, (execute plan.charges stock).missing = some missing →
    ∃ reaction rest, (execute plan.charges stock).remaining = reaction :: rest ∧
      (execute plan.charges stock).stock.count missing < reaction.reactants.count missing
  elongationCut : ∀ stock missing, (execute plan.elongationCore stock).missing = some missing →
    ∃ reaction rest, (execute plan.elongationCore stock).remaining = reaction :: rest ∧
      (execute plan.elongationCore stock).stock.count missing < reaction.reactants.count missing
  chargingDisposition : ∀ stock,
    (execute plan.charges stock).fired ++ (execute plan.charges stock).remaining = plan.charges
  elongationDisposition : ∀ stock,
    (execute plan.elongationCore stock).fired ++ (execute plan.elongationCore stock).remaining =
      plan.elongationCore

theorem resourceContract (plan : Program.Plan) : ResourceContract plan :=
  ⟨execution_balance plan.charges, execution_balance plan.elongationCore,
    execution_potential plan.charges, execution_potential plan.elongationCore,
    execution_cut plan.charges, execution_cut plan.elongationCore,
    execution_decomposes plan.charges, execution_decomposes plan.elongationCore⟩

structure OriginalResourceProgram : Prop where
  sourceGenerated : type_of% Program.source_generated_original_plan
  printedRecognition : type_of% Program.original_printed_protein_consumed
  coreLengths : type_of% Program.original_core_lengths
  reactionCounts : type_of% Program.original_core_reaction_counts
  resources : ResourceContract Program.originalPlan

theorem sourceGeneratedOriginalResourceProgram : OriginalResourceProgram :=
  ⟨Program.source_generated_original_plan, Program.original_printed_protein_consumed,
    Program.original_core_lengths, Program.original_core_reaction_counts,
    resourceContract Program.originalPlan⟩

end CPS1ResourceExecution
