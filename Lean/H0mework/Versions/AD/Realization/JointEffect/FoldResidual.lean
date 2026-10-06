import H0mework.Versions.AD.Realization.JointEffect.Fold

/-!
# Provenance of a folded dependent joint residual

The residual selected by the passive effect fold is an actual payload in the
complete aligned occurrence trace.  A child failure therefore cannot be
relabelled as a root-only diagnostic or disappear behind the aggregate fold.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootLawDependentJointPassiveEffect

open CofinalHistoryTransition
open RootLawDependentJointStateController
open RootLawDependentJointTransition

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {root : SourceNativeLivingRootClosure N V}
variable {recognition : RecognitionAt H root}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}

theorem settleNode_residual_payload
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor))
    (payload : AlignedJointPayloadAt step successor history)
    (residual : ExactResidualAt step successor history)
    (exact : settleNode step successor history payload = .inr residual) :
    ExactResidualAt.payload residual = payload := by
  rcases payload with ⟨pair, disposition⟩
  cases disposition <;> simp [settleNode] at exact
  all_goals
    cases exact
    rfl

@[simp] theorem settleNode_payload_residual
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor))
    (residual : ExactResidualAt step successor history) :
    settleNode step successor history (ExactResidualAt.payload residual) =
      .inr residual := by
  cases residual <;> rfl

theorem settleTree_zero_residual
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor))
    (residual : ExactResidualAt step successor history) :
    settleTree step successor history
        (RootedAccountedUnfolding.zero (ExactResidualAt.payload residual)) =
      .inr residual := by
  change effectFoldAt step successor history
      (ExactResidualAt.payload residual) [] = .inr residual
  rw [effectFoldAt, settleNode_payload_residual]

mutual

theorem settleTree_residual_mem_trace
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor))
    (occurrence : RootedAccountedUnfolding
      (AlignedJointPayloadAt step successor history))
    (residual : ExactResidualAt step successor history)
    (exact : settleTree step successor history occurrence = .inr residual) :
    ExactResidualAt.payload residual ∈ occurrence.trace := by
  cases occurrence with
  | occur payload branches =>
      change effectFoldAt step successor history payload
          (RootedAccountedUnfolding.foldBranches
            (effectFoldAt step successor history) branches) =
        .inr residual at exact
      unfold effectFoldAt at exact
      cases node_eq : settleNode step successor history payload with
      | inr rootResidual =>
          simp only [node_eq] at exact
          cases exact
          change ExactResidualAt.payload residual ∈ payload ::
            RootedAccountedUnfolding.traceBranches branches
          rw [settleNode_residual_payload step successor history
            payload residual node_eq]
          exact List.mem_cons_self
      | inl generated =>
          simp only [node_eq] at exact
          change (match collectGenerated step successor history
              (RootedAccountedUnfolding.foldBranches
                (effectFoldAt step successor history) branches) with
            | .inl generatedBranches =>
                Sum.inl (RootedAccountedUnfolding.occur generated
                  generatedBranches)
            | .inr childResidual => Sum.inr childResidual) =
              .inr residual at exact
          cases branches_eq : collectGenerated step successor history
              (RootedAccountedUnfolding.foldBranches
                (effectFoldAt step successor history) branches) with
          | inl generatedBranches =>
              simp only [branches_eq] at exact
              contradiction
          | inr childResidual =>
              simp only [branches_eq] at exact
              cases exact
              change ExactResidualAt.payload residual ∈ payload ::
                RootedAccountedUnfolding.traceBranches branches
              exact List.mem_cons_of_mem _
                (collectGenerated_residual_mem_trace step successor history
                  branches residual branches_eq)

theorem collectGenerated_residual_mem_trace
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor))
    (branches : AccountedBranches
      (AlignedJointPayloadAt step successor history))
    (residual : ExactResidualAt step successor history)
    (exact : collectGenerated step successor history
      (RootedAccountedUnfolding.foldBranches
        (effectFoldAt step successor history) branches) = .inr residual) :
    ExactResidualAt.payload residual ∈
      RootedAccountedUnfolding.traceBranches branches := by
  cases branches with
  | nil =>
      change (Sum.inl .nil : AccountedBranches
          (GeneratedNodeAt step successor history) ⊕
            ExactResidualAt step successor history) = .inr residual at exact
      contradiction
  | cons head tail =>
      change collectGenerated step successor history
          (settleTree step successor history head ::
            RootedAccountedUnfolding.foldBranches
              (effectFoldAt step successor history) tail) =
        .inr residual at exact
      cases head_eq : settleTree step successor history head with
      | inr headResidual =>
          simp only [head_eq, collectGenerated] at exact
          cases exact
          change ExactResidualAt.payload residual ∈ head.trace ++
            RootedAccountedUnfolding.traceBranches tail
          exact List.mem_append_left _
            (settleTree_residual_mem_trace step successor history
              head residual head_eq)
      | inl generatedHead =>
          simp only [head_eq, collectGenerated] at exact
          change (match collectGenerated step successor history
              (RootedAccountedUnfolding.foldBranches
                (effectFoldAt step successor history) tail) with
            | .inl generatedTail =>
                Sum.inl (AccountedBranches.cons generatedHead generatedTail)
            | .inr tailResidual => Sum.inr tailResidual) =
              .inr residual at exact
          cases tail_eq : collectGenerated step successor history
              (RootedAccountedUnfolding.foldBranches
                (effectFoldAt step successor history) tail) with
          | inl generatedTail =>
              simp only [tail_eq] at exact
              contradiction
          | inr tailResidual =>
              simp only [tail_eq] at exact
              cases exact
              change ExactResidualAt.payload residual ∈ head.trace ++
                RootedAccountedUnfolding.traceBranches tail
              exact List.mem_append_right _
                (collectGenerated_residual_mem_trace step successor history
                  tail residual tail_eq)

end

end

end RootLawDependentJointPassiveEffect
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
