import H0mework.Versions.AD.Realization.JointEffect.Alignment

/-!
# Full-tree fold for a passive dependent joint effect

Every aligned source/target pairing node is already classified by the total
joint-transition kernel.  This file folds the sole accounted occurrence into
either a complete tree of generated naturality squares or the first exact
node residual.  No root-only shortcut may ignore a child branch.
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

structure GeneratedNodeAt
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor)) where
  pair : AlignedPairAt step successor
  joint : GeneratedJointTransitionAt history pair.1 pair.2
    (stepSourceExposureAt step pair.1).sourceAction.carrierAction
    (stepTargetExposureAt step successor pair.2).sourceAction.carrierAction
    (stepSourceExposureAt step pair.1).measurement
    (stepTargetExposureAt step successor pair.2).measurement
    (stepSourceExposureAt step pair.1).hilbertEvolution
    (stepTargetExposureAt step successor pair.2).hilbertEvolution

inductive ExactResidualAt
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor)) : Type u
  | pairingKernel (pair : AlignedPairAt step successor)
      (coordinate : PairingKernelResidualAt history pair.1 pair.2)
  | pairingValue (pair : AlignedPairAt step successor)
      (coordinate : PairingValueResidualAt history pair.1 pair.2)
  | action (pair : AlignedPairAt step successor)
      (coordinate : ActionResidualAt history
        (stepSourceExposureAt step pair.1).sourceAction.carrierAction
        (stepTargetExposureAt step successor pair.2).sourceAction.carrierAction)
  | measurement (pair : AlignedPairAt step successor)
      (coordinate : MeasurementResidualAt history
        (stepSourceExposureAt step pair.1).measurement
        (stepTargetExposureAt step successor pair.2).measurement)
  | evolution (pair : AlignedPairAt step successor)
      (coordinate : EvolutionResidualAt
        (stepSourceExposureAt step pair.1).hilbertEvolution
        (stepTargetExposureAt step successor pair.2).hilbertEvolution)

def ExactResidualAt.payload
    {step : StepAt recognition visit} {successor : StepLedgerSuccessorAt step}
    {history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor)} :
    ExactResidualAt step successor history →
      AlignedJointPayloadAt step successor history
  | .pairingKernel pair coordinate =>
      ⟨pair, .pairingKernelResidual coordinate⟩
  | .pairingValue pair coordinate =>
      ⟨pair, .pairingValueResidual coordinate⟩
  | .action pair coordinate => ⟨pair, .actionResidual coordinate⟩
  | .measurement pair coordinate =>
      ⟨pair, .measurementResidual coordinate⟩
  | .evolution pair coordinate =>
      ⟨pair, .evolutionResidual coordinate⟩

abbrev NodeOutcomeAt
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor)) :=
  GeneratedNodeAt step successor history ⊕ ExactResidualAt step successor history

def settleNode
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor))
    (payload : AlignedJointPayloadAt step successor history) :
    NodeOutcomeAt step successor history := by
  rcases payload with ⟨pair, disposition⟩
  cases disposition with
  | generated joint => exact .inl ⟨pair, joint⟩
  | pairingKernelResidual coordinate =>
      exact .inr (.pairingKernel pair coordinate)
  | pairingValueResidual coordinate =>
      exact .inr (.pairingValue pair coordinate)
  | actionResidual coordinate => exact .inr (.action pair coordinate)
  | measurementResidual coordinate =>
      exact .inr (.measurement pair coordinate)
  | evolutionResidual coordinate => exact .inr (.evolution pair coordinate)

abbrev TreeOutcomeAt
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor)) :=
  RootedAccountedUnfolding (GeneratedNodeAt step successor history) ⊕
    ExactResidualAt step successor history

def collectGenerated
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor)) :
    List (TreeOutcomeAt step successor history) →
      AccountedBranches (GeneratedNodeAt step successor history) ⊕
        ExactResidualAt step successor history
  | [] => .inl .nil
  | .inr residual :: _ => .inr residual
  | .inl head :: tail =>
      match collectGenerated step successor history tail with
      | .inl branches => .inl (.cons head branches)
      | .inr residual => .inr residual

def effectFoldAt
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor))
    (payload : AlignedJointPayloadAt step successor history)
    (children : List (TreeOutcomeAt step successor history)) :
    TreeOutcomeAt step successor history :=
  match settleNode step successor history payload with
  | .inr residual => .inr residual
  | .inl generated =>
      match collectGenerated step successor history children with
      | .inl branches => .inl (.occur generated branches)
      | .inr residual => .inr residual

def settleTree
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor))
    (occurrence : RootedAccountedUnfolding
      (AlignedJointPayloadAt step successor history)) :
    TreeOutcomeAt step successor history :=
  occurrence.fold (effectFoldAt step successor history)

theorem settleTree_unique
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor))
    (candidate : RootedAccountedUnfolding
      (AlignedJointPayloadAt step successor history) →
        TreeOutcomeAt step successor history)
    (commutes : ∀ origin branches,
      candidate (.occur origin branches) =
        effectFoldAt step successor history origin
          (RootedAccountedUnfolding.candidateValues candidate branches))
    (occurrence : RootedAccountedUnfolding
      (AlignedJointPayloadAt step successor history)) :
    candidate occurrence = settleTree step successor history occurrence :=
  RootedAccountedUnfolding.fold_unique _ candidate commutes occurrence

theorem settleNode_generated_pair
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor))
    (payload : AlignedJointPayloadAt step successor history)
    (generated : GeneratedNodeAt step successor history)
    (exact : settleNode step successor history payload = .inl generated) :
    generated.pair = payload.1 := by
  rcases payload with ⟨pair, disposition⟩
  cases disposition <;> simp [settleNode] at exact
  case generated joint =>
    cases exact
    rfl

mutual

theorem settleTree_generated_projects
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor))
    (occurrence : RootedAccountedUnfolding
      (AlignedJointPayloadAt step successor history))
    (generated : RootedAccountedUnfolding
      (GeneratedNodeAt step successor history))
    (exact : settleTree step successor history occurrence = .inl generated) :
    generated.map GeneratedNodeAt.pair = occurrence.map Sigma.fst := by
  cases occurrence with
  | occur payload branches =>
      change effectFoldAt step successor history payload
          (RootedAccountedUnfolding.foldBranches
            (effectFoldAt step successor history) branches) =
        .inl generated at exact
      unfold effectFoldAt at exact
      cases node_eq : settleNode step successor history payload with
      | inr residual =>
          simp only [node_eq] at exact
          contradiction
      | inl node =>
          simp only [node_eq] at exact
          change (match collectGenerated step successor history
              (RootedAccountedUnfolding.foldBranches
                (effectFoldAt step successor history) branches) with
            | .inl generatedBranches =>
                Sum.inl (RootedAccountedUnfolding.occur node generatedBranches)
            | .inr residual => Sum.inr residual) = .inl generated at exact
          cases branches_eq : collectGenerated step successor history
              (RootedAccountedUnfolding.foldBranches
                (effectFoldAt step successor history) branches) with
          | inr residual =>
              simp only [branches_eq] at exact
              contradiction
          | inl generatedBranches =>
              simp only [branches_eq] at exact
              cases exact
              change RootedAccountedUnfolding.occur node.pair
                  (RootedAccountedUnfolding.mapBranches
                    GeneratedNodeAt.pair generatedBranches) =
                RootedAccountedUnfolding.occur payload.1
                  (RootedAccountedUnfolding.mapBranches Sigma.fst branches)
              rw [settleNode_generated_pair step successor history
                payload node node_eq]
              rw [collectGenerated_projects step successor history branches
                generatedBranches branches_eq]

theorem collectGenerated_projects
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor))
    (branches : AccountedBranches
      (AlignedJointPayloadAt step successor history))
    (generatedBranches : AccountedBranches
      (GeneratedNodeAt step successor history))
    (exact : collectGenerated step successor history
      (RootedAccountedUnfolding.foldBranches
        (effectFoldAt step successor history) branches) =
        .inl generatedBranches) :
    RootedAccountedUnfolding.mapBranches GeneratedNodeAt.pair
        generatedBranches =
      RootedAccountedUnfolding.mapBranches Sigma.fst branches := by
  cases branches with
  | nil =>
      change (Sum.inl .nil : AccountedBranches
          (GeneratedNodeAt step successor history) ⊕
            ExactResidualAt step successor history) =
        .inl generatedBranches at exact
      cases exact
      rfl
  | cons head tail =>
      change collectGenerated step successor history
          (settleTree step successor history head ::
            RootedAccountedUnfolding.foldBranches
              (effectFoldAt step successor history) tail) =
        .inl generatedBranches at exact
      cases head_eq : settleTree step successor history head with
      | inr residual =>
          simp only [head_eq, collectGenerated] at exact
          contradiction
      | inl generatedHead =>
          simp only [head_eq, collectGenerated] at exact
          change (match collectGenerated step successor history
              (RootedAccountedUnfolding.foldBranches
                (effectFoldAt step successor history) tail) with
            | .inl generatedTail =>
                Sum.inl (AccountedBranches.cons generatedHead generatedTail)
            | .inr residual => Sum.inr residual) =
              .inl generatedBranches at exact
          cases tail_eq : collectGenerated step successor history
              (RootedAccountedUnfolding.foldBranches
                (effectFoldAt step successor history) tail) with
          | inr residual =>
              simp only [tail_eq] at exact
              contradiction
          | inl generatedTail =>
              simp only [tail_eq] at exact
              cases exact
              change AccountedBranches.cons
                  (generatedHead.map GeneratedNodeAt.pair)
                  (RootedAccountedUnfolding.mapBranches
                    GeneratedNodeAt.pair generatedTail) =
                AccountedBranches.cons (head.map Sigma.fst)
                  (RootedAccountedUnfolding.mapBranches Sigma.fst tail)
              rw [settleTree_generated_projects step successor history
                head generatedHead head_eq]
              rw [collectGenerated_projects step successor history tail
                generatedTail tail_eq]

end

end

end RootLawDependentJointPassiveEffect
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
