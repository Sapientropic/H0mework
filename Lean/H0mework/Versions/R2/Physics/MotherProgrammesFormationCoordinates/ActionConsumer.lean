import H0mework.Versions.R2.Physics.MotherProgrammesFormationCoordinates.ActionEmitter

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCoordinateCompletion

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineGlobalIntegratedAction StageNineDiracDualFormNativeJointResidualCarrier
open StageNineP286SourceNativeCenteredReducedEntropySafeStep
open StageNineP286SourceNativeReducedEntropyDescent
open Stage9C.Revision Stage9C.Reduction Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open MotherFamilyOccurrence StageEightDiscreteFormation

noncomputable section

def completedHistory : ℕ → List PointPresentation
  | 0 => []
  | index + 1 => completedHistory index ++ [completedEmit (completedStateAt index).1]

theorem generated_history_commutes (index : ℕ) :
    (completedHistory index).map points = GeneratedPotentialHistory.emittedHistory index := by
  induction index with
  | zero => rfl
  | succ index induction =>
      simp only [completedHistory, List.map_append, List.map_cons, List.map_nil,
        induction, emitted_points, GeneratedPotentialHistory.history_succ]
      rw [show (completedStateAt index).1 = (GeneratedPotentialHistory.stateAt index).1 from
        congrArg Prod.fst (generated_state_commutes index)]

theorem generated_source_commutes (index : ℕ) :
    source (completedStateAt index).1 (completedStateAt index).2 =
      GeneratedPotentialHistory.formedSource index := by
  have visits : (completedStateAt index).1 = (GeneratedPotentialHistory.stateAt index).1 :=
    congrArg Prod.fst (generated_state_commutes index)
  have operands : points (completedStateAt index).2 = (GeneratedPotentialHistory.stateAt index).2 :=
    congrArg Prod.snd (generated_state_commutes index)
  unfold source GeneratedPotentialHistory.formedSource
  rw [visits, operands]

/-- The completed operation selects the same full target as the finite
emitter, original mother history and source-indexed physical writer. -/
theorem completed_history_consumed (index : ℕ) (center : BasePoint) (epoch : ℕ)
    (point : BasePoint) (ambient : Module.End ℂ DiracExteriorMatterCarrier) :
    let before := completedStateAt index
    let after := completedStateAt (index + 1)
    let formed := source after.1 after.2
    let current := GeneralSourceEvolution.stateAt formed center epoch
    let target := GeneralSourceEvolution.stateAt formed center (epoch + 1)
    after = completedStep before ∧
      statePoints after = GeneratedPotentialHistory.stateAt (index + 1) ∧
      formed = GeneratedPotentialHistory.formedSource (index + 1) ∧
      completedHistory (index + 1) = completedHistory index ++ [completedEmit before.1] ∧
      (completedHistory (index + 1)).map points = GeneratedPotentialHistory.emittedHistory (index + 1) ∧
      presentationSub after.2 before.2 = completedEmit before.1 ∧
      (∃! event : PointPresentation, completedAct before event = after) ∧
      (successor before.1).targetCurrent = after.1.current ∧
      (successor before.1).ledgerEvolution =
        (SpinPair.generatedPatch (Recognition.generated before.1).occurrence).toLedgerWriteEvolution ∧
      SourceNativeTemporalVisitAt.finite (finiteVisit after.1) = after.1 ∧
      formed = PotentialSourceFormation.sourceStep before.1 (points before.2) (points (completedEmit before.1)) ∧
      readMaterial formed = execute (programAt (codeOf before.1 + 1)) neutralOrigin ∧
      formed.stageEight.coframeLinearCoefficient =
        (source before.1 before.2).stageEight.coframeLinearCoefficient +
          PotentialSourceFormation.coframeMaterials (points (completedEmit before.1)) ∧
      formed.continuousContactResidual = (source before.1 before.2).continuousContactResidual +
        PotentialSourceFormation.materials (points (completedEmit before.1)) 0 ∧
      (∀ slot, generatedMotherPotential Runtime.source (points after.2 slot) 1 =
        generatedMotherPotential Runtime.source (points before.2 slot) 1 +
          generatedMotherPotential Runtime.source (points (completedEmit before.1) slot) 1) ∧
      PotentialSourceFormation.remainders (points after.2) =
        PotentialSourceFormation.remainders (points before.2) +
          PotentialSourceFormation.remainders (points (completedEmit before.1)) ∧
      PotentialSourceFormation.restorePoints (PotentialSourceFormation.materials (points after.2))
        (PotentialSourceFormation.remainders (points after.2)) = points after.2 ∧
      target = GeneralSourceEvolution.next formed center current ∧
      target.current = p286CartanNext formed current.current current.smooth current.nondegenerate center ∧
      target.current = materialField formed ∧
      DiracDualFormNativeJointZeroFiber formed target.current ∧
      target.current.coframe point = homogeneousCoframe (sourceClock formed) ∧
      actualRelativeAction formed current.current target.current =
        p286CenteredReducedRelativeAction formed current.current current.smooth current.nondegenerate center ∧
      actualRelativeAction formed current.current target.current = 0 ∧
      target.current.conjugateMatter point (ambient (target.current.matter point)) =
        4 * (spinScale : ℂ) * Stage9DEF.State.vectorEvaluation
          (Stage9DEF.Source.restrict target.current point) (Stage9DEF.Compatibility.responseMatrix ambient) := by
  refine ⟨rfl, generated_state_commutes (index + 1), generated_source_commutes (index + 1),
    rfl, generated_history_commutes (index + 1),
    (presentation_event_recovered (completedStateAt index).2 (completedEmit (completedStateAt index).1)).2,
    (full_event_fibre (completedStateAt index) (completedStateAt (index + 1))).2 rfl, ?_⟩
  have afterOrigin : originDepth ≤ temporalDepth (completedStateAt index).1.history := by
    rw [show (completedStateAt index).1 = (GeneratedPotentialHistory.stateAt index).1 from
      congrArg Prod.fst (generated_state_commutes index)]
    exact GeneratedPotentialHistory.after_origin index
  obtain ⟨nativeTarget, ledger, recovered, sourceNext, discrete, coframe, contact,
    potential, spatial, complete, _⟩ :=
    PotentialSourceFormation.history_step_consumed (completedStateAt index).1 afterOrigin
      (points (completedStateAt index).2) (points (completedEmit (completedStateAt index).1))
      center epoch point ambient
  refine ⟨nativeTarget, ledger, recovered, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    GeneralSourceEvolution.whole_native_consumed
      (source (completedStateAt (index + 1)).1 (completedStateAt (index + 1)).2)
      center epoch point ambient⟩
  all_goals
    simpa only [completedStateAt, completedStep, completedAct, source, points_add,
      PotentialSourceFormation.nextOperands] using
      (by first | exact sourceNext | exact discrete | exact coframe | exact contact |
        exact potential | exact spatial | exact complete)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCoordinateCompletion
