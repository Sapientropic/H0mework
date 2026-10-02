import H0mework.Versions.R2.Physics.MotherProgrammesFormationPotential.GeneratedHistory

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.GeneratedPotentialHistory

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineP286SourceNativeCenteredReducedEntropySafeStep
open StageNineP286SourceNativeReducedEntropyDescent
open Stage9C.Revision Stage9C.Reduction Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open MotherFamilyOccurrence StageEightDiscreteFormation PotentialSourceFormation

noncomputable section

/-- The caller supplies only an observation step and physical query. The
entire material displacement and its retained event history are generated. -/
theorem generated_history_consumed (index : ℕ) (center : BasePoint) (epoch : ℕ)
    (point : BasePoint) (action : Module.End ℂ DiracExteriorMatterCarrier) :
    let before := stateAt index
    let after := stateAt (index + 1)
    let source := formedSource (index + 1)
    let physicalCurrent := GeneralSourceEvolution.stateAt source center epoch
    let physicalTarget := GeneralSourceEvolution.stateAt source center (epoch + 1)
    before.1 = Stage9C.Revision.SpinPair.visit (10 + index) ∧
      after.1 = Stage9C.Revision.SpinPair.visit (10 + (index + 1)) ∧
      materials after.2 = ContinuousSourceFormation.coordinates Runtime.source +
        ContinuousSourceFormation.finite (index + 1) ∧
      materials (emit before.1) =
        ContinuousSourceFormation.weight (codeOf before.1) • ContinuousSourceFormation.responseAt before.1 ∧
      emittedHistory (index + 1) = emittedHistory index ++ [emit before.1] ∧
      (∀ earlier, earlier ≤ index + 1 → (emittedHistory earlier).IsPrefix (emittedHistory (index + 1))) ∧
      after.2 = initialPoints + (emittedHistory (index + 1)).sum ∧
      after.2 - before.2 = emit before.1 ∧
      (∃! displacement : Points, act before displacement = after) ∧
      (successor before.1).targetCurrent = after.1.current ∧
      (successor before.1).ledgerEvolution =
        (Stage9C.Revision.SpinPair.generatedPatch (Recognition.generated before.1).occurrence).toLedgerWriteEvolution ∧
      SourceNativeTemporalVisitAt.finite (finiteVisit after.1) = after.1 ∧
      source = sourceStep before.1 before.2 (emit before.1) ∧
      readMaterial source = execute (programAt (codeOf before.1 + 1)) neutralOrigin ∧
      source.stageEight.coframeLinearCoefficient =
        (sourceOf before.1 before.2).stageEight.coframeLinearCoefficient + coframeMaterials (emit before.1) ∧
      source.continuousContactResidual =
        (sourceOf before.1 before.2).continuousContactResidual + materials (emit before.1) 0 ∧
      (∀ slot, generatedMotherPotential Runtime.source (after.2 slot) 1 =
        generatedMotherPotential Runtime.source (before.2 slot) 1 +
          generatedMotherPotential Runtime.source (emit before.1 slot) 1) ∧
      remainders after.2 = remainders before.2 + remainders (emit before.1) ∧
      restorePoints (materials after.2) (remainders after.2) = after.2 ∧
      physicalTarget = GeneralSourceEvolution.next source center physicalCurrent ∧
      physicalTarget.current = p286CartanNext source physicalCurrent.current
        physicalCurrent.smooth physicalCurrent.nondegenerate center ∧
      physicalTarget.current = materialField source ∧
      DiracDualFormNativeJointZeroFiber source physicalTarget.current ∧
      physicalTarget.current.coframe point = homogeneousCoframe (sourceClock source) ∧
      actualRelativeAction source physicalCurrent.current physicalTarget.current =
        p286CenteredReducedRelativeAction source physicalCurrent.current
          physicalCurrent.smooth physicalCurrent.nondegenerate center ∧
      actualRelativeAction source physicalCurrent.current physicalTarget.current = 0 ∧
      physicalTarget.current.conjugateMatter point (action (physicalTarget.current.matter point)) =
        4 * (spinScale : ℂ) * Stage9DEF.State.vectorEvaluation
          (Stage9DEF.Source.restrict physicalTarget.current point) (Stage9DEF.Compatibility.responseMatrix action) := by
  refine ⟨visit_projection index, visit_projection (index + 1), materials_finite (index + 1), emit_materials _,
    history_succ index, fun _ bound => history_prefix_of_le bound, points_from_full_history (index + 1),
    emitted_recovered index, ?_, ?_⟩
  · exact (full_event_fibre (stateAt index) (stateAt (index + 1))).2 rfl
  · exact PotentialSourceFormation.history_step_consumed (stateAt index).1 (after_origin index)
      (stateAt index).2 (emit (stateAt index).1) center epoch point action

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.GeneratedPotentialHistory
