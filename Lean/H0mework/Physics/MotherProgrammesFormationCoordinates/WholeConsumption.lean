import H0mework.Physics.MotherProgrammesFormationCoordinates.WholeAction

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.WholePointFormation

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineGlobalIntegratedAction StageNineDiracDualFormNativeJointResidualCarrier
open StageNineP286SourceNativeCenteredReducedEntropySafeStep StageNineP286SourceNativeReducedEntropyDescent
open Stage9C.Revision Stage9C.Reduction Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open MotherFamilyOccurrence MotherCoordinateCompletion

noncomputable section

theorem generated_source_commutes (count : ℕ) :
    source (stateAt count).1 (stateAt count).2 = GeneratedPotentialHistory.formedSource count := by
  have visits := congrArg Prod.fst (generated_state_commutes count)
  have operands := congrArg Prod.snd (generated_state_commutes count)
  dsimp only [statePoints] at visits operands
  unfold source GeneratedPotentialHistory.formedSource
  change PotentialSourceFormation.sourceOf (stateAt count).1 (points (stateAt count).2) = _
  rw [visits, operands]

theorem history_readback (count : ℕ) :
    (GeneratedPotentialHistory.emittedHistory count).map pointEquiv.symm = emittedHistory count := by
  rw [← generated_history_commutes, List.map_map]
  change (emittedHistory count).map (fun value => pointEquiv.symm (pointEquiv value)) = _
  simp only [Equiv.symm_apply_apply]
  exact List.map_id _

/-- The entire completed operand, event and finite history are consumed
at the unchanged original root successor and its source-indexed physical target. -/
theorem generated_native_consumed (count : ℕ) (center : BasePoint) (epoch : ℕ)
    (point : BasePoint) (ambient : Module.End ℂ DiracExteriorMatterCarrier) :
    let before := stateAt count
    let after := stateAt (count + 1)
    let formed := source after.1 after.2
    let current := GeneralSourceEvolution.stateAt formed center epoch
    let target := GeneralSourceEvolution.stateAt formed center (epoch + 1)
    after = step before ∧
      statePoints after = GeneratedPotentialHistory.stateAt (count + 1) ∧
      formed = GeneratedPotentialHistory.formedSource (count + 1) ∧
      (GeneratedPotentialHistory.emittedHistory (count + 1)).map pointEquiv.symm = emittedHistory (count + 1) ∧
      (∃! event : Carrier, act before event = after) ∧
      (successor before.1).targetCurrent = after.1.current ∧
      (successor before.1).ledgerEvolution =
        (SpinPair.generatedPatch (Recognition.generated before.1).occurrence).toLedgerWriteEvolution ∧
      SourceNativeTemporalVisitAt.finite (finiteVisit after.1) = after.1 ∧
      formed = PotentialSourceFormation.sourceStep before.1 (points before.2) (points (emit before.1)) ∧
      pointEquiv.symm (points after.2) = after.2 ∧
      (∀ slot, curvatureRate (generatedMotherPotential Runtime.source (points after.2 slot) 1) =
        coordinate after.2 slot 0) ∧
      (∀ (slot : Fin 65) (axis : Fin 3), points after.2 slot axis.succ = coordinate after.2 slot axis.succ) ∧
      target = GeneralSourceEvolution.next formed center current ∧
      target.current = p286CartanNext formed current.current current.smooth current.nondegenerate center ∧
      target.current = field after.1 after.2 ∧
      DiracDualFormNativeJointZeroFiber formed target.current ∧
      target.current.coframe point = homogeneousCoframe (sourceClock formed) ∧
      actualRelativeAction formed current.current target.current =
        p286CenteredReducedRelativeAction formed current.current current.smooth current.nondegenerate center ∧
      actualRelativeAction formed current.current target.current = 0 ∧
      target.current.conjugateMatter point (ambient (target.current.matter point)) =
        4 * (spinScale : ℂ) * Stage9DEF.State.vectorEvaluation
          (Stage9DEF.Source.restrict target.current point) (Stage9DEF.Compatibility.responseMatrix ambient) := by
  refine ⟨rfl, generated_state_commutes (count + 1), generated_source_commutes (count + 1),
    history_readback (count + 1), (full_event_fibre (stateAt count) (stateAt (count + 1))).2 rfl,
    rfl, target_patch _, finite_readback _, ?_,
    native_consumed (stateAt (count + 1)).1 (stateAt (count + 1)).2 center epoch point ambient⟩
  have afterOrigin : originDepth ≤ temporalDepth (stateAt count).1.history := by
    rw [show (stateAt count).1 = (GeneratedPotentialHistory.stateAt count).1 from
      congrArg Prod.fst (generated_state_commutes count)]
    exact GeneratedPotentialHistory.after_origin count
  change PotentialSourceFormation.sourceOf (targetVisit (stateAt count).1)
      (points (completedAdd (65 * 4) (stateAt count).2 (emit (stateAt count).1))) = _
  rw [points_add]
  exact PotentialSourceFormation.source_next_commutes (stateAt count).1 afterOrigin
    (points (stateAt count).2) (points (emit (stateAt count).1))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.WholePointFormation
