import H0mework.Physics.MotherProgrammesFormationCoordinates.HistoriesRecovery

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.WholePointHistories

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineGlobalIntegratedAction StageNineDiracDualFormNativeJointResidualCarrier
open StageNineP286SourceNativeCenteredReducedEntropySafeStep StageNineP286SourceNativeReducedEntropyDescent
open Stage9C.Revision Stage9C.Reduction Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open WholePointFormation MotherFamilyOccurrence

noncomputable section

/-- The existing full physical consumer is indexed by the actual state of this path. -/
def PhysicalAt (state : State) : Prop :=
  ∀ (center : BasePoint) (epoch : ℕ) (point : BasePoint)
    (ambient : Module.End ℂ DiracExteriorMatterCarrier),
    let formed := source state.1 state.2
    let current := GeneralSourceEvolution.stateAt formed center epoch
    let target := GeneralSourceEvolution.stateAt formed center (epoch + 1)
    target = GeneralSourceEvolution.next formed center current ∧
      target.current = p286CartanNext formed current.current current.smooth current.nondegenerate center ∧
      target.current = field state.1 state.2 ∧
      DiracDualFormNativeJointZeroFiber formed target.current ∧
      target.current.coframe point = homogeneousCoframe (sourceClock formed) ∧
      actualRelativeAction formed current.current target.current =
        p286CenteredReducedRelativeAction formed current.current current.smooth current.nondegenerate center ∧
      actualRelativeAction formed current.current target.current = 0 ∧
      target.current.conjugateMatter point (ambient (target.current.matter point)) =
        4 * (spinScale : ℂ) * Stage9DEF.State.vectorEvaluation
          (Stage9DEF.Source.restrict target.current point) (Stage9DEF.Compatibility.responseMatrix ambient)

theorem physical_at (state : State) : PhysicalAt state := by
  intro center epoch point ambient
  exact (WholePointFormation.native_consumed state.1 state.2 center epoch point ambient).2.2.2

def NativeStep (before : State) (event : Carrier) : Prop :=
  let after := act before event
  (successor before.1).targetCurrent = after.1.current ∧
    (successor before.1).ledgerEvolution =
      (SpinPair.generatedPatch (Recognition.generated before.1).occurrence).toLedgerWriteEvolution ∧
    SourceNativeTemporalVisitAt.finite (finiteVisit after.1) = after.1 ∧
    source after.1 after.2 =
      PotentialSourceFormation.sourceStep before.1 (points before.2) (points event) ∧
    PhysicalAt after

theorem native_step (before : State) (event : Carrier)
    (afterOrigin : originDepth ≤ temporalDepth before.1.history) : NativeStep before event := by
  refine ⟨rfl, target_patch _, finite_readback _, ?_, physical_at _⟩
  change PotentialSourceFormation.sourceOf (targetVisit before.1)
    (points (MotherCoordinateCompletion.completedAdd (65 * 4) before.2 event)) = _
  rw [WholePointFormation.points_add]
  exact PotentialSourceFormation.source_next_commutes before.1 afterOrigin (points before.2) (points event)

def NativeHistory (before : State) : List Carrier → Prop
  | [] => True
  | event :: events => NativeStep before event ∧ NativeHistory (act before event) events

theorem native_history (before : State) (events : List Carrier)
    (afterOrigin : originDepth ≤ temporalDepth before.1.history) : NativeHistory before events := by
  induction events generalizing before with
  | nil => trivial
  | cons event events induction =>
      refine ⟨native_step before event afterOrigin, induction (act before event) ?_⟩
      have depth : temporalDepth (targetVisit before.1).history = temporalDepth before.1.history + 1 :=
        temporalDepth_next before.1.history (successor before.1).next_eq
      change originDepth ≤ temporalDepth (targetVisit before.1).history
      rw [depth]
      omega

theorem all_intermediate_physics (before : State) (events : List Carrier) :
    ∀ state ∈ trace before events, PhysicalAt state := fun state _ => physical_at state

/-- Events are arbitrary finite legal operands. Each actual prefix produces
its own original successor, complete source update and physical target. -/
theorem whole_finite_history (events : List Carrier) :
    recover (trace initial events) = events ∧
      (rawRecover ((trace initial events).map statePoints)).map pointEquiv.symm = events ∧
      (trace initial events).map statePoints = rawTrace (statePoints initial) (events.map points) ∧
      Lawful (trace initial events) ∧ NativeHistory initial events ∧
      (∀ state ∈ trace initial events, PhysicalAt state) := by
  refine ⟨recover_trace _ _, recover_from_points _ _, trace_commutes _ _,
    trace_lawful _ _, native_history _ _ ?_, all_intermediate_physics _ _⟩
  change originDepth ≤ temporalDepth Runtime.visit.history
  rw [originDepth, finite_depth]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.WholePointHistories
