import H0mework.Physics.MotherProgrammesFormationProgrammes.ExecutionTrace
import H0mework.Physics.MotherProgrammesFormationMatter.ActionConsumer

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProgrammeExecution

open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineGlobalIntegratedAction StageNineDiracDualFormNativeJointResidualCarrier
open StageNineP286SourceNativeCenteredReducedEntropySafeStep StageNineP286SourceNativeReducedEntropyDescent
open Stage9C.Revision Stage9C.Reduction Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open WholePointFormation WholePointHistories MotherProgrammes MotherFamilyOccurrence
open scoped Matrix

noncomputable section

theorem entry_birth (index : ℕ) (prior : List Entry) (entry : Entry) (suffix : List Entry)
    (position : programme index = prior ++ entry :: suffix) :
    let cell := run (start index) prior
    let born := view (arrival cell entry)
    replay (view (start index)) (events (start index) (prior ++ [entry])) = born ∧
      WholePointFormation.source born.1 born.2 = entry.source ∧
      PotentialSourceFormation.remainders (WholePointFormation.points born.2) =
        PotentialSourceFormation.remainders (WholePointFormation.points entry.carrier) ∧
      (temporalDepth entry.discreteVisit.history < temporalDepth born.1.history ∧
        temporalDepth entry.coordinateVisit.history < temporalDepth born.1.history) ∧
      PhysicalAt born := by
  have member : entry ∈ programme index := by rw [position]; simp
  exact ⟨prefix_arrival _ _ _, arrival_source _ _, rfl,
    birth_after_parents index _ entry (index_mono (start index) prior) member, physical_at _⟩

/-- The only execution input is the current mother index. The complete
programme and every event are formed from that occurrence and its retained past. -/
theorem programme_execution_consumed (index : ℕ) :
    replay initial (fullEvents index) = view (terminalCell index) ∧
      index < (terminalCell index).1 ∧
      (WholePointFormation.emittedHistory index).IsPrefix (fullEvents index) ∧
      (trace initial (WholePointFormation.emittedHistory index)).IsPrefix (trace initial (fullEvents index)) ∧
      List.Sublist ((programme index).map entryReadout) (RawSourcePaths.pathReadout initial (fullEvents index)) ∧
      (trace initial (fullEvents index)).map Prod.fst =
        (List.range' 10 ((fullEvents index).length + 1)).map SpinPair.visit ∧
      recover (trace initial (fullEvents index)) = fullEvents index ∧
      (rawRecover ((trace initial (fullEvents index)).map statePoints)).map pointEquiv.symm = fullEvents index ∧
      (trace initial (fullEvents index)).map statePoints =
        rawTrace (statePoints initial) ((fullEvents index).map points) ∧
      Lawful (trace initial (fullEvents index)) ∧ NativeHistory initial (fullEvents index) ∧
      (∀ state ∈ trace initial (fullEvents index), PhysicalAt state) :=
  ⟨full_replay index, terminal_late index, retained_events index, retained_trace index,
    full_order index, RawSourcePaths.trace_visits 10 initial.2 (fullEvents index),
    whole_finite_history (fullEvents index)⟩

/-- The operator is read from this same actual mother occurrence. -/
def NativeOperatorAt (cell : Cell) (center : BasePoint) (epoch : ℕ) (point : BasePoint) : Prop :=
    let terminal := view cell
    let ambient := MotherMatterActions.operatorAt terminal.1
    let formed := WholePointFormation.source terminal.1 terminal.2
    let current := GeneralSourceEvolution.stateAt formed center epoch
    let target := GeneralSourceEvolution.stateAt formed center (epoch + 1)
    MotherMatterActions.operatorEquiv.symm ambient = MotherMatterActions.finiteData terminal.1 ∧
      MotherMatterActions.readMatrix ambient = MotherMatterActions.matrix (MotherMatterActions.finiteData terminal.1) ∧
      (∀ matter : DiracExteriorMatterCarrier,
        (MotherMatterActions.matterBasis.repr (ambient matter) : MotherMatterActions.Index → ℂ) =
          MotherMatterActions.matrix (MotherMatterActions.finiteData terminal.1) *ᵥ
            MotherMatterActions.matterBasis.repr matter) ∧
      target = GeneralSourceEvolution.next formed center current ∧
      target.current = p286CartanNext formed current.current current.smooth current.nondegenerate center ∧
      target.current = WholePointFormation.field terminal.1 terminal.2 ∧
      DiracDualFormNativeJointZeroFiber formed target.current ∧
      target.current.coframe point = homogeneousCoframe (sourceClock formed) ∧
      actualRelativeAction formed current.current target.current =
        p286CenteredReducedRelativeAction formed current.current current.smooth current.nondegenerate center ∧
      actualRelativeAction formed current.current target.current = 0 ∧
      target.current.conjugateMatter point (ambient (target.current.matter point)) =
        4 * (spinScale : ℂ) * Stage9DEF.State.vectorEvaluation
          (Stage9DEF.Source.restrict target.current point) (Stage9DEF.Compatibility.responseMatrix ambient)

theorem native_operator_at (cell : Cell) (center : BasePoint) (epoch : ℕ) (point : BasePoint) :
    NativeOperatorAt cell center epoch point :=
  (MotherMatterActions.finite_native_consumed (view cell).1 (view cell).2 center epoch point).2

theorem entry_native_consumed (index : ℕ) (prior : List Entry) (entry : Entry) (suffix : List Entry)
    (position : programme index = prior ++ entry :: suffix)
    (center : BasePoint) (epoch : ℕ) (point : BasePoint) :
    let cell := arrival (run (start index) prior) entry
    let born := view cell
    replay (view (start index)) (events (start index) (prior ++ [entry])) = born ∧
      WholePointFormation.source born.1 born.2 = entry.source ∧
      PotentialSourceFormation.remainders (WholePointFormation.points born.2) =
        PotentialSourceFormation.remainders (WholePointFormation.points entry.carrier) ∧
      (temporalDepth entry.discreteVisit.history < temporalDepth born.1.history ∧
        temporalDepth entry.coordinateVisit.history < temporalDepth born.1.history) ∧
      NativeOperatorAt cell center epoch point := by
  have birth := entry_birth index prior entry suffix position
  exact ⟨birth.1, birth.2.1, birth.2.2.1, birth.2.2.2.1, native_operator_at _ center epoch point⟩

theorem terminal_native_consumed (index : ℕ) (center : BasePoint) (epoch : ℕ) (point : BasePoint) :
    NativeOperatorAt (terminalCell index) center epoch point := native_operator_at _ center epoch point

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProgrammeExecution
