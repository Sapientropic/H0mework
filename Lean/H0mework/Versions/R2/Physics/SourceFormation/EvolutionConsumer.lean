import H0mework.Versions.R2.Physics.SourceFormation.EvolutionState
import H0mework.Versions.R2.Physics.SourceFamily.QuantumEvolution

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.GeneralSourceEvolution

open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineDynamicBreakingVacuum
open StageNineDiracDualFormNativeJointResidualCarrier StageNineDiracDualFormNativeMotherAction
open StageNineP286SourceNativeCenteredReducedEntropyIteration
open StageNineP286SourceNativeCenteredReducedEntropySafeStep
open StageNineP286SourceNativeReducedEntropyDescent
open Stage9C.Reduction Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous

noncomputable section

def occupied (source : SmoothUnifiedSource) : Stage9DEF.Source.OccupiedField :=
  Stage9DEF.Source.restrict (MotherFamilyOccurrence.materialField source)

theorem occupied_family (source : SmoothUnifiedSource) :
    occupied source = SourceFamilyEvolution.Quantum.occupied (ArbitrarySourceFormation.index source) := by
  unfold occupied SourceFamilyEvolution.Quantum.occupied Stage9DEF.Source.restrict
  rw [← ArbitrarySourceFormation.material_field_eq, ArbitrarySourceFormation.matter_eq]

theorem occupied_formula (source : SmoothUnifiedSource) (point : BasePoint) (index : Stage9DEF.Source.Index) :
    occupied source point index = spinPairCoefficients
      (phase (MotherFamilyOccurrence.sourcePhaseRate source) point)
      (phase (-MotherFamilyOccurrence.sourcePhaseRate source) point) index.1 index.2 / 2 := by
  rw [occupied_family, SourceFamilyEvolution.Quantum.occupied_formula,
    ArbitrarySourceFormation.source_phase_eq]

theorem occupied_normalized (source : SmoothUnifiedSource) (point : BasePoint) :
    (∑ index : Stage9DEF.Source.Index, star (occupied source point index) * occupied source point index) = 1 := by
  rw [occupied_family]
  exact SourceFamilyEvolution.Quantum.occupied_inner_self (ArbitrarySourceFormation.index source) point

theorem quantum_response (source : SmoothUnifiedSource) (point : BasePoint)
    (action : Module.End ℂ DiracExteriorMatterCarrier) :
    (MotherFamilyOccurrence.materialField source).conjugateMatter point
        (action ((MotherFamilyOccurrence.materialField source).matter point)) =
      4 * (spinScale : ℂ) * Stage9DEF.State.vectorEvaluation
        (occupied source point) (Stage9DEF.Compatibility.responseMatrix action) := by
  rw [occupied_family, ← ArbitrarySourceFormation.material_field_eq,
    ArbitrarySourceFormation.matter_eq, ArbitrarySourceFormation.dual_eq]
  exact SourceFamilyEvolution.Quantum.action_response (ArbitrarySourceFormation.index source) point action

theorem physical_coframe (source : SmoothUnifiedSource) (center : BasePoint) (epoch : ℕ)
    (point : BasePoint) :
    (stateAt source center epoch).current.coframe point =
      homogeneousCoframe (MotherFamilyOccurrence.sourceClock source) := by
  rw [whole_current]
  rfl

theorem actual_action_generated (source : SmoothUnifiedSource) (center : BasePoint) (epoch : ℕ) :
    actualRelativeAction source (stateAt source center epoch).current
      (stateAt source center (epoch + 1)).current =
      p286CenteredReducedRelativeAction source (stateAt source center epoch).current
        (stateAt source center epoch).smooth (stateAt source center epoch).nondegenerate center :=
  p286CartanStateNext_actualRelativeAction center (stateAt source center epoch) (cartan_fixed source center epoch)

theorem actual_action_zero (source : SmoothUnifiedSource) (center : BasePoint) (epoch : ℕ) :
    actualRelativeAction source (stateAt source center epoch).current
      (stateAt source center (epoch + 1)).current = 0 := by
  rw [whole_current, whole_current]
  simp [actualRelativeAction]

theorem pointwise_action_increment (source : SmoothUnifiedSource) (center : BasePoint) (epoch : ℕ)
    (chart : StageNineChart) (point : BasePoint) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point
        (toContinuumPointField (stateAt source center (epoch + 1)).current point) -
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point
        (toContinuumPointField (stateAt source center epoch).current point) = 0 := by
  rw [whole_current, whole_current, sub_self]

theorem current_quantum_response (source : SmoothUnifiedSource) (center : BasePoint) (epoch : ℕ)
    (point : BasePoint) (action : Module.End ℂ DiracExteriorMatterCarrier) :
    (stateAt source center epoch).current.conjugateMatter point
        (action ((stateAt source center epoch).current.matter point)) =
      4 * (spinScale : ℂ) * Stage9DEF.State.vectorEvaluation
        (Stage9DEF.Source.restrict (stateAt source center epoch).current point)
        (Stage9DEF.Compatibility.responseMatrix action) := by
  rw [whole_current]
  exact quantum_response source point action

/-- One raw source supplies the original complete write, full Euler field,
physical clock and ambient-action response at the unchanged spacetime point. -/
theorem whole_native_consumed (source : SmoothUnifiedSource) (center : BasePoint) (epoch : ℕ)
    (point : BasePoint) (action : Module.End ℂ DiracExteriorMatterCarrier) :
    let current := stateAt source center epoch
    let target := stateAt source center (epoch + 1)
    target = next source center current ∧
      target.current = p286CartanNext source current.current current.smooth current.nondegenerate center ∧
      target.current = MotherFamilyOccurrence.materialField source ∧
      DiracDualFormNativeJointZeroFiber source target.current ∧
      target.current.coframe point = homogeneousCoframe (MotherFamilyOccurrence.sourceClock source) ∧
      actualRelativeAction source current.current target.current =
        p286CenteredReducedRelativeAction source current.current current.smooth current.nondegenerate center ∧
      actualRelativeAction source current.current target.current = 0 ∧
      target.current.conjugateMatter point (action (target.current.matter point)) =
        4 * (spinScale : ℂ) * Stage9DEF.State.vectorEvaluation
          (Stage9DEF.Source.restrict target.current point) (Stage9DEF.Compatibility.responseMatrix action) :=
  ⟨state_succ _ _ _, whole_write _ _ _, whole_current _ _ _, current_joint_zero _ _ _,
    physical_coframe _ _ _ _, actual_action_generated _ _ _, actual_action_zero _ _ _,
    current_quantum_response _ _ _ _ _⟩

theorem zero_phase_current (center : BasePoint) (epoch : ℕ) :
    sourceGeneratedVacuumBase zeroPhaseSmoothUnifiedSource = 0 ∧
      DiracDualFormNativeJointZeroFiber zeroPhaseSmoothUnifiedSource
        (stateAt zeroPhaseSmoothUnifiedSource center epoch).current ∧
      (stateAt zeroPhaseSmoothUnifiedSource center (epoch + 1)).current =
        MotherFamilyOccurrence.materialField zeroPhaseSmoothUnifiedSource :=
  ⟨zeroPhase_sourceGeneratedVacuumBase, current_joint_zero _ _ _, whole_current _ _ _⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.GeneralSourceEvolution
