import H0mework.Versions.R2.Physics.MotherProgrammesFormationCoordinates.WholeCarrier

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.WholePointFormation

open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineDiracDualFormNativeJointResidualCarrier StageNineDiracDualFormNativeMotherAction
open StageNineP286SourceNativeCenteredReducedEntropySafeStep StageNineP286SourceNativeReducedEntropyDescent
open Stage9C.Reduction Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open MotherFamilyOccurrence

noncomputable section

def source (visit : MotherVisit) (value : Carrier) : SmoothUnifiedSource :=
  PotentialSourceFormation.sourceOf visit (points value)

def field (visit : MotherVisit) (value : Carrier) : StageNineHolonomicConfiguration :=
  materialField (source visit value)

def action (visit : MotherVisit) (value : Carrier) (chart : StageNineChart) (point : BasePoint) : ℝ :=
  sourceGeneratedDiracDualFormNativeUnifiedLocalDensity (source visit value) chart point
    (toContinuumPointField (field visit value) point)

/-- The same complete source-generated operand supplies both the actual
mother potential and every physical consumer, including all spatial coordinates. -/
theorem native_consumed (visit : MotherVisit) (value : Carrier)
    (center : BasePoint) (epoch : ℕ) (point : BasePoint)
    (ambient : Module.End ℂ DiracExteriorMatterCarrier) :
    let formed := source visit value
    let current := GeneralSourceEvolution.stateAt formed center epoch
    let target := GeneralSourceEvolution.stateAt formed center (epoch + 1)
    pointEquiv.symm (points value) = value ∧
      (∀ slot, curvatureRate (generatedMotherPotential Runtime.source (points value slot) 1) =
        coordinate value slot 0) ∧
      (∀ (slot : Fin 65) (axis : Fin 3), points value slot axis.succ = coordinate value slot axis.succ) ∧
      target = GeneralSourceEvolution.next formed center current ∧
      target.current = p286CartanNext formed current.current current.smooth current.nondegenerate center ∧
      target.current = field visit value ∧
      DiracDualFormNativeJointZeroFiber formed target.current ∧
      target.current.coframe point = homogeneousCoframe (sourceClock formed) ∧
      actualRelativeAction formed current.current target.current =
        p286CenteredReducedRelativeAction formed current.current current.smooth current.nondegenerate center ∧
      actualRelativeAction formed current.current target.current = 0 ∧
      target.current.conjugateMatter point (ambient (target.current.matter point)) =
        4 * (spinScale : ℂ) * Stage9DEF.State.vectorEvaluation
          (Stage9DEF.Source.restrict target.current point) (Stage9DEF.Compatibility.responseMatrix ambient) := by
  refine ⟨pointEquiv.symm_apply_apply value, actual_material value, ?_,
    GeneralSourceEvolution.whole_native_consumed (source visit value) center epoch point ambient⟩
  intro slot axis
  exact actual_spatial value slot axis

/-- The target and spatial values occur in the coverage conclusion, after
formation of the entire coordinate carrier and its physical factory. -/
theorem every_source_realized (target : SmoothUnifiedSource)
    (spatial : PotentialSourceFormation.SpatialRemainders) (chart : StageNineChart) (point : BasePoint) :
    ∃ code, ∃ value : Carrier,
      source (Stage9C.Revision.SpinPair.visit (10 + code)) value = target ∧
      PotentialSourceFormation.remainders (points value) = spatial ∧
      field (Stage9C.Revision.SpinPair.visit (10 + code)) value = materialField target ∧
      DiracDualFormNativeJointZeroFiber target
        (field (Stage9C.Revision.SpinPair.visit (10 + code)) value) ∧
      action (Stage9C.Revision.SpinPair.visit (10 + code)) value chart point =
        sourceGeneratedDiracDualFormNativeUnifiedLocalDensity target chart point
          (toContinuumPointField (materialField target) point) := by
  obtain ⟨code, operands, generated, retained⟩ :=
    PotentialSourceFormation.every_source_generated target spatial
  let value := pointEquiv.symm operands
  have recovered : points value = operands := pointEquiv.apply_symm_apply operands
  have formed : source (Stage9C.Revision.SpinPair.visit (10 + code)) value = target := by
    unfold source
    rw [recovered]
    exact generated
  refine ⟨code, value, formed, recovered ▸ retained, ?_, ?_, ?_⟩
  · unfold field
    rw [formed]
  · unfold field
    rw [formed]
    exact ArbitrarySourceFormation.material_joint_zero target
  · unfold action field
    rw [formed]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.WholePointFormation
