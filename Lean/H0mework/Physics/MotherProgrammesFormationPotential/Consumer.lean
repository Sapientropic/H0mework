import H0mework.Physics.MotherProgrammesFormationPotential.Assembly
import H0mework.Physics.SourceFormation.EvolutionConsumer

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.PotentialSourceFormation

open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineGravityBianchi
open StageNineCClassicalWorldAcceptance StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeMotherAction
open StageNineP286SourceNativeCenteredReducedEntropySafeStep
open StageNineP286SourceNativeReducedEntropyDescent
open Stage9C.Reduction Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous MotherFamilyOccurrence

noncomputable section

def fieldOf (visit : MotherVisit) (points : Points) : StageNineHolonomicConfiguration :=
  materialField (sourceOf visit points)

def actionOf (visit : MotherVisit) (points : Points) (chart : StageNineChart) (point : BasePoint) : ℝ :=
  sourceGeneratedDiracDualFormNativeUnifiedLocalDensity (sourceOf visit points) chart point
    (toContinuumPointField (fieldOf visit points) point)

theorem complete_physical_generated (visit : MotherVisit) (points : Points) :
    (fieldOf visit points).Smooth ∧ (fieldOf visit points).Nondegenerate ∧
      GravityConnectionLorentzAdmissible (fieldOf visit points) ∧
      DiracDualFormNativeJointZeroFiber (sourceOf visit points) (fieldOf visit points) ∧
      DynamicScalarSourceContactAtOrigin (sourceOf visit points) (fieldOf visit points) :=
  ArbitrarySourceFormation.material_realization _

theorem source_displacement_consumed (visit : MotherVisit) (points displacement : Points) :
    (∀ slot,
      generatedMotherPotential Runtime.source (points slot + displacement slot) 1 =
        generatedMotherPotential Runtime.source (points slot) 1 +
          generatedMotherPotential Runtime.source (displacement slot) 1) ∧
      ((sourceOf visit (points + displacement)).stageEight.coframeLinearCoefficient -
          (sourceOf visit points).stageEight.coframeLinearCoefficient = coframeMaterials displacement ∧
        (sourceOf visit (points + displacement)).continuousContactResidual -
          (sourceOf visit points).continuousContactResidual = materials displacement 0) ∧
      remainders (points + displacement) = remainders points + remainders displacement ∧
      restorePoints (materials (points + displacement)) (remainders (points + displacement)) =
        points + displacement :=
  ⟨fun slot => potential_increment (points slot) (displacement slot),
    source_material_increment visit points displacement, remainders_increment points displacement,
    points_recovered (points + displacement)⟩

/-- The full operands and their unused spatial coordinates remain available
beside the source image. The original generic writer consumes that same source. -/
theorem source_native_consumed (visit : MotherVisit) (points : Points) (center : BasePoint)
    (epoch : ℕ) (point : BasePoint) (action : Module.End ℂ DiracExteriorMatterCarrier) :
    let source := sourceOf visit points
    let current := GeneralSourceEvolution.stateAt source center epoch
    let target := GeneralSourceEvolution.stateAt source center (epoch + 1)
    source.stageEight.coframeLinearCoefficient = coframeMaterials points ∧
      source.continuousContactResidual = materials points 0 ∧
      restorePoints (materials points) (remainders points) = points ∧
      target = GeneralSourceEvolution.next source center current ∧
      target.current = p286CartanNext source current.current current.smooth current.nondegenerate center ∧
      target.current = materialField source ∧
      DiracDualFormNativeJointZeroFiber source target.current ∧
      target.current.coframe point = homogeneousCoframe (sourceClock source) ∧
      actualRelativeAction source current.current target.current =
        p286CenteredReducedRelativeAction source current.current current.smooth current.nondegenerate center ∧
      actualRelativeAction source current.current target.current = 0 ∧
      target.current.conjugateMatter point (action (target.current.matter point)) =
        4 * (spinScale : ℂ) * Stage9DEF.State.vectorEvaluation
          (Stage9DEF.Source.restrict target.current point) (Stage9DEF.Compatibility.responseMatrix action) :=
  ⟨rfl, rfl, points_recovered points,
    GeneralSourceEvolution.whole_native_consumed (sourceOf visit points) center epoch point action⟩

theorem every_source_realized (source : SmoothUnifiedSource) (spatial : SpatialRemainders)
    (chart : StageNineChart) (point : BasePoint) :
    ∃ code points,
      sourceOf (Stage9C.Revision.SpinPair.visit (10 + code)) points = source ∧
      remainders points = spatial ∧
      fieldOf (Stage9C.Revision.SpinPair.visit (10 + code)) points = materialField source ∧
      DiracDualFormNativeJointZeroFiber source (fieldOf (Stage9C.Revision.SpinPair.visit (10 + code)) points) ∧
      actionOf (Stage9C.Revision.SpinPair.visit (10 + code)) points chart point =
        sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point
          (toContinuumPointField (materialField source) point) := by
  obtain ⟨code, points, generated, retained⟩ := every_source_generated source spatial
  refine ⟨code, points, generated, retained, congrArg materialField generated, ?_, ?_⟩
  · rw [fieldOf, generated]
    exact ArbitrarySourceFormation.material_joint_zero source
  · unfold actionOf fieldOf
    rw [generated]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.PotentialSourceFormation
