import H0mework.Physics.MotherProgrammesFormationCoordinates.Completion
import H0mework.Physics.MotherProgrammesFormationPotential.History

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCoordinateCompletion

open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineDiracDualFormNativeJointResidualCarrier StageNineDiracDualFormNativeMotherAction
open StageNineP286SourceNativeCenteredReducedEntropySafeStep StageNineP286SourceNativeReducedEntropyDescent
open Stage9C.Reduction Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open MotherFamilyOccurrence

noncomputable section

/-- Completion supplies the 65 material coordinates; the actual 195 spatial
coordinates are retained separately in the complete point presentation. -/
abbrev PointPresentation := Completed 65 × PotentialSourceFormation.SpatialRemainders

def points (data : PointPresentation) : PotentialSourceFormation.Points :=
  PotentialSourceFormation.restorePoints (realEquiv 65 data.1) data.2

theorem points_materials (data : PointPresentation) :
    PotentialSourceFormation.materials (points data) = realEquiv 65 data.1 :=
  PotentialSourceFormation.materials_restored _ _

theorem points_spatial (data : PointPresentation) :
    PotentialSourceFormation.remainders (points data) = data.2 :=
  PotentialSourceFormation.remainders_restored _ _

def pointPresentationEquiv : PointPresentation ≃ PotentialSourceFormation.Points where
  toFun := points
  invFun value := ((realEquiv 65).symm (PotentialSourceFormation.materials value),
    PotentialSourceFormation.remainders value)
  left_inv data := by
    apply Prod.ext
    · change (realEquiv 65).symm (PotentialSourceFormation.materials (points data)) = data.1
      rw [points_materials, (realEquiv 65).symm_apply_apply]
    · exact points_spatial data
  right_inv value := by
    change PotentialSourceFormation.restorePoints
      (realEquiv 65 ((realEquiv 65).symm (PotentialSourceFormation.materials value)))
      (PotentialSourceFormation.remainders value) = value
    rw [(realEquiv 65).apply_symm_apply]
    exact PotentialSourceFormation.points_recovered value

theorem actual_potential_coordinate (data : PointPresentation) (slot : Fin 65) :
    curvatureRate (generatedMotherPotential Runtime.source (points data slot) 1) =
      realEquiv 65 data.1 slot :=
  congrFun (points_materials data) slot

theorem finite_potential_agrees (visit : MotherVisit)
    (spatial : PotentialSourceFormation.SpatialRemainders) (slot : Fin 65) :
    curvatureRate (generatedMotherPotential Runtime.source
      (points ((fromVisit 65 visit : Completed 65), spatial) slot) 1) =
      RationalSourceFormation.sourceTrace
        (StageEightDiscreteFormation.sourceAtVisit (sample 65 visit slot)) := by
  rw [actual_potential_coordinate]
  exact finite_native_read 65 visit slot

def source (visit : MotherVisit) (data : PointPresentation) : SmoothUnifiedSource :=
  PotentialSourceFormation.sourceOf visit (points data)

def field (visit : MotherVisit) (data : PointPresentation) : StageNineHolonomicConfiguration :=
  materialField (source visit data)

def action (visit : MotherVisit) (data : PointPresentation) (chart : StageNineChart) (point : BasePoint) : ℝ :=
  sourceGeneratedDiracDualFormNativeUnifiedLocalDensity (source visit data) chart point
    (toContinuumPointField (field visit data) point)

theorem native_consumed (visit : MotherVisit) (data : PointPresentation)
    (center : BasePoint) (epoch : ℕ) (point : BasePoint)
    (ambient : Module.End ℂ DiracExteriorMatterCarrier) :
    let current := GeneralSourceEvolution.stateAt (source visit data) center epoch
    let target := GeneralSourceEvolution.stateAt (source visit data) center (epoch + 1)
    PotentialSourceFormation.materials (points data) = realEquiv 65 data.1 ∧
      PotentialSourceFormation.remainders (points data) = data.2 ∧
      target = GeneralSourceEvolution.next (source visit data) center current ∧
      target.current = p286CartanNext (source visit data) current.current
        current.smooth current.nondegenerate center ∧
      target.current = field visit data ∧
      DiracDualFormNativeJointZeroFiber (source visit data) target.current ∧
      target.current.coframe point = homogeneousCoframe (sourceClock (source visit data)) ∧
      actualRelativeAction (source visit data) current.current target.current =
        p286CenteredReducedRelativeAction (source visit data) current.current
          current.smooth current.nondegenerate center ∧
      actualRelativeAction (source visit data) current.current target.current = 0 ∧
      target.current.conjugateMatter point (ambient (target.current.matter point)) =
        4 * (spinScale : ℂ) * Stage9DEF.State.vectorEvaluation
          (Stage9DEF.Source.restrict target.current point) (Stage9DEF.Compatibility.responseMatrix ambient) :=
  ⟨points_materials data, points_spatial data,
    GeneralSourceEvolution.whole_native_consumed (source visit data) center epoch point ambient⟩

/-- Target values appear only in this coverage theorem. The carrier and its
canonical realization were constructed from the fixed rational source image. -/
theorem every_source_realized (target : SmoothUnifiedSource)
    (spatial : PotentialSourceFormation.SpatialRemainders) (chart : StageNineChart) (point : BasePoint) :
    ∃ code, ∃ value : Completed 65,
      source (Stage9C.Revision.SpinPair.visit (10 + code)) (value, spatial) = target ∧
      PotentialSourceFormation.remainders (points (value, spatial)) = spatial ∧
      field (Stage9C.Revision.SpinPair.visit (10 + code)) (value, spatial) = materialField target ∧
      DiracDualFormNativeJointZeroFiber target
        (field (Stage9C.Revision.SpinPair.visit (10 + code)) (value, spatial)) ∧
      action (Stage9C.Revision.SpinPair.visit (10 + code)) (value, spatial) chart point =
        sourceGeneratedDiracDualFormNativeUnifiedLocalDensity target chart point
          (toContinuumPointField (materialField target) point) := by
  obtain ⟨code, operands, generated, retained⟩ :=
    PotentialSourceFormation.every_source_generated target spatial
  let value := (realEquiv 65).symm (PotentialSourceFormation.materials operands)
  have recovered : points (value, spatial) = operands := by
    unfold points value
    rw [(realEquiv 65).apply_symm_apply, ← retained]
    exact PotentialSourceFormation.points_recovered operands
  have source_eq : source (Stage9C.Revision.SpinPair.visit (10 + code)) (value, spatial) = target := by
    unfold source
    rw [recovered]
    exact generated
  refine ⟨code, value, source_eq, points_spatial _, ?_, ?_, ?_⟩
  · unfold field
    rw [source_eq]
  · unfold field
    rw [source_eq]
    exact ArbitrarySourceFormation.material_joint_zero target
  · unfold action field
    rw [source_eq]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCoordinateCompletion
