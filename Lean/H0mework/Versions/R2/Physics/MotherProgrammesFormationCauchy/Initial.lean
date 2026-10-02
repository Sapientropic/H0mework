import H0mework.Physics.JointVariation.GlobalDevelopmentOperator
import H0mework.Versions.R2.Physics.RootRuntime.RuntimeOccurrence
import H0mework.Versions.R2.Realization.SourceComparison.RawConsumption

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CauchyRecovery

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open StageNineCanonicalCauchyState StageNineP286ActionCauchySplit
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource StageNineJointActionCanonicalPhasePathLaw
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineFormNativeLorentzTorsionSpinEquation StageNineP286GaugeAuxiliaryVariation

noncomputable section

def motherSource : SmoothUnifiedSource := Runtime.source

/-- A deterministic extension of independent instantaneous data. No field
away from the initial slice is accepted from the caller. -/
def initialExtension (initial : StageNineCauchyState) : StageNineHolonomicConfiguration where
  coframe := fun point => initial.coframe (canonicalSpatialProjection point)
  gravityConnection := fun point => initial.gravityConnection (canonicalSpatialProjection point)
  gravityAuxiliary := fun point => initial.gravityAuxiliary (canonicalSpatialProjection point)
  gravitySimplicityMultiplier := fun point =>
    initial.gravitySimplicityMultiplier (canonicalSpatialProjection point)
  gaugeConnection := fun point => initial.gaugeConnection (canonicalSpatialProjection point)
  gaugeAuxiliary := fun point => initial.gaugeAuxiliary (canonicalSpatialProjection point)
  scalar := fun point => initial.scalar (canonicalSpatialProjection point) +
    canonicalTimeProjection point • initial.scalarVelocity (canonicalSpatialProjection point)
  matter := fun point => initial.matter (canonicalSpatialProjection point)
  conjugateMatter := fun point => initial.conjugateMatter (canonicalSpatialProjection point)

theorem initialExtension_scalar_line (initial : StageNineCauchyState)
    (time : ℝ) (space : StageNineSpatialPoint) :
    (initialExtension initial).scalar (canonicalCauchySlicePoint time space) =
      initial.scalar space + time • initial.scalarVelocity space := by
  simp [initialExtension]

theorem initialExtension_scalar_differentiable (initial : StageNineCauchyState)
    (scalar : Differentiable ℝ initial.scalar)
    (velocity : Differentiable ℝ initial.scalarVelocity) :
    Differentiable ℝ (initialExtension initial).scalar :=
  (scalar.comp canonicalSpatialProjection.differentiable).add
    (canonicalTimeProjection.differentiable.smul
      (velocity.comp canonicalSpatialProjection.differentiable))

theorem initialExtension_scalar_velocity (initial : StageNineCauchyState)
    (scalar : Differentiable ℝ initial.scalar)
    (velocity : Differentiable ℝ initial.scalarVelocity)
    (space : StageNineSpatialPoint) :
    fieldDirectionalDerivative (initialExtension initial).scalar
      (canonicalCauchySlicePoint 0 space) canonicalLorentzianTimeDirection =
      initial.scalarVelocity space := by
  have actual := field_timeLine_hasDerivAt (initialExtension initial).scalar space 0
    (initialExtension_scalar_differentiable initial scalar velocity).differentiableAt
  have prescribed : HasDerivAt
      (fun time => (initialExtension initial).scalar (canonicalCauchySlicePoint time space))
      (initial.scalarVelocity space) 0 := by
    simpa only [initialExtension_scalar_line] using
      hasDerivAt_const_add_time_smul (initial.scalar space) (initial.scalarVelocity space) 0
  exact actual.unique prescribed

theorem initialExtension_recovers_initial (initial : StageNineCauchyState)
    (scalar : Differentiable ℝ initial.scalar)
    (velocity : Differentiable ℝ initial.scalarVelocity) :
    canonicalCauchyRestriction 0 (initialExtension initial) = initial := by
  apply StageNineCauchyState.ext
  · funext space; simp [canonicalCauchyRestriction, initialExtension]
  · funext space; simp [canonicalCauchyRestriction, initialExtension]
  · funext space; simp [canonicalCauchyRestriction, initialExtension]
  · funext space; simp [canonicalCauchyRestriction, initialExtension]
  · funext space; simp [canonicalCauchyRestriction, initialExtension]
  · funext space; simp [canonicalCauchyRestriction, initialExtension]
  · funext space; simp [canonicalCauchyRestriction, initialExtension]
  · funext space; exact initialExtension_scalar_velocity initial scalar velocity space
  · funext space; simp [canonicalCauchyRestriction, initialExtension]
  · funext space; simp [canonicalCauchyRestriction, initialExtension]

/-- The current Dirac-dual form-native writer consumes the generated initial
extension, including its independent conjugate-matter data. -/
def firstDevelopment (initial : StageNineCauchyState) : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator motherSource
    (initialExtension initial)

/-- The same current-epoch writer regenerates each complete spacetime field.
This is a computational index; physical time remains the field's coordinate. -/
abbrev dynamics (initial : StageNineCauchyState) : RawGeneratedRoot.Dynamics where
  State := StageNineHolonomicConfiguration
  EventAt := fun _ => PUnit
  initial := initialExtension initial
  emit := fun _ => PUnit.unit
  update := fun {current} _ =>
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator motherSource current

theorem first_generated (initial : StageNineCauchyState) :
    RawGeneratedRoot.currentAt (dynamics initial) 1 = firstDevelopment initial := rfl

theorem initial_data_recovered (initial : StageNineCauchyState)
    (scalar : Differentiable ℝ initial.scalar)
    (velocity : Differentiable ℝ initial.scalarVelocity) :
    canonicalCauchyRestriction 0 (RawGeneratedRoot.currentAt (dynamics initial) 0) = initial :=
  initialExtension_recovers_initial initial scalar velocity

set_option maxHeartbeats 2000000 in
/-- Every generated complete-field write is consumed by the existing
form-native gravity equations, exact row transfer, and source next. -/
theorem generated_write_consumed (initial : StageNineCauchyState) (index : ℕ) :
    let D := dynamics initial
    let current := RawGeneratedRoot.currentAt D index
    let successor := RawGeneratedRoot.generatedSuccessor D (state := current) PUnit.unit
    successor.targetCurrent = RawGeneratedRoot.currentAt D (index + 1) ∧
    FormNativeGravitySimplicityEquation successor.targetCurrent ∧
    FormNativeGravityAuxiliaryEquation successor.targetCurrent ∧
    successor.ledgerEvolution.destination (RawGeneratedRoot.entry D current) =
      ⟨RawGeneratedRoot.entry D successor.targetCurrent,
        .transferred PUnit.unit rfl rfl (Nat.le_refl _)⟩ := by
  exact ⟨rfl,
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_simplicity _ _,
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_gravityAuxiliaryEquation _ _,
    RawGeneratedRoot.generated_ledger (dynamics initial)
      (state := RawGeneratedRoot.currentAt (dynamics initial) index) PUnit.unit⟩

theorem generated_coframe (initial : StageNineCauchyState) (index : ℕ) :
    (RawGeneratedRoot.currentAt (dynamics initial) index).coframe =
      (initialExtension initial).coframe := by
  induction index with
  | zero => rfl
  | succ index previous =>
    change (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator motherSource
      (RawGeneratedRoot.currentAt (dynamics initial) index)).coframe = _
    exact (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_coframe
      motherSource _).trans previous

theorem generated_nondegenerate (initial : StageNineCauchyState)
    (nondegenerate : ∀ space, Matrix.det (initial.coframe space) ≠ 0) (index : ℕ) :
    (RawGeneratedRoot.currentAt (dynamics initial) index).Nondegenerate := by
  intro point
  rw [generated_coframe]
  exact nondegenerate (canonicalSpatialProjection point)

private theorem preCartan_coframe (current : StageNineHolonomicConfiguration) :
    (completeJointGlobalP286Current motherSource current).coframe = current.coframe := by
  simpa only [sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe] using
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_coframe motherSource current

theorem generated_torsion_spin (initial : StageNineCauchyState)
    (nondegenerate : ∀ space, Matrix.det (initial.coframe space) ≠ 0) (index : ℕ) :
    FormNativeIIPlusTorsionSpinEquation motherSource
      (RawGeneratedRoot.currentAt (dynamics initial) (index + 1)) := by
  apply sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_torsionSpin
  intro point
  rw [preCartan_coframe]
  exact generated_nondegenerate initial nondegenerate index point

/-- The developed gauge auxiliary retains the newly generated algebraic
anchor, rather than asserting that every raw initial auxiliary is unchanged. -/
theorem generated_zero_slice (initial : StageNineCauchyState) (index : ℕ)
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryCoordinate
      (RawGeneratedRoot.currentAt (dynamics initial) (index + 1))
      (canonicalCauchySlicePoint 0 space) =
    holonomicP286GaugeAuxiliaryCoordinate
      (completeJointGlobalP286AlgebraicCurrent motherSource
        (RawGeneratedRoot.currentAt (dynamics initial) index))
      (canonicalCauchySlicePoint 0 space) :=
  sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_gaugeAuxiliary_zeroSlice
    motherSource _ space

def faithfulExecution (initial : StageNineCauchyState) :
    Σ process : CausalCore.Process (RawGeneratedRoot.root (dynamics initial)).toAnswerNextCausalWorld,
      CausalCore.FaithfulRealization
        (RawGeneratedRoot.root (dynamics initial)).toAnswerNextCausalWorld process :=
  RawGeneratedRoot.realization (dynamics initial)

theorem generated_next (initial : StageNineCauchyState)
    (visit : GroundedFaithfulRealization.Visit (RawGeneratedRoot.root (dynamics initial))) :
    let D := dynamics initial
    (RawGeneratedRoot.root D).generatedNextCurrentAt visit =
      ⟨RawGeneratedRoot.vocabulary D, (RawGeneratedRoot.root D).toAuthoritativeRoot,
        visit.next (next := D.update (D.emit visit.current)) rfl⟩ :=
  RawGeneratedRoot.next_current _ visit

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CauchyRecovery
