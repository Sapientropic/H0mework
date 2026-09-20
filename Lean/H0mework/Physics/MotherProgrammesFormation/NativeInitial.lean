import H0mework.Physics.MotherProgrammesFormationCauchy.Initial
import H0mework.Physics.MotherProgrammesFormation.NativeSource

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ActualInitial

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open StageNineCanonicalCauchyState StageNineHolonomicField
open StageNineP286ActionCauchySplit StageNineP286ActionConnectionVelocity
open StageNineEnrichedProofFreeSource ProofFreeRicherAnholonomicSource
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open Stage9C.Revision
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective

local instance p286CoordinateFintype : Fintype P286CoordinateIndex := Fintype.ofFinite _

/-- Regularity of the independent spatial Cauchy data only. -/
structure SmoothInitial (initial : StageNineCauchyState) : Prop where
  coframe : ∀ row column, ContDiff ℝ ∞ (fun space => initial.coframe space row column)
  gravityConnection : ∀ direction output input,
    ContDiff ℝ ∞ (fun space => initial.gravityConnection space direction output input)
  gravityAuxiliary : ∀ internalPair spacetimePair,
    ContDiff ℝ ∞ (fun space => initial.gravityAuxiliary space internalPair spacetimePair)
  gravitySimplicityMultiplier : ∀ internalPair spacetimePair,
    ContDiff ℝ ∞ (fun space =>
      initial.gravitySimplicityMultiplier space internalPair spacetimePair)
  gaugeConnection : ∀ direction,
    ContDiff ℝ ∞ (fun space => p286CoordinateEquiv (initial.gaugeConnection space direction))
  gaugeAuxiliary : ∀ pair,
    ContDiff ℝ ∞ (fun space => p286CoordinateEquiv (initial.gaugeAuxiliary space pair))
  scalar : ContDiff ℝ ∞ initial.scalar
  scalarVelocity : ContDiff ℝ ∞ initial.scalarVelocity
  matter : ContDiff ℝ ∞ (fun space => matterCoordinateEquiv (initial.matter space))
  conjugateMatter : ∀ index : MatterCoordinateIndex,
    ContDiff ℝ ∞ (fun space => initial.conjugateMatter space
      (matterCoordinateEquiv.symm (EuclideanSpace.single index 1)))

theorem extension_smooth (initial : StageNineCauchyState) (smooth : SmoothInitial initial) :
    (CauchyRecovery.initialExtension initial).Smooth := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro row column
    exact (smooth.coframe row column).comp canonicalSpatialProjection.contDiff
  · intro direction output input
    exact (smooth.gravityConnection direction output input).comp canonicalSpatialProjection.contDiff
  · intro internalPair spacetimePair
    exact (smooth.gravityAuxiliary internalPair spacetimePair).comp canonicalSpatialProjection.contDiff
  · intro internalPair spacetimePair
    exact (smooth.gravitySimplicityMultiplier internalPair spacetimePair).comp
      canonicalSpatialProjection.contDiff
  · intro direction
    exact (smooth.gaugeConnection direction).comp canonicalSpatialProjection.contDiff
  · intro pair
    exact (smooth.gaugeAuxiliary pair).comp canonicalSpatialProjection.contDiff
  · exact (smooth.scalar.comp canonicalSpatialProjection.contDiff).add
      (canonicalTimeProjection.contDiff.smul
        (smooth.scalarVelocity.comp canonicalSpatialProjection.contDiff))
  · exact smooth.matter.comp canonicalSpatialProjection.contDiff
  · intro index
    exact (smooth.conjugateMatter index).comp canonicalSpatialProjection.contDiff

theorem extension_nondegenerate (initial : StageNineCauchyState)
    (nondegenerate : ∀ space, Matrix.det (initial.coframe space) ≠ 0) :
    (CauchyRecovery.initialExtension initial).Nondegenerate :=
  fun point => nondegenerate (canonicalSpatialProjection point)

theorem initial_recovered (initial : StageNineCauchyState) (smooth : SmoothInitial initial) :
    canonicalCauchyRestriction 0 (CauchyRecovery.initialExtension initial) = initial :=
  CauchyRecovery.initialExtension_recovers_initial initial
    (smooth.scalar.differentiable (by simp))
    (smooth.scalarVelocity.differentiable (by simp))

/-- The source's constitutive writer prepares its own auxiliary field from
the independently generated extension. -/
def state (initial : StageNineCauchyState) (smooth : SmoothInitial initial)
    (nondegenerate : ∀ space, Matrix.det (initial.coframe space) ≠ 0) : MaterialState :=
  ActualSourceCoverage.preparedState (CauchyRecovery.initialExtension initial)
    (extension_smooth initial smooth) (extension_nondegenerate initial nondegenerate)

set_option maxHeartbeats 2000000 in
/-- This operand is consumed by the original source/event algebra and its
complete ledger compiler. No new root or temporal visit is constructed. -/
theorem native_consumed (initial : StageNineCauchyState) (smooth : SmoothInitial initial)
    (nondegenerate : ∀ space, Matrix.det (initial.coframe space) ≠ 0) :
    let prepared := state initial smooth nondegenerate
    let successor := ActualSourceCoverage.successor prepared
    SpinPair.source.toRootSource.actual.compile (ActualSourceCoverage.occurrence prepared) =
      .nativeWrite (materialActionAt (SpinPair.underlying (.running prepared))) ∧
    successor.targetCurrent = SpinPair.next (.running prepared) ∧
    Recognition.wholeField successor.targetCurrent =
      Stage9C.Reduction.p286CartanNext positiveSmoothUnifiedSource prepared.current
        prepared.smooth prepared.nondegenerate 0 ∧
    successor.ledgerEvolution.destination (materialEntry (SpinPair.support (.running prepared))) =
      ⟨materialEntry (SpinPair.support (SpinPair.next (.running prepared))),
        .transferred (.transfer (materialActionAt (SpinPair.underlying (.running prepared))))
          rfl rfl (Nat.le_refl _)⟩ := by
  exact ⟨rfl, ActualSourceCoverage.successor_native _,
    ActualSourceCoverage.actual_whole_write _, rfl⟩

private theorem zeroSlice_contDiff : ContDiff ℝ ∞ (canonicalCauchySlicePoint 0) := by
  rw [show canonicalCauchySlicePoint 0 = canonicalSpatialInclusion by
    funext space
    rw [canonicalCauchySlicePoint_eq_const_add_inclusion]
    simp]
  exact canonicalSpatialInclusion.contDiff

/-- The source's existing smooth complete field supplies regular independent
zero-slice data, including the scalar velocity. -/
theorem slice_smooth (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    SmoothInitial (canonicalCauchyRestriction 0 configuration) where
  coframe := fun row column => (smooth.1 row column).comp zeroSlice_contDiff
  gravityConnection := fun direction output input =>
    (smooth.2.1 direction output input).comp zeroSlice_contDiff
  gravityAuxiliary := fun internalPair spacetimePair =>
    (smooth.2.2.1 internalPair spacetimePair).comp zeroSlice_contDiff
  gravitySimplicityMultiplier := fun internalPair spacetimePair =>
    (smooth.2.2.2.1 internalPair spacetimePair).comp zeroSlice_contDiff
  gaugeConnection := fun direction => (smooth.2.2.2.2.1 direction).comp zeroSlice_contDiff
  gaugeAuxiliary := fun pair => (smooth.2.2.2.2.2.1 pair).comp zeroSlice_contDiff
  scalar := smooth.2.2.2.2.2.2.1.comp zeroSlice_contDiff
  scalarVelocity := by
    have derivative := (smooth.2.2.2.2.2.2.1.fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiff_const : ContDiff ℝ ∞ (fun _ : BasePoint =>
        coordinateDirection canonicalLorentzianTimeDirection))
    exact derivative.comp zeroSlice_contDiff
  matter := smooth.2.2.2.2.2.2.2.1.comp zeroSlice_contDiff
  conjugateMatter := fun index => (smooth.2.2.2.2.2.2.2.2 index).comp zeroSlice_contDiff

def originalInitial : StageNineCauchyState := canonicalCauchyRestriction 0 Runtime.configuration

theorem originalInitial_smooth : SmoothInitial originalInitial :=
  slice_smooth Runtime.configuration Recovery.stageOneThroughTenClosure.final.classical.smooth

theorem originalInitial_nondegenerate :
    ∀ space, Matrix.det (originalInitial.coframe space) ≠ 0 :=
  fun space => Recovery.stageOneThroughTenClosure.final.classical.nondegenerate
    (canonicalCauchySlicePoint 0 space)

def originalState : MaterialState :=
  state originalInitial originalInitial_smooth originalInitial_nondegenerate

theorem original_initial_recovered :
    canonicalCauchyRestriction 0 (CauchyRecovery.initialExtension originalInitial) = originalInitial :=
  initial_recovered originalInitial originalInitial_smooth

theorem original_whole_write :
    Recognition.wholeField (ActualSourceCoverage.successor originalState).targetCurrent =
      Stage9C.Reduction.p286CartanNext positiveSmoothUnifiedSource originalState.current
        originalState.smooth originalState.nondegenerate 0 :=
  ActualSourceCoverage.actual_whole_write originalState

theorem original_next :
    (ActualSourceCoverage.successor originalState).targetCurrent =
      SpinPair.next (.running originalState) :=
  ActualSourceCoverage.successor_native originalState

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ActualInitial
