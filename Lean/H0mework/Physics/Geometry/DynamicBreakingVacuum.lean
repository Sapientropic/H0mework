import H0mework.Physics.Geometry.FullMotherDescentAndTransport
import H0mework.Physics.Matter.SU7ExteriorYukawaMassSpectrum
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Stage-9B source-generated dynamic breaking vacuum

The Stage-8 joint `Λ⁴V` scalar is no longer installed as a final vacuum.
The proof-free source phase generates a base scalar, the generated transition
produces its local representatives, and a source-frame-relative quadratic
potential dynamically selects those representatives as its unique global
minimum.  The potential has an actual Fréchet derivative in finite
`Λ⁴V` coordinates and its generated vacuum is stationary.

Gauge descent is proved by transforming the scalar and generated frame
together.  The exact stabilizer is classified by all 35 exterior-basis
coordinate equations; on the embedded hypercharge circle its intersection is
proved to be exactly the identity, and the full stabilizer is proper.  At the
positive source origin the dynamically selected vacuum is exactly the one
joint scalar consumed by Stage 8, so the mass map and mixing readouts are
recovered.  The legacy one-channel explicit scalar and a zero-phase source
remain negative regressions.
-/

namespace SaturationMonoid.PhysicsCore.StageNineDynamicBreakingVacuum

open ProofFreeRicherAnholonomicSource
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7ExteriorBreakingYukawa
open SU7ExteriorYukawaMassSpectrum
open StageEightProofFreeSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalBundle

noncomputable section

abbrev ScalarBasisIndex := ExteriorBasisIndex 4
abbrev ScalarCoordinateCarrier := EuclideanSpace ℂ ScalarBasisIndex

def scalarCoordinateEquiv :
    ExteriorBreakingScalarCarrier ≃ₗ[ℂ] ScalarCoordinateCarrier :=
  (su7ExteriorBasis 4).repr ≪≫ₗ
    Finsupp.linearEquivFunOnFinite ℂ ℂ ScalarBasisIndex ≪≫ₗ
      (WithLp.linearEquiv 2 ℂ (ScalarBasisIndex → ℂ)).symm

def scalarCoordinateAction
    (groupElement : SU7MotherGroup)
    (coordinates : ScalarCoordinateCarrier) : ScalarCoordinateCarrier :=
  scalarCoordinateEquiv
    (exteriorBreakingScalarRepresentation groupElement
      (scalarCoordinateEquiv.symm coordinates))

@[simp] theorem scalarCoordinateAction_one
    (coordinates : ScalarCoordinateCarrier) :
    scalarCoordinateAction 1 coordinates = coordinates := by
  simp [scalarCoordinateAction]

theorem scalarCoordinateAction_mul
    (first second : SU7MotherGroup)
    (coordinates : ScalarCoordinateCarrier) :
    scalarCoordinateAction (first * second) coordinates =
      scalarCoordinateAction first (scalarCoordinateAction second coordinates) := by
  unfold scalarCoordinateAction
  rw [map_mul]
  rw [scalarCoordinateEquiv.symm_apply_apply]
  rw [Module.End.mul_apply]

theorem scalarCoordinateAction_add
    (groupElement : SU7MotherGroup)
    (first second : ScalarCoordinateCarrier) :
    scalarCoordinateAction groupElement (first + second) =
      scalarCoordinateAction groupElement first +
        scalarCoordinateAction groupElement second := by
  simp [scalarCoordinateAction]

def scalarCoordinateSquaredNorm
    (coordinates : ScalarCoordinateCarrier) : ℝ :=
  ∑ index : ScalarBasisIndex, Complex.normSq (coordinates index)

theorem scalarCoordinateSquaredNorm_nonneg
    (coordinates : ScalarCoordinateCarrier) :
    0 ≤ scalarCoordinateSquaredNorm coordinates := by
  exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

@[simp] theorem scalarCoordinateSquaredNorm_zero :
    scalarCoordinateSquaredNorm (0 : ScalarCoordinateCarrier) = 0 := by
  simp [scalarCoordinateSquaredNorm]

theorem scalarCoordinateSquaredNorm_eq_zero_iff
    (coordinates : ScalarCoordinateCarrier) :
    scalarCoordinateSquaredNorm coordinates = 0 ↔ coordinates = 0 := by
  constructor
  · intro sumZero
    apply PiLp.ext
    intro index
    apply Complex.normSq_eq_zero.mp
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => Complex.normSq_nonneg _)).mp sumZero index
      (Finset.mem_univ index)
  · rintro rfl
    simp [scalarCoordinateSquaredNorm]

def sourceGeneratedVacuumBase
    (source : SmoothUnifiedSource) : ExteriorBreakingScalarCarrier :=
  (source.stageEight.physicalPhaseAmplitude : ℂ) •
    finiteGenerationJointBreakingScalar

def sourceGeneratedVacuumCoordinates
    (source : SmoothUnifiedSource) : ScalarCoordinateCarrier :=
  scalarCoordinateEquiv (sourceGeneratedVacuumBase source)

@[simp] theorem positive_sourceGeneratedVacuumBase :
    sourceGeneratedVacuumBase positiveSmoothUnifiedSource =
      finiteGenerationJointBreakingScalar := by
  rw [sourceGeneratedVacuumBase]
  norm_num [positiveSmoothUnifiedSource, canonicalSource_physicalPhaseAmplitude]

theorem positive_sourceGeneratedVacuumBase_nonzero :
    sourceGeneratedVacuumBase positiveSmoothUnifiedSource ≠ 0 := by
  rw [positive_sourceGeneratedVacuumBase]
  exact finiteGenerationJointBreakingScalar_ne_zero

def generatedScalarFrame
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) : SU7MotherGroup :=
  generatedTransition source 0 chart point

def generatedLocalVacuumCoordinates
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) : ScalarCoordinateCarrier :=
  scalarCoordinateAction (generatedScalarFrame source chart point)
    (sourceGeneratedVacuumCoordinates source)

def scalarFrameRelativeCoordinates
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (coordinates : ScalarCoordinateCarrier) :
    ScalarCoordinateCarrier :=
  scalarCoordinateAction (generatedScalarFrame source chart point)⁻¹ coordinates

def generatedScalarPotential
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (coordinates : ScalarCoordinateCarrier) : ℝ :=
  scalarCoordinateSquaredNorm
    (scalarFrameRelativeCoordinates source chart point coordinates -
      sourceGeneratedVacuumCoordinates source)

theorem scalarFrameRelative_localVacuum
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) :
    scalarFrameRelativeCoordinates source chart point
        (generatedLocalVacuumCoordinates source chart point) =
      sourceGeneratedVacuumCoordinates source := by
  rw [scalarFrameRelativeCoordinates, generatedLocalVacuumCoordinates,
    ← scalarCoordinateAction_mul]
  simp

@[simp] theorem generatedScalarPotential_localVacuum
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) :
    generatedScalarPotential source chart point
      (generatedLocalVacuumCoordinates source chart point) = 0 := by
  simp [generatedScalarPotential, scalarFrameRelative_localVacuum]

theorem generatedScalarPotential_nonneg
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (coordinates : ScalarCoordinateCarrier) :
    0 ≤ generatedScalarPotential source chart point coordinates := by
  exact scalarCoordinateSquaredNorm_nonneg _

theorem generatedScalarPotential_eq_zero_iff
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (coordinates : ScalarCoordinateCarrier) :
    generatedScalarPotential source chart point coordinates = 0 ↔
      coordinates = generatedLocalVacuumCoordinates source chart point := by
  rw [generatedScalarPotential, scalarCoordinateSquaredNorm_eq_zero_iff,
    sub_eq_zero]
  constructor
  · intro relativeEquals
    have pushed := congrArg
      (scalarCoordinateAction (generatedScalarFrame source chart point))
      relativeEquals
    change scalarCoordinateAction (generatedScalarFrame source chart point)
        (scalarCoordinateAction (generatedScalarFrame source chart point)⁻¹
          coordinates) = _ at pushed
    rw [← scalarCoordinateAction_mul] at pushed
    simp only [mul_inv_cancel, scalarCoordinateAction_one] at pushed
    simpa [generatedLocalVacuumCoordinates] using pushed
  · intro coordinatesEquals
    rw [coordinatesEquals, scalarFrameRelative_localVacuum]

theorem generatedScalarFrame_overlap
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint) :
    generatedScalarFrame source terminal point =
      generatedTransition source initial terminal point *
        generatedScalarFrame source initial point := by
  exact (generatedTransition_cocycle source 0 initial terminal point).symm

theorem generatedLocalVacuumCoordinates_overlap
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint) :
    generatedLocalVacuumCoordinates source terminal point =
      scalarCoordinateAction
        (generatedTransition source initial terminal point)
        (generatedLocalVacuumCoordinates source initial point) := by
  rw [generatedLocalVacuumCoordinates, generatedScalarFrame_overlap,
    scalarCoordinateAction_mul]
  rfl

theorem scalarFrameRelativeCoordinates_overlap
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint) (coordinates : ScalarCoordinateCarrier) :
    scalarFrameRelativeCoordinates source terminal point
        (scalarCoordinateAction
          (generatedTransition source initial terminal point) coordinates) =
      scalarFrameRelativeCoordinates source initial point coordinates := by
  rw [scalarFrameRelativeCoordinates, scalarFrameRelativeCoordinates,
    generatedScalarFrame_overlap source initial terminal point, mul_inv_rev,
    ← scalarCoordinateAction_mul]
  have groupEquality :
      (generatedScalarFrame source initial point)⁻¹ *
          (generatedTransition source initial terminal point)⁻¹ *
            generatedTransition source initial terminal point =
        (generatedScalarFrame source initial point)⁻¹ := by
    group
  rw [groupEquality]

/-- Local gauge invariance/descent of the actual scalar potential.  The source
frame and scalar transform together; no unitarity receipt is assumed. -/
theorem generatedScalarPotential_overlap_invariant
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint) (coordinates : ScalarCoordinateCarrier) :
    generatedScalarPotential source terminal point
        (scalarCoordinateAction
          (generatedTransition source initial terminal point) coordinates) =
      generatedScalarPotential source initial point coordinates := by
  rw [generatedScalarPotential, generatedScalarPotential,
    scalarFrameRelativeCoordinates_overlap]

def generatedVacuumStabilizer
    (source : SmoothUnifiedSource) : Subgroup SU7MotherGroup where
  carrier := {groupElement |
    exteriorBreakingScalarRepresentation groupElement
        (sourceGeneratedVacuumBase source) =
      sourceGeneratedVacuumBase source}
  one_mem' := by simp
  mul_mem' := by
    intro first second firstFixed secondFixed
    change exteriorBreakingScalarRepresentation (first * second)
      (sourceGeneratedVacuumBase source) = _
    rw [map_mul]
    change exteriorBreakingScalarRepresentation first
      (exteriorBreakingScalarRepresentation second
        (sourceGeneratedVacuumBase source)) = _
    rw [secondFixed, firstFixed]
  inv_mem' := by
    intro groupElement fixed
    have cancellation := congrArg
      (exteriorBreakingScalarRepresentation groupElement⁻¹) fixed
    simpa [← map_mul] using cancellation.symm

/-- Exact finite classification of the actual stabilizer: membership is the
35-coordinate equalizer in the generated `Λ⁴V` basis. -/
theorem generatedVacuumStabilizer_mem_iff_coordinates
    (source : SmoothUnifiedSource) (groupElement : SU7MotherGroup) :
    groupElement ∈ generatedVacuumStabilizer source ↔
      ∀ index : ScalarBasisIndex,
        (su7ExteriorBasis 4).coord index
            (exteriorBreakingScalarRepresentation groupElement
              (sourceGeneratedVacuumBase source)) =
          (su7ExteriorBasis 4).coord index
            (sourceGeneratedVacuumBase source) := by
  constructor
  · intro fixed index
    exact congrArg ((su7ExteriorBasis 4).coord index) fixed
  · intro coordinatesEqual
    change exteriorBreakingScalarRepresentation groupElement
      (sourceGeneratedVacuumBase source) = sourceGeneratedVacuumBase source
    exact (su7ExteriorBasis 4).ext_elem coordinatesEqual

theorem positive_hypercharge_mem_vacuumStabilizer_iff
    (phase : Circle) :
    embeddedP286HyperchargeElement phase ∈
        generatedVacuumStabilizer positiveSmoothUnifiedSource ↔
      phase = 1 := by
  constructor
  · intro fixed
    have h01 :
        finiteGenerationScalarIndex 0 0 ≠
          finiteGenerationScalarIndex 0 1 := by decide
    have h10 :
        finiteGenerationScalarIndex 0 0 ≠
          finiteGenerationScalarIndex 1 0 := by decide
    have h11 :
        finiteGenerationScalarIndex 0 0 ≠
          finiteGenerationScalarIndex 1 1 := by decide
    have coordinateEquality := congrArg
      ((su7ExteriorBasis 4).coord
        (finiteGenerationScalarIndex 0 0)) fixed
    have weight : exteriorHyperchargeWeight
        (finiteGenerationScalarIndex 0 0) = -1 := by decide
    simp [positive_sourceGeneratedVacuumBase,
      finiteGenerationJointBreakingScalar, Fin.sum_univ_two,
      finiteGenerationBreakingTensor, exteriorBreakingScalarRepresentation,
      p286Hypercharge_exterior_basis,
      exteriorHyperchargeCharacter_eq_zpow, weight,
      h01, h10, h11] at coordinateEquality
    exact Circle.coe_injective coordinateEquality
  · rintro rfl
    simp [generatedVacuumStabilizer]

theorem positive_generatedVacuumStabilizer_proper :
    generatedVacuumStabilizer positiveSmoothUnifiedSource ≠ ⊤ := by
  intro stabilizerTop
  have quarterTurnFixed : hyperchargeQuarterTurn ∈
      generatedVacuumStabilizer positiveSmoothUnifiedSource := by
    rw [stabilizerTop]
    simp
  exact finiteGenerationJointBreakingScalar_is_genuinely_broken
    (by simpa [generatedVacuumStabilizer,
      positive_sourceGeneratedVacuumBase] using quarterTurnFixed)

theorem positive_origin_localVacuum_recovers_stageEightJointScalar :
    scalarCoordinateEquiv.symm
        (generatedLocalVacuumCoordinates positiveSmoothUnifiedSource 0 0) =
      finiteGenerationJointBreakingScalar := by
  simp [generatedLocalVacuumCoordinates, generatedScalarFrame,
    positive_sourceGeneratedVacuumBase, sourceGeneratedVacuumCoordinates,
    scalarCoordinateAction, generatedTransition]

theorem positive_dynamicVacuum_generates_stageEightMass :
    exteriorYukawaMassMap
        (scalarCoordinateEquiv.symm
          (generatedLocalVacuumCoordinates positiveSmoothUnifiedSource 0 0)) =
        exteriorYukawaMassMap finiteGenerationJointBreakingScalar ∧
      finiteGenerationMassMatrixOfScalar
        (scalarCoordinateEquiv.symm
          (generatedLocalVacuumCoordinates positiveSmoothUnifiedSource 0 0)) =
        finiteGenerationJointMassMatrix ∧
      exteriorYukawaMassMap
        (scalarCoordinateEquiv.symm
          (generatedLocalVacuumCoordinates positiveSmoothUnifiedSource 0 0)) ≠
        0 := by
  rw [positive_origin_localVacuum_recovers_stageEightJointScalar]
  exact ⟨rfl, rfl, finiteGenerationJointMassMap_ne_zero⟩

/-- Negative regression: the old explicit one-channel Stage-8 scalar is not a
minimum of the new source-generated potential. -/
theorem legacyExplicitBreakingScalar_not_dynamicVacuum :
    generatedScalarPotential positiveSmoothUnifiedSource 0 0
      (scalarCoordinateEquiv exteriorBreakingScalar) ≠ 0 := by
  intro potentialZero
  have coordinatesEqual :=
    (generatedScalarPotential_eq_zero_iff
      positiveSmoothUnifiedSource 0 0
      (scalarCoordinateEquiv exteriorBreakingScalar)).mp potentialZero
  have carrierEqual := congrArg scalarCoordinateEquiv.symm coordinatesEqual
  rw [positive_origin_localVacuum_recovers_stageEightJointScalar] at carrierEqual
  exact exteriorBreakingScalar_ne_finiteGenerationJointBreakingScalar
    (by simpa using carrierEqual)

def zeroPhaseStageEightSource : StageEightProofFreeSource.Source :=
  { canonicalSource with p506PhasePotential := fun _ => 0 }

def zeroPhaseSmoothUnifiedSource : SmoothUnifiedSource where
  stageEight := zeroPhaseStageEightSource
  continuousContactResidual := 2 * Real.pi

@[simp] theorem zeroPhase_sourceGeneratedVacuumBase :
    sourceGeneratedVacuumBase zeroPhaseSmoothUnifiedSource = 0 := by
  simp [sourceGeneratedVacuumBase, zeroPhaseSmoothUnifiedSource,
    zeroPhaseStageEightSource, StageEightProofFreeSource.Source.physicalPhaseAmplitude]

theorem zeroPhase_dynamicVacuum_massMap_zero :
    exteriorYukawaMassMap
        (sourceGeneratedVacuumBase zeroPhaseSmoothUnifiedSource) = 0 := by
  rw [zeroPhase_sourceGeneratedVacuumBase]
  exact exteriorYukawaMassMap_zeroBreaking

def frameRelativeScalarPotential
    (target coordinates : ScalarCoordinateCarrier) : ℝ :=
  scalarCoordinateSquaredNorm (coordinates - target)

def scalarCoordinateRealPairing
    (first second : ScalarCoordinateCarrier) : ℝ :=
  ∑ index : ScalarBasisIndex,
    (star (first index) * second index).re

theorem scalarCoordinateRealPairing_self
    (coordinates : ScalarCoordinateCarrier) :
    scalarCoordinateRealPairing coordinates coordinates =
      scalarCoordinateSquaredNorm coordinates := by
  apply Finset.sum_congr rfl
  intro index _
  simp [Complex.normSq_apply]

def frameRelativeScalarGradient
    (target coordinates : ScalarCoordinateCarrier) :
    ScalarCoordinateCarrier → ℝ :=
  fun variation =>
    2 * scalarCoordinateRealPairing (coordinates - target) variation

/-- Exact quadratic expansion; its linear coefficient is the actual first
variation and the remaining term is explicitly second order. -/
theorem frameRelativeScalarPotential_expansion
    (target coordinates variation : ScalarCoordinateCarrier)
    (coefficient : ℝ) :
    frameRelativeScalarPotential target
        (coordinates + (coefficient : ℂ) • variation) =
      frameRelativeScalarPotential target coordinates +
        coefficient * frameRelativeScalarGradient target coordinates variation +
        coefficient ^ 2 * scalarCoordinateSquaredNorm variation := by
  simp only [frameRelativeScalarPotential, scalarCoordinateSquaredNorm,
    frameRelativeScalarGradient, scalarCoordinateRealPairing,
    Complex.normSq_apply]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  simp
  ring

@[simp] theorem frameRelativeScalarGradient_at_target
    (target : ScalarCoordinateCarrier) :
    frameRelativeScalarGradient target target = 0 := by
  funext variation
  simp [frameRelativeScalarGradient, scalarCoordinateRealPairing]

theorem frameRelativeScalarPotential_uniqueMinimum
    (target coordinates : ScalarCoordinateCarrier) :
    frameRelativeScalarPotential target target ≤
      frameRelativeScalarPotential target coordinates ∧
      (frameRelativeScalarPotential target coordinates =
        frameRelativeScalarPotential target target ↔ coordinates = target) := by
  constructor
  · rw [frameRelativeScalarPotential, frameRelativeScalarPotential,
      sub_self, scalarCoordinateSquaredNorm_zero]
    exact scalarCoordinateSquaredNorm_nonneg _
  · rw [frameRelativeScalarPotential, frameRelativeScalarPotential]
    rw [sub_self, scalarCoordinateSquaredNorm_zero]
    exact (scalarCoordinateSquaredNorm_eq_zero_iff _).trans sub_eq_zero

def GeneratedScalarVacuumStationary
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) : Prop :=
  frameRelativeScalarGradient (sourceGeneratedVacuumCoordinates source)
    (scalarFrameRelativeCoordinates source chart point
      (generatedLocalVacuumCoordinates source chart point)) = 0

theorem generatedLocalVacuum_stationary
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) :
    GeneratedScalarVacuumStationary source chart point := by
  rw [GeneratedScalarVacuumStationary, scalarFrameRelative_localVacuum]
  exact frameRelativeScalarGradient_at_target _

/-- S9-B1 checkpoint: one proof-free source generates a gauge-descending
quadratic scalar potential, its unique stationary/global minimum, the exact
finite stabilizer equations, and the Stage-8 joint mass output. -/
theorem positiveSource_generates_dynamicVacuum_and_stageEightMass :
    (∀ chart point,
      generatedScalarPotential positiveSmoothUnifiedSource chart point
          (generatedLocalVacuumCoordinates positiveSmoothUnifiedSource chart point) = 0 ∧
        GeneratedScalarVacuumStationary positiveSmoothUnifiedSource chart point) ∧
      (∀ initial terminal point coordinates,
        generatedScalarPotential positiveSmoothUnifiedSource terminal point
            (scalarCoordinateAction
              (generatedTransition positiveSmoothUnifiedSource initial terminal point)
              coordinates) =
          generatedScalarPotential positiveSmoothUnifiedSource initial point coordinates) ∧
      sourceGeneratedVacuumBase positiveSmoothUnifiedSource ≠ 0 ∧
      generatedVacuumStabilizer positiveSmoothUnifiedSource ≠ ⊤ ∧
      (∀ phase : Circle,
        embeddedP286HyperchargeElement phase ∈
            generatedVacuumStabilizer positiveSmoothUnifiedSource ↔ phase = 1) ∧
      exteriorYukawaMassMap
        (scalarCoordinateEquiv.symm
          (generatedLocalVacuumCoordinates positiveSmoothUnifiedSource 0 0)) ≠ 0 := by
  exact ⟨fun chart point =>
      ⟨generatedScalarPotential_localVacuum _ _ _,
        generatedLocalVacuum_stationary _ _ _⟩,
    generatedScalarPotential_overlap_invariant positiveSmoothUnifiedSource,
    positive_sourceGeneratedVacuumBase_nonzero,
    positive_generatedVacuumStabilizer_proper,
    positive_hypercharge_mem_vacuumStabilizer_iff,
    positive_dynamicVacuum_generates_stageEightMass.2.2⟩


end

end SaturationMonoid.PhysicsCore.StageNineDynamicBreakingVacuum
