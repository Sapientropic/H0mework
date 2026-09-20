import H0mework.Physics.Cauchy.P286ActionCauchySplit
import H0mework.Physics.Holonomic.GeneratedHolonomicPhaseEvolution

/-!
# S9-C3h88: canonical Cauchy state and source-generated phase update

`StageNineHolonomicConfiguration` is a four-dimensional field history, not an
instantaneous state.  This module introduces a pure-data slice carrier at the
already fixed time coordinate:

* all nine primitive field values are retained as spatial fields;
* the scalar time derivative is retained because the scalar sector is
  second-order;
* no Euler--Lagrange equation, shell, residual, integrability statement,
  stationarity receipt, endpoint, or branch witness is stored.

The existing source-generated continuous phase path acts directly on this
carrier.  The action is defined before any residual readout, has identity and
composition laws, is nontrivial for the positive source, and commutes with
restriction of a smooth holonomic history to a canonical time slice.

This is a genuine source-generated update on the correct instantaneous data
type.  It is still the internal phase sector rather than the full interacting
BF/GR/SM Cauchy development; the action-native P286 momentum equation from
C3h87 remains a downstream evolution gate.
-/

namespace SaturationMonoid.PhysicsCore.StageNineCanonicalCauchyState

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineSourceGeneratedHolonomicPhaseEvolution
open SU7ExteriorBreakingYukawa
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7MotherLieAlgebra
open DiracExteriorMatterAction

noncomputable section

/-- The three spatial coordinates of the fixed `3+1` split. -/
abbrev StageNineSpatialPoint := EuclideanSpace ℝ (Fin 3)

/-- Canonical embedding of a spatial point into the coordinate-time slice.
The foliation and normalization are definitions, not source parameters. -/
def canonicalCauchySlicePoint
    (time : ℝ) (space : StageNineSpatialPoint) : BasePoint :=
  EuclideanSpace.single canonicalLorentzianTimeDirection time +
    ∑ direction : Fin 3,
      EuclideanSpace.single direction.succ (space direction)

@[simp] theorem canonicalCauchySlicePoint_time
    (time : ℝ) (space : StageNineSpatialPoint) :
    canonicalCauchySlicePoint time space canonicalLorentzianTimeDirection =
      time := by
  simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
    Fin.sum_univ_three]

@[simp] theorem canonicalCauchySlicePoint_spatial
    (time : ℝ) (space : StageNineSpatialPoint) (direction : Fin 3) :
    canonicalCauchySlicePoint time space direction.succ =
      space direction := by
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-- Pure instantaneous Stage-9 data.  The scalar velocity is data, while
curvature, BF momentum, equations, and residuals remain derived readouts. -/
@[ext] structure StageNineCauchyState where
  coframe : StageNineSpatialPoint → LorentzianCoframe
  gravityConnection :
    StageNineSpatialPoint → PointwiseLorentzSpinConnection
  gravityAuxiliary : StageNineSpatialPoint → PhysicalBivector
  gravitySimplicityMultiplier :
    StageNineSpatialPoint → PhysicalBivector
  gaugeConnection :
    StageNineSpatialPoint → LorentzianIndex → P286LieBlockData
  gaugeAuxiliary :
    StageNineSpatialPoint → Fin 6 → P286LieBlockData
  scalar : StageNineSpatialPoint → ScalarCoordinateCarrier
  scalarVelocity : StageNineSpatialPoint → ScalarCoordinateCarrier
  matter : StageNineSpatialPoint → DiracExteriorMatterCarrier
  conjugateMatter :
    StageNineSpatialPoint → Module.Dual ℂ DiracExteriorMatterCarrier

/-- Restrict a four-dimensional primitive history to one canonical Cauchy
slice.  Only the scalar time derivative must be added to the primitive
values. -/
def canonicalCauchyRestriction
    (time : ℝ) (configuration : StageNineHolonomicConfiguration) :
    StageNineCauchyState where
  coframe := fun space =>
    configuration.coframe (canonicalCauchySlicePoint time space)
  gravityConnection := fun space =>
    configuration.gravityConnection (canonicalCauchySlicePoint time space)
  gravityAuxiliary := fun space =>
    configuration.gravityAuxiliary (canonicalCauchySlicePoint time space)
  gravitySimplicityMultiplier := fun space =>
    configuration.gravitySimplicityMultiplier
      (canonicalCauchySlicePoint time space)
  gaugeConnection := fun space =>
    configuration.gaugeConnection (canonicalCauchySlicePoint time space)
  gaugeAuxiliary := fun space =>
    configuration.gaugeAuxiliary (canonicalCauchySlicePoint time space)
  scalar := fun space =>
    configuration.scalar (canonicalCauchySlicePoint time space)
  scalarVelocity := fun space =>
    fieldDirectionalDerivative configuration.scalar
      (canonicalCauchySlicePoint time space)
      canonicalLorentzianTimeDirection
  matter := fun space =>
    configuration.matter (canonicalCauchySlicePoint time space)
  conjugateMatter := fun space =>
    configuration.conjugateMatter (canonicalCauchySlicePoint time space)

/-- The scalar phase action as a complex-linear coordinate map. -/
def scalarCoordinatePhaseLinear
    (groupElement : SU7MotherGroup) :
    ScalarCoordinateCarrier →ₗ[ℂ] ScalarCoordinateCarrier :=
  scalarCoordinateEquiv.toLinearMap.comp
    ((exteriorBreakingScalarRepresentation groupElement).comp
      scalarCoordinateEquiv.symm.toLinearMap)

@[simp] theorem scalarCoordinatePhaseLinear_apply
    (groupElement : SU7MotherGroup)
    (coordinates : ScalarCoordinateCarrier) :
    scalarCoordinatePhaseLinear groupElement coordinates =
      scalarCoordinateAction groupElement coordinates :=
  rfl

/-- Finite dimensionality makes the same phase action a continuous real
linear map, which is the correct map for spacetime Fréchet derivatives. -/
def scalarCoordinatePhaseContinuousRealLinear
    (groupElement : SU7MotherGroup) :
    ScalarCoordinateCarrier →L[ℝ] ScalarCoordinateCarrier :=
  (scalarCoordinatePhaseLinear groupElement).toContinuousLinearMap
    |>.restrictScalars ℝ

@[simp] theorem scalarCoordinatePhaseContinuousRealLinear_apply
    (groupElement : SU7MotherGroup)
    (coordinates : ScalarCoordinateCarrier) :
    scalarCoordinatePhaseContinuousRealLinear groupElement coordinates =
      scalarCoordinateAction groupElement coordinates :=
  rfl

/-- A constant internal phase action commutes with every spacetime
directional derivative. -/
theorem fieldDirectionalDerivative_scalarCoordinateAction
    (groupElement : SU7MotherGroup)
    (field : BasePoint → ScalarCoordinateCarrier)
    (point : BasePoint) (direction : LorentzianIndex)
    (differentiable : DifferentiableAt ℝ field point) :
    fieldDirectionalDerivative
        (fun candidate =>
          scalarCoordinateAction groupElement (field candidate))
        point direction =
      scalarCoordinateAction groupElement
        (fieldDirectionalDerivative field point direction) := by
  let action :=
    scalarCoordinatePhaseContinuousRealLinear groupElement
  have derivative :
      HasFDerivAt (fun candidate => action (field candidate))
        (action.comp (fderiv ℝ field point)) point :=
    action.hasFDerivAt.comp point differentiable.hasFDerivAt
  unfold fieldDirectionalDerivative
  change
    fderiv ℝ (fun candidate => action (field candidate)) point
        (coordinateDirection direction) =
      action
        (fderiv ℝ field point (coordinateDirection direction))
  rw [derivative.fderiv]
  rfl

/-- Source/path-generated internal phase update on instantaneous Cauchy
data.  It consumes no residual or equation field. -/
def sourceGeneratedCauchyPhaseUpdate
    (source : SmoothUnifiedSource) (time : ℝ)
    (state : StageNineCauchyState) :
    StageNineCauchyState where
  coframe := state.coframe
  gravityConnection := state.gravityConnection
  gravityAuxiliary := state.gravityAuxiliary
  gravitySimplicityMultiplier := state.gravitySimplicityMultiplier
  gaugeConnection := state.gaugeConnection
  gaugeAuxiliary := state.gaugeAuxiliary
  scalar := fun space =>
    scalarCoordinateAction (sourcePhaseGroupElement source time)
      (state.scalar space)
  scalarVelocity := fun space =>
    scalarCoordinateAction (sourcePhaseGroupElement source time)
      (state.scalarVelocity space)
  matter := fun space =>
    diracExteriorMatterGaugeRepresentation
      (sourcePhaseGroupElement source time) (state.matter space)
  conjugateMatter := fun space =>
    (state.conjugateMatter space).comp
      (diracExteriorMatterGaugeRepresentation
        (sourcePhaseGroupElement source time)⁻¹)

@[simp] theorem sourceGeneratedCauchyPhaseUpdate_zero
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState) :
    sourceGeneratedCauchyPhaseUpdate source 0 state = state := by
  apply StageNineCauchyState.ext
  · simp [sourceGeneratedCauchyPhaseUpdate]
  · simp [sourceGeneratedCauchyPhaseUpdate]
  · simp [sourceGeneratedCauchyPhaseUpdate]
  · simp [sourceGeneratedCauchyPhaseUpdate]
  · simp [sourceGeneratedCauchyPhaseUpdate]
  · simp [sourceGeneratedCauchyPhaseUpdate]
  · funext space
    simp [sourceGeneratedCauchyPhaseUpdate]
  · funext space
    simp [sourceGeneratedCauchyPhaseUpdate]
  · funext space
    change
      diracExteriorMatterGaugeRepresentation
          (sourcePhaseGroupElement source 0) (state.matter space) =
        state.matter space
    rw [sourcePhaseGroupElement_zero, map_one]
    rfl
  · funext space
    apply LinearMap.ext
    intro matter
    change
      state.conjugateMatter space
          (diracExteriorMatterGaugeRepresentation
            (sourcePhaseGroupElement source 0)⁻¹ matter) =
        state.conjugateMatter space matter
    rw [sourcePhaseGroupElement_zero, inv_one, map_one]
    rfl

theorem sourceGeneratedCauchyPhaseUpdate_add
    (source : SmoothUnifiedSource) (first second : ℝ)
    (state : StageNineCauchyState) :
    sourceGeneratedCauchyPhaseUpdate source (first + second) state =
      sourceGeneratedCauchyPhaseUpdate source first
        (sourceGeneratedCauchyPhaseUpdate source second state) := by
  apply StageNineCauchyState.ext
  · simp [sourceGeneratedCauchyPhaseUpdate]
  · simp [sourceGeneratedCauchyPhaseUpdate]
  · simp [sourceGeneratedCauchyPhaseUpdate]
  · simp [sourceGeneratedCauchyPhaseUpdate]
  · simp [sourceGeneratedCauchyPhaseUpdate]
  · simp [sourceGeneratedCauchyPhaseUpdate]
  · funext space
    change
      scalarCoordinateAction
          (sourcePhaseGroupElement source (first + second))
          (state.scalar space) =
        scalarCoordinateAction (sourcePhaseGroupElement source first)
          (scalarCoordinateAction (sourcePhaseGroupElement source second)
            (state.scalar space))
    rw [sourcePhaseGroupElement_add, scalarCoordinateAction_mul]
  · funext space
    change
      scalarCoordinateAction
          (sourcePhaseGroupElement source (first + second))
          (state.scalarVelocity space) =
        scalarCoordinateAction (sourcePhaseGroupElement source first)
          (scalarCoordinateAction (sourcePhaseGroupElement source second)
            (state.scalarVelocity space))
    rw [sourcePhaseGroupElement_add, scalarCoordinateAction_mul]
  · funext space
    change
      diracExteriorMatterGaugeRepresentation
          (sourcePhaseGroupElement source (first + second))
          (state.matter space) =
        diracExteriorMatterGaugeRepresentation
          (sourcePhaseGroupElement source first)
          (diracExteriorMatterGaugeRepresentation
            (sourcePhaseGroupElement source second)
            (state.matter space))
    rw [sourcePhaseGroupElement_add, map_mul]
    rfl
  · funext space
    apply LinearMap.ext
    intro matter
    change
      state.conjugateMatter space
          (diracExteriorMatterGaugeRepresentation
            (sourcePhaseGroupElement source (first + second))⁻¹ matter) =
        state.conjugateMatter space
          (diracExteriorMatterGaugeRepresentation
            (sourcePhaseGroupElement source second)⁻¹
            (diracExteriorMatterGaugeRepresentation
              (sourcePhaseGroupElement source first)⁻¹ matter))
    rw [sourcePhaseGroupElement_add, mul_inv_rev, map_mul]
    rfl

theorem sourceGeneratedCauchyPhaseUpdate_left_inverse
    (source : SmoothUnifiedSource) (time : ℝ)
    (state : StageNineCauchyState) :
    sourceGeneratedCauchyPhaseUpdate source (-time)
        (sourceGeneratedCauchyPhaseUpdate source time state) = state := by
  calc
    sourceGeneratedCauchyPhaseUpdate source (-time)
        (sourceGeneratedCauchyPhaseUpdate source time state) =
        sourceGeneratedCauchyPhaseUpdate source (-time + time) state :=
      (sourceGeneratedCauchyPhaseUpdate_add source (-time) time state).symm
    _ = state := by simp

theorem sourceGeneratedCauchyPhaseUpdate_right_inverse
    (source : SmoothUnifiedSource) (time : ℝ)
    (state : StageNineCauchyState) :
    sourceGeneratedCauchyPhaseUpdate source time
        (sourceGeneratedCauchyPhaseUpdate source (-time) state) = state := by
  calc
    sourceGeneratedCauchyPhaseUpdate source time
        (sourceGeneratedCauchyPhaseUpdate source (-time) state) =
        sourceGeneratedCauchyPhaseUpdate source (time + -time) state :=
      (sourceGeneratedCauchyPhaseUpdate_add source time (-time) state).symm
    _ = state := by simp

/-- Each source-generated time slice is an actual equivalence of Cauchy
states; the inverse is the oppositely oriented source path. -/
def sourceGeneratedCauchyPhaseEquiv
    (source : SmoothUnifiedSource) (time : ℝ) :
    Equiv.Perm StageNineCauchyState where
  toFun := sourceGeneratedCauchyPhaseUpdate source time
  invFun := sourceGeneratedCauchyPhaseUpdate source (-time)
  left_inv := sourceGeneratedCauchyPhaseUpdate_left_inverse source time
  right_inv := sourceGeneratedCauchyPhaseUpdate_right_inverse source time

@[simp] theorem sourceGeneratedCauchyPhaseEquiv_apply
    (source : SmoothUnifiedSource) (time : ℝ)
    (state : StageNineCauchyState) :
    sourceGeneratedCauchyPhaseEquiv source time state =
      sourceGeneratedCauchyPhaseUpdate source time state :=
  rfl

/-- Path-first formulation of the update: additive time is bundled as a
homomorphism into the automorphism group of pure Cauchy data. -/
def sourceGeneratedCauchyPhaseFlow
    (source : SmoothUnifiedSource) :
    Multiplicative ℝ →* Equiv.Perm StageNineCauchyState where
  toFun time := sourceGeneratedCauchyPhaseEquiv source time.toAdd
  map_one' := by
    apply Equiv.ext
    intro state
    exact sourceGeneratedCauchyPhaseUpdate_zero source state
  map_mul' := by
    intro first second
    apply Equiv.ext
    intro state
    exact sourceGeneratedCauchyPhaseUpdate_add source first.toAdd
      second.toAdd state

@[simp] theorem sourceGeneratedCauchyPhaseFlow_apply
    (source : SmoothUnifiedSource) (time : Multiplicative ℝ)
    (state : StageNineCauchyState) :
    sourceGeneratedCauchyPhaseFlow source time state =
      sourceGeneratedCauchyPhaseUpdate source time.toAdd state :=
  rfl

/-- Restricting a smooth holonomic phase update gives exactly the
source-generated update on instantaneous Cauchy data, including the scalar
velocity. -/
theorem canonicalCauchyRestriction_phaseUpdate
    (source : SmoothUnifiedSource) (phaseTime sliceTime : ℝ)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    canonicalCauchyRestriction sliceTime
        (sourceGeneratedHolonomicPhaseUpdate source phaseTime configuration) =
      sourceGeneratedCauchyPhaseUpdate source phaseTime
        (canonicalCauchyRestriction sliceTime configuration) := by
  rcases smooth with
    ⟨_, _, _, _, _, _, scalarSmooth, _, _⟩
  apply StageNineCauchyState.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · funext space
    exact fieldDirectionalDerivative_scalarCoordinateAction
      (sourcePhaseGroupElement source phaseTime) configuration.scalar
      (canonicalCauchySlicePoint sliceTime space)
      canonicalLorentzianTimeDirection
      ((scalarSmooth.differentiable (by simp)).differentiableAt)
  · rfl
  · rfl

@[simp] theorem zeroRate_sourceGeneratedCauchyPhaseUpdate
    (time : ℝ) (state : StageNineCauchyState) :
    sourceGeneratedCauchyPhaseUpdate zeroRateSmoothUnifiedSource time state =
      state := by
  apply StageNineCauchyState.ext
  · simp [sourceGeneratedCauchyPhaseUpdate]
  · simp [sourceGeneratedCauchyPhaseUpdate]
  · simp [sourceGeneratedCauchyPhaseUpdate]
  · simp [sourceGeneratedCauchyPhaseUpdate]
  · simp [sourceGeneratedCauchyPhaseUpdate]
  · simp [sourceGeneratedCauchyPhaseUpdate]
  · funext space
    simp [sourceGeneratedCauchyPhaseUpdate]
  · funext space
    simp [sourceGeneratedCauchyPhaseUpdate]
  · funext space
    change
      diracExteriorMatterGaugeRepresentation
          (sourcePhaseGroupElement zeroRateSmoothUnifiedSource time)
          (state.matter space) =
        state.matter space
    rw [zeroRate_sourcePhaseGroupElement, map_one]
    rfl
  · funext space
    apply LinearMap.ext
    intro matter
    change
      state.conjugateMatter space
          (diracExteriorMatterGaugeRepresentation
            (sourcePhaseGroupElement zeroRateSmoothUnifiedSource time)⁻¹
            matter) =
        state.conjugateMatter space matter
    rw [zeroRate_sourcePhaseGroupElement, inv_one, map_one]
    rfl

def positivePhaseProbeCauchyState :
    StageNineCauchyState :=
  canonicalCauchyRestriction 0 positivePhaseProbeConfiguration

/-- Positive path-first regression on the actual instantaneous carrier. -/
theorem positive_sourceGeneratedCauchyPhaseUpdate_nontrivial :
    sourceGeneratedCauchyPhaseUpdate positiveSmoothUnifiedSource 1
        positivePhaseProbeCauchyState ≠
      positivePhaseProbeCauchyState := by
  intro updateFixed
  have scalarFixed := congrArg
    (fun state : StageNineCauchyState => state.scalar 0) updateFixed
  have coordinateFixed :
      scalarCoordinateAction
          (sourcePhaseGroupElement positiveSmoothUnifiedSource 1)
          (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) =
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
    simpa [sourceGeneratedCauchyPhaseUpdate,
      positivePhaseProbeCauchyState, canonicalCauchyRestriction,
      positivePhaseProbeConfiguration] using scalarFixed
  have baseFixed :
      exteriorBreakingScalarRepresentation
          (sourcePhaseGroupElement positiveSmoothUnifiedSource 1)
          (sourceGeneratedVacuumBase positiveSmoothUnifiedSource) =
        sourceGeneratedVacuumBase positiveSmoothUnifiedSource := by
    have pushed := congrArg scalarCoordinateEquiv.symm coordinateFixed
    simpa [scalarCoordinateAction, sourceGeneratedVacuumCoordinates] using
      pushed
  have phaseFixed :
      (generatedUnitaryFlow positiveSmoothUnifiedSource).evolve 1 = 1 :=
    (positive_hypercharge_mem_vacuumStabilizer_iff
      ((generatedUnitaryFlow positiveSmoothUnifiedSource).evolve 1)).mp
      baseFixed
  exact positive_generatedUnitaryFlow_nontrivial phaseFixed

theorem positive_sourceGeneratedCauchyPhaseFlow_nontrivial :
    sourceGeneratedCauchyPhaseFlow positiveSmoothUnifiedSource
        (Multiplicative.ofAdd 1) ≠ 1 := by
  intro flowIdentity
  have fixed := congrArg
    (fun update : Equiv.Perm StageNineCauchyState =>
      update positivePhaseProbeCauchyState) flowIdentity
  apply positive_sourceGeneratedCauchyPhaseUpdate_nontrivial
  simpa using fixed

end

end SaturationMonoid.PhysicsCore.StageNineCanonicalCauchyState
