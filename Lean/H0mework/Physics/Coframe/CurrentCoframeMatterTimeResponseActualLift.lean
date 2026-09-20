import H0mework.Physics.Cauchy.CanonicalCauchyState
import H0mework.Physics.Coframe.CurrentCoframeMatterTimeResponse
import H0mework.Physics.Matter.MatterVariation

/-!
# Current-coframe matter time-response actual lift

The current-coframe Dirac operator already generates a unique temporal
covariant matter response from an actual configuration.  This module gives
that response a faithful actual-level realization:

```text
actual U
→ action-generated temporal covariant response T(U)
→ generated raw first-jet difference
→ canonical linear physical-time matter write
→ actual Uᵐ.
```

The write preserves every non-matter field, the matter value at the origin,
and every spatial matter first jet.  It changes only the temporal raw matter
first jet needed to realize `T(U)`.  The update is literally the identity iff
the input actual already carries its action-generated temporal response.

No residual, target jet, branch, inverse witness, coefficient, or equation
certificate enters the constructor.  Re-substitution into the same temporal
action law is producer soundness.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCurrentCoframeMatterTimeResponseActualLift

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-! ## Canonical faithful linear-time installer -/

/-- Linear physical-time matter-coordinate write with no adjustable
coefficient. -/
def matterLinearTimeCoordinateWrite
    (response : DiracExteriorMatterCarrier)
    (point : BasePoint) : MatterCoordinateCarrier :=
  point canonicalLorentzianTimeDirection • matterCoordinateEquiv response

@[simp] theorem matterLinearTimeCoordinateWrite_origin
    (response : DiracExteriorMatterCarrier) :
    matterLinearTimeCoordinateWrite response 0 = 0 := by
  simp [matterLinearTimeCoordinateWrite]

theorem matterLinearTimeCoordinateWrite_directionalDerivative
    (response : DiracExteriorMatterCarrier)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (matterLinearTimeCoordinateWrite response) point direction =
      if direction = canonicalLorentzianTimeDirection then
        matterCoordinateEquiv response
      else
        0 := by
  have derivative :=
    (localBaseCoordinate canonicalLorentzianTimeDirection).hasFDerivAt
      (x := point)
      |>.smul_const (matterCoordinateEquiv response)
  unfold fieldDirectionalDerivative matterLinearTimeCoordinateWrite
  change
    fderiv ℝ
        (fun candidate =>
          localBaseCoordinate canonicalLorentzianTimeDirection candidate •
            matterCoordinateEquiv response)
        point (coordinateDirection direction) =
      _
  rw [derivative.fderiv]
  fin_cases direction <;>
    simp [coordinateDirection, canonicalLorentzianTimeDirection]

theorem matterLinearTimeCoordinateWrite_contDiff
    (response : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ (matterLinearTimeCoordinateWrite response) := by
  exact
    (localBaseCoordinate canonicalLorentzianTimeDirection).contDiff.smul
      contDiff_const

/-- Install one already-generated temporal raw matter response. -/
def installMatterLinearTimeResponse
    (configuration : StageNineHolonomicConfiguration)
    (response : DiracExteriorMatterCarrier) :
    StageNineHolonomicConfiguration :=
  varyMatterCoordinates configuration
    (matterLinearTimeCoordinateWrite response) 1

@[simp] theorem installMatterLinearTimeResponse_coframe
    (configuration : StageNineHolonomicConfiguration)
    (response : DiracExteriorMatterCarrier) :
    (installMatterLinearTimeResponse configuration response).coframe =
      configuration.coframe :=
  rfl

@[simp] theorem installMatterLinearTimeResponse_gravityConnection
    (configuration : StageNineHolonomicConfiguration)
    (response : DiracExteriorMatterCarrier) :
    (installMatterLinearTimeResponse configuration response).gravityConnection =
      configuration.gravityConnection :=
  rfl

@[simp] theorem installMatterLinearTimeResponse_gravityAuxiliary
    (configuration : StageNineHolonomicConfiguration)
    (response : DiracExteriorMatterCarrier) :
    (installMatterLinearTimeResponse configuration response).gravityAuxiliary =
      configuration.gravityAuxiliary :=
  rfl

@[simp] theorem installMatterLinearTimeResponse_gravitySimplicityMultiplier
    (configuration : StageNineHolonomicConfiguration)
    (response : DiracExteriorMatterCarrier) :
    (installMatterLinearTimeResponse configuration response
      ).gravitySimplicityMultiplier =
      configuration.gravitySimplicityMultiplier :=
  rfl

@[simp] theorem installMatterLinearTimeResponse_gaugeConnection
    (configuration : StageNineHolonomicConfiguration)
    (response : DiracExteriorMatterCarrier) :
    (installMatterLinearTimeResponse configuration response).gaugeConnection =
      configuration.gaugeConnection :=
  rfl

@[simp] theorem installMatterLinearTimeResponse_gaugeAuxiliary
    (configuration : StageNineHolonomicConfiguration)
    (response : DiracExteriorMatterCarrier) :
    (installMatterLinearTimeResponse configuration response).gaugeAuxiliary =
      configuration.gaugeAuxiliary :=
  rfl

@[simp] theorem installMatterLinearTimeResponse_scalar
    (configuration : StageNineHolonomicConfiguration)
    (response : DiracExteriorMatterCarrier) :
    (installMatterLinearTimeResponse configuration response).scalar =
      configuration.scalar :=
  rfl

@[simp] theorem installMatterLinearTimeResponse_conjugateMatter
    (configuration : StageNineHolonomicConfiguration)
    (response : DiracExteriorMatterCarrier) :
    (installMatterLinearTimeResponse configuration response).conjugateMatter =
      configuration.conjugateMatter :=
  rfl

theorem installMatterLinearTimeResponse_matter_coordinate
    (configuration : StageNineHolonomicConfiguration)
    (response : DiracExteriorMatterCarrier)
    (point : BasePoint) :
    matterCoordinateEquiv
        ((installMatterLinearTimeResponse configuration response).matter
          point) =
      matterCoordinateEquiv (configuration.matter point) +
        matterLinearTimeCoordinateWrite response point := by
  simp [installMatterLinearTimeResponse, varyMatterCoordinates]

@[simp] theorem installMatterLinearTimeResponse_matter_origin
    (configuration : StageNineHolonomicConfiguration)
    (response : DiracExteriorMatterCarrier) :
    (installMatterLinearTimeResponse configuration response).matter 0 =
      configuration.matter 0 := by
  apply matterCoordinateEquiv.injective
  simp [installMatterLinearTimeResponse_matter_coordinate]

theorem installMatterLinearTimeResponse_matterCoordinateDerivative_origin
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (response : DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          matterCoordinateEquiv
            ((installMatterLinearTimeResponse configuration response).matter
              point))
        0 direction =
      fieldDirectionalDerivative
          (fun point => matterCoordinateEquiv (configuration.matter point))
          0 direction +
        if direction = canonicalLorentzianTimeDirection then
          matterCoordinateEquiv response
        else
          0 := by
  have backgroundDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (configuration.matter point)) 0 :=
    (smooth.2.2.2.2.2.2.2.1.differentiable (by simp)).differentiableAt
  have responseDifferentiable : DifferentiableAt ℝ
      (matterLinearTimeCoordinateWrite response) 0 :=
    (matterLinearTimeCoordinateWrite_contDiff response).differentiable
      (by simp) |>.differentiableAt
  unfold fieldDirectionalDerivative
  rw [show
    (fun point =>
      matterCoordinateEquiv
        ((installMatterLinearTimeResponse configuration response).matter
          point)) =
      (fun point => matterCoordinateEquiv (configuration.matter point)) +
        matterLinearTimeCoordinateWrite response by
    funext point
    exact installMatterLinearTimeResponse_matter_coordinate
      configuration response point]
  rw [fderiv_add backgroundDifferentiable responseDifferentiable, add_apply]
  change
    _ +
        fieldDirectionalDerivative
          (matterLinearTimeCoordinateWrite response) 0 direction =
      _
  rw [matterLinearTimeCoordinateWrite_directionalDerivative]

theorem
    holonomicMatterCovariantDerivative_installMatterLinearTimeResponse_origin
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (response : DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative
        (installMatterLinearTimeResponse configuration response)
        0 direction =
      holonomicMatterCovariantDerivative configuration 0 direction +
        if direction = canonicalLorentzianTimeDirection then
          response
        else
          0 := by
  unfold holonomicMatterCovariantDerivative
  rw [
    installMatterLinearTimeResponse_matterCoordinateDerivative_origin
      configuration smooth response direction]
  split_ifs <;>
    simp only [map_add, matterCoordinateEquiv.symm_apply_apply, map_zero,
      installMatterLinearTimeResponse_gravityConnection,
      installMatterLinearTimeResponse_gaugeConnection,
      installMatterLinearTimeResponse_matter_origin] <;>
    module

theorem installMatterLinearTimeResponse_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (response : DiracExteriorMatterCarrier) :
    (installMatterLinearTimeResponse configuration response).Smooth := by
  rcases smooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      gravityMultiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  refine
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      gravityMultiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, ?_, conjugateMatterSmooth⟩
  rw [show
    (fun point =>
      matterCoordinateEquiv
        ((installMatterLinearTimeResponse configuration response).matter
          point)) =
      (fun point => matterCoordinateEquiv (configuration.matter point)) +
        matterLinearTimeCoordinateWrite response by
    funext point
    exact installMatterLinearTimeResponse_matter_coordinate
      configuration response point]
  exact matterSmooth.add (matterLinearTimeCoordinateWrite_contDiff response)

theorem installMatterLinearTimeResponse_nondegenerate
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (response : DiracExteriorMatterCarrier) :
    (installMatterLinearTimeResponse configuration response).Nondegenerate := by
  simpa [StageNineHolonomicConfiguration.Nondegenerate] using nondegenerate

@[simp] theorem installMatterLinearTimeResponse_zero
    (configuration : StageNineHolonomicConfiguration) :
    installMatterLinearTimeResponse configuration 0 = configuration := by
  cases configuration
  simp [installMatterLinearTimeResponse, varyMatterCoordinates,
    matterLinearTimeCoordinateWrite]

/-- Faithful zero fiber: a nonzero generated first-jet response cannot
disappear into a third unchanged actual. -/
theorem installMatterLinearTimeResponse_eq_iff
    (configuration : StageNineHolonomicConfiguration)
    (response : DiracExteriorMatterCarrier) :
    installMatterLinearTimeResponse configuration response = configuration ↔
      response = 0 := by
  constructor
  · intro actualEq
    have matterEq := congrArg
      (fun candidate : StageNineHolonomicConfiguration =>
        matterCoordinateEquiv
          (candidate.matter
            (coordinateDirection canonicalLorentzianTimeDirection)))
      actualEq
    rw [installMatterLinearTimeResponse_matter_coordinate] at matterEq
    have responseCoordinateZero :
        matterLinearTimeCoordinateWrite response
            (coordinateDirection canonicalLorentzianTimeDirection) =
          0 := by
      exact add_left_cancel
        (show
          matterCoordinateEquiv
                (configuration.matter
                  (coordinateDirection canonicalLorentzianTimeDirection)) +
              matterLinearTimeCoordinateWrite response
                (coordinateDirection canonicalLorentzianTimeDirection) =
            matterCoordinateEquiv
                (configuration.matter
                  (coordinateDirection canonicalLorentzianTimeDirection)) +
              0 by
          simpa using matterEq)
    apply matterCoordinateEquiv.injective
    simpa [matterLinearTimeCoordinateWrite, localBaseCoordinate,
      coordinateDirection, canonicalLorentzianTimeDirection] using
      responseCoordinateZero
  · rintro rfl
    exact installMatterLinearTimeResponse_zero configuration

/-! ## State-dependent action response -/

/-- Raw temporal first-jet change determined by the actual-owned action
response and the actual's current temporal covariant derivative. -/
def currentCoframeMatterTimeResponseWrite
    (configuration : StageNineHolonomicConfiguration) :
    DiracExteriorMatterCarrier :=
  actionGeneratedHolonomicCurrentCoframeMatterTimeCovariantDerivative
      configuration 0 -
    holonomicMatterCovariantDerivative configuration 0
      canonicalLorentzianTimeDirection

/-- Apply the unique current-state matter write to the same actual. -/
def actionGeneratedCurrentCoframeMatterTimeResponseActual
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  installMatterLinearTimeResponse configuration
    (currentCoframeMatterTimeResponseWrite configuration)

@[simp] theorem actionGeneratedCurrentCoframeMatterTimeResponseActual_coframe
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedCurrentCoframeMatterTimeResponseActual configuration
      ).coframe =
      configuration.coframe :=
  rfl

@[simp] theorem
    actionGeneratedCurrentCoframeMatterTimeResponseActual_gravityConnection
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedCurrentCoframeMatterTimeResponseActual configuration
      ).gravityConnection =
      configuration.gravityConnection :=
  rfl

@[simp] theorem
    actionGeneratedCurrentCoframeMatterTimeResponseActual_gravityAuxiliary
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedCurrentCoframeMatterTimeResponseActual configuration
      ).gravityAuxiliary =
      configuration.gravityAuxiliary :=
  rfl

@[simp] theorem
    actionGeneratedCurrentCoframeMatterTimeResponseActual_gravitySimplicityMultiplier
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedCurrentCoframeMatterTimeResponseActual configuration
      ).gravitySimplicityMultiplier =
      configuration.gravitySimplicityMultiplier :=
  rfl

@[simp] theorem
    actionGeneratedCurrentCoframeMatterTimeResponseActual_gaugeConnection
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedCurrentCoframeMatterTimeResponseActual configuration
      ).gaugeConnection =
      configuration.gaugeConnection :=
  rfl

@[simp] theorem
    actionGeneratedCurrentCoframeMatterTimeResponseActual_gaugeAuxiliary
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedCurrentCoframeMatterTimeResponseActual configuration
      ).gaugeAuxiliary =
      configuration.gaugeAuxiliary :=
  rfl

@[simp] theorem actionGeneratedCurrentCoframeMatterTimeResponseActual_scalar
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedCurrentCoframeMatterTimeResponseActual configuration
      ).scalar =
      configuration.scalar :=
  rfl

@[simp] theorem
    actionGeneratedCurrentCoframeMatterTimeResponseActual_conjugateMatter
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedCurrentCoframeMatterTimeResponseActual configuration
      ).conjugateMatter =
      configuration.conjugateMatter :=
  rfl

@[simp] theorem
    actionGeneratedCurrentCoframeMatterTimeResponseActual_matter_origin
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedCurrentCoframeMatterTimeResponseActual configuration
      ).matter 0 =
      configuration.matter 0 :=
  installMatterLinearTimeResponse_matter_origin _ _

/-- A temporal matter-response write changes the physical time jet but not
the complete canonical zero slice.  This is the precise state-extraction
boundary used by current-state restarts. -/
theorem
    canonicalCauchyRestriction_zero_actionGeneratedCurrentCoframeMatterTimeResponseActual
    (configuration : StageNineHolonomicConfiguration) :
    canonicalCauchyRestriction 0
        (actionGeneratedCurrentCoframeMatterTimeResponseActual configuration) =
      canonicalCauchyRestriction 0 configuration := by
  apply StageNineCauchyState.ext
  all_goals try rfl
  funext space
  apply matterCoordinateEquiv.injective
  change
    matterCoordinateEquiv
          ((installMatterLinearTimeResponse configuration
              (currentCoframeMatterTimeResponseWrite configuration)).matter
            (canonicalCauchySlicePoint 0 space)) =
      matterCoordinateEquiv
        (configuration.matter (canonicalCauchySlicePoint 0 space))
  rw [installMatterLinearTimeResponse_matter_coordinate]
  simp [matterLinearTimeCoordinateWrite, canonicalCauchySlicePoint,
    canonicalLorentzianTimeDirection, Fin.sum_univ_three]

theorem
    actionGeneratedCurrentCoframeMatterTimeResponseActual_spatialCovariantDerivative
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : Fin 3) :
    holonomicMatterCovariantDerivative
        (actionGeneratedCurrentCoframeMatterTimeResponseActual configuration)
        0 direction.succ =
      holonomicMatterCovariantDerivative configuration 0 direction.succ := by
  unfold actionGeneratedCurrentCoframeMatterTimeResponseActual
  rw [
    holonomicMatterCovariantDerivative_installMatterLinearTimeResponse_origin
      configuration smooth
      (currentCoframeMatterTimeResponseWrite configuration)]
  simp [canonicalLorentzianTimeDirection]

theorem
    actionGeneratedCurrentCoframeMatterTimeResponseActual_timeCovariantDerivative
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    holonomicMatterCovariantDerivative
        (actionGeneratedCurrentCoframeMatterTimeResponseActual configuration)
        0 canonicalLorentzianTimeDirection =
      actionGeneratedHolonomicCurrentCoframeMatterTimeCovariantDerivative
        configuration 0 := by
  unfold actionGeneratedCurrentCoframeMatterTimeResponseActual
  rw [
    holonomicMatterCovariantDerivative_installMatterLinearTimeResponse_origin
      configuration smooth
      (currentCoframeMatterTimeResponseWrite configuration)]
  simp only [if_pos]
  unfold currentCoframeMatterTimeResponseWrite
  abel

theorem
    actionGeneratedCurrentCoframeMatterTimeResponseActual_knownVector
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    holonomicCurrentCoframeMatterKnownVector
        (actionGeneratedCurrentCoframeMatterTimeResponseActual configuration)
        0 =
      holonomicCurrentCoframeMatterKnownVector configuration 0 := by
  unfold holonomicCurrentCoframeMatterKnownVector
  rw [
    actionGeneratedCurrentCoframeMatterTimeResponseActual_coframe,
    actionGeneratedCurrentCoframeMatterTimeResponseActual_scalar,
    actionGeneratedCurrentCoframeMatterTimeResponseActual_matter_origin]
  simp_rw [
    actionGeneratedCurrentCoframeMatterTimeResponseActual_spatialCovariantDerivative
      configuration smooth]

theorem
    actionGeneratedCurrentCoframeMatterTimeResponseActual_satisfies_actionLaw
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (configuration.coframe 0) ≠ 0) :
    HolonomicCurrentCoframeMatterTimeActionLaw
      (actionGeneratedCurrentCoframeMatterTimeResponseActual configuration)
      0
      (holonomicMatterCovariantDerivative
        (actionGeneratedCurrentCoframeMatterTimeResponseActual configuration)
        0 canonicalLorentzianTimeDirection) := by
  have generatedLaw :=
    actionGeneratedHolonomicCurrentCoframeMatterTimeCovariantDerivative_satisfies_actionLaw
      configuration 0 noncharacteristic
  unfold HolonomicCurrentCoframeMatterTimeActionLaw at generatedLaw ⊢
  rw [
    actionGeneratedCurrentCoframeMatterTimeResponseActual_coframe,
    actionGeneratedCurrentCoframeMatterTimeResponseActual_knownVector
      configuration smooth,
    actionGeneratedCurrentCoframeMatterTimeResponseActual_timeCovariantDerivative
      configuration smooth]
  exact generatedLaw

theorem
    actionGeneratedCurrentCoframeMatterTimeResponseActual_timeDerivative_eq_generated :
    ∀ (configuration : StageNineHolonomicConfiguration)
      (_smooth : configuration.Smooth)
      (_noncharacteristic :
        coframeTemporalPrincipalScalar (configuration.coframe 0) ≠ 0),
      holonomicMatterCovariantDerivative
          (actionGeneratedCurrentCoframeMatterTimeResponseActual configuration)
          0 canonicalLorentzianTimeDirection =
        actionGeneratedHolonomicCurrentCoframeMatterTimeCovariantDerivative
          (actionGeneratedCurrentCoframeMatterTimeResponseActual configuration)
          0 := by
  intro configuration smooth noncharacteristic
  let actual :=
    actionGeneratedCurrentCoframeMatterTimeResponseActual configuration
  have actualNoncharacteristic :
      coframeTemporalPrincipalScalar (actual.coframe 0) ≠ 0 := by
    simpa [actual] using noncharacteristic
  exact
    holonomicCurrentCoframeMatterTimeActionLaw_unique
      actual 0 actualNoncharacteristic _ _
      (actionGeneratedCurrentCoframeMatterTimeResponseActual_satisfies_actionLaw
        configuration smooth noncharacteristic)
      (actionGeneratedHolonomicCurrentCoframeMatterTimeCovariantDerivative_satisfies_actionLaw
        actual 0 actualNoncharacteristic)

theorem actionGeneratedCurrentCoframeMatterTimeResponseActual_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    (actionGeneratedCurrentCoframeMatterTimeResponseActual configuration
      ).Smooth :=
  installMatterLinearTimeResponse_smooth configuration smooth _

theorem actionGeneratedCurrentCoframeMatterTimeResponseActual_nondegenerate
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate) :
    (actionGeneratedCurrentCoframeMatterTimeResponseActual configuration
      ).Nondegenerate :=
  installMatterLinearTimeResponse_nondegenerate configuration nondegenerate _

theorem actionGeneratedCurrentCoframeMatterTimeResponseActual_eq_iff
    (configuration : StageNineHolonomicConfiguration) :
    actionGeneratedCurrentCoframeMatterTimeResponseActual configuration =
        configuration ↔
      holonomicMatterCovariantDerivative configuration 0
          canonicalLorentzianTimeDirection =
        actionGeneratedHolonomicCurrentCoframeMatterTimeCovariantDerivative
          configuration 0 := by
  change
    installMatterLinearTimeResponse configuration
          (currentCoframeMatterTimeResponseWrite configuration) =
        configuration ↔
      _
  rw [installMatterLinearTimeResponse_eq_iff]
  unfold currentCoframeMatterTimeResponseWrite
  constructor
  · intro responseZero
    exact (sub_eq_zero.mp responseZero).symm
  · intro alreadyGenerated
    exact sub_eq_zero.mpr alreadyGenerated.symm

end

end
  SaturationMonoid.PhysicsCore.StageNineCurrentCoframeMatterTimeResponseActualLift
