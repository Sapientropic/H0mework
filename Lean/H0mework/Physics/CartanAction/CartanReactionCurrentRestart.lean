import H0mework.Physics.CartanAction.CartanConnectionLocalActualLift
import H0mework.Physics.DualVariation.JointResidualCarrier
import H0mework.Physics.Exterior.GravityMultiplierAuxiliaryIntegratedVariation
import H0mework.Physics.Lorentz.LorentzConnectionExteriorActionZeroFiber

/-!
# Current-native Cartan and gravity-reaction restart

This module gives the dependency-light current-state restart

```text
current
  -> write omega(p) from the repaired-action Cartan producer on current
  -> compute B(p) := II+(current.coframe(p))
  -> compute lambda from the live B and the curvature of the written omega.
```

The constructor accepts only a source and an arbitrary holonomic current.
It accepts no response, residual, target field, equation, receipt, branch
choice, curvature value, or stationarity certificate.  The coframe and all
unwritten gauge/matter primitives are preserved from `current`.

The readback theorems are producer-soundness: W13 blindness makes the written
connection self-generated on the final actual; the reaction evaluator is
blind to the multiplier it writes; and the typed Cartan torsion reproduces
the same final action spin response at every nondegenerate point.  No old
curvature settlement is transported through this restart.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanReactionCurrentRestart

open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCartanAffineConnectionActualization
open StageNineCartanTorsionThreeFormEquiv
open StageNineCoframeFirstJet
open StageNineCartanTorsionThreeFormCoordinates
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineEnrichedProofFreeSource
open StageNineFormNativeIIPlusJetKinematics
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeLorentzGeometricKinematics
open StageNineFormNativeLorentzTorsionSpinEquation
open StageNineFormNativeMatterSpinThreeForm
open StageNineGlobalIntegratedAction
open StageNineGravityBianchi
open StageNineHolonomicField
open StageNineIIPlusRestriction
open StageNineLorentzConnectionVariation
open StageNineLorentzConnectionExteriorActionZeroFiber
open StageNineMatterCovariantDerivativeAffine
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineTopologicalLorentzThreeFormDuality
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

/-! ## Current-state writes -/

/-- First restart leg: replace only the primitive Lorentz connection by the
pointwise repaired-action Cartan producer evaluated on `current`. -/
def diracDualFormNativeCartanConnectionWrittenCurrent
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { current with
    gravityConnection := fun point =>
      diracDualFormNativeActionCartanConnectionAt source current point }

/-- Explicit simplicity preparation after the connection write.  This
computes `B := II+(e)` while retaining the literal current coframe. -/
def diracDualFormNativeCartanSimplicityPreparedCurrent
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  restrictHolonomicConfigurationToIIPlus
    (diracDualFormNativeCartanConnectionWrittenCurrent source current)

/-- Live action reaction evaluated after both the connection write and the
explicit computed-`II+` preparation. -/
def diracDualFormNativeCartanReactionCurrentField
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    BasePoint → PhysicalBivector :=
  formNativeGravityReactionField
    (diracDualFormNativeCartanSimplicityPreparedCurrent source current)

/-- Joint current-native restart.  The final write changes only `lambda`
relative to the connection-written, computed-`II+` actual. -/
def sourceActionGeneratedDiracDualCartanReactionCurrentRestart
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { diracDualFormNativeCartanSimplicityPreparedCurrent source current with
    gravitySimplicityMultiplier :=
      diracDualFormNativeCartanReactionCurrentField source current }

/-! ## Primitive-field provenance -/

@[simp] theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
      source current).coframe = current.coframe :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
      source current).gravityConnection =
        fun point =>
          diracDualFormNativeActionCartanConnectionAt source current point :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_auxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        source current).gravityAuxiliary point =
      physicalIIPlusBivector (current.coframe point) :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_multiplier
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
      source current).gravitySimplicityMultiplier =
        diracDualFormNativeCartanReactionCurrentField source current :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
      source current).gaugeConnection = current.gaugeConnection :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
      source current).gaugeAuxiliary = current.gaugeAuxiliary :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
      source current).scalar = current.scalar :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
      source current).matter = current.matter :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
      source current).conjugateMatter = current.conjugateMatter :=
  rfl

/-- The Cartan/reaction restart changes no field read by the scalar Euler
coefficient. -/
theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalarResidual_eq_current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual source
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        source current) point).scalar =
      (diracDualFormNativePointwiseJointResidual source current point).scalar :=
  rfl

/-! ## Final-actual producer soundness -/

/-- Recomputing the Cartan producer on the final actual returns the installed
connection.  The proof uses only W13 blindness to the written `B`, `omega`,
and `lambda` fields. -/
theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection_selfGenerated
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        source current).gravityConnection point =
      diracDualFormNativeActionCartanConnectionAt source
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current) point := by
  let final :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  change
    diracDualFormNativeActionCartanConnectionAt source current point =
      diracDualFormNativeActionCartanConnectionAt source final point
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
    source current final point rfl rfl rfl]
  rfl

/-- The final multiplier is the reaction recomputed on the final actual.
This is the dependency fact that the reaction reads `B` and `omega`, not the
multiplier it writes. -/
theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_reaction_selfGenerated
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        source current).gravitySimplicityMultiplier =
      formNativeGravityReactionField
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current) :=
  rfl

/-- The source/current Cartan-reaction write is a projector.  Its first
application installs the action Cartan connection and the corresponding live
reaction; a second application reads the same coframe and matter fields and
therefore emits the identical current. -/
theorem sourceActionGeneratedDiracDualCartanReactionCurrentRestart_idempotent
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current) =
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        source current := by
  let final :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  apply StageNineHolonomicConfiguration.ext
  · rfl
  · funext point
    exact
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection_selfGenerated
        source current point).symm
  · rfl
  · change formNativeGravityReactionField
        (diracDualFormNativeCartanSimplicityPreparedCurrent source final) =
      formNativeGravityReactionField final
    congr 1
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The explicit computed-`II+` middle step makes the final actual satisfy
the form-native simplicity equation while preserving `current.coframe`. -/
theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_simplicity
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    FormNativeGravitySimplicityEquation
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        source current) := by
  intro point
  rfl

/-- Producer soundness for the action-derived auxiliary equation.  The
equation is not counted as an independent constraint because its unique
reaction normal form defines the final multiplier write. -/
theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_auxiliaryEquation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    FormNativeGravityAuxiliaryEquation
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        source current) := by
  exact
    (formNativeGravityAuxiliaryEquation_iff_multiplier_eq_reaction
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        source current)).2
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_reaction_selfGenerated
        source current)

/-- Typed pointwise torsion--spin readback on the same final actual.  The
nondegeneracy hypothesis is only the algebraic invertibility gate for the
Cartan torsion/three-form equivalence. -/
theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_typedTorsionSpinAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    cartanTorsionThreeForm
        ((sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current).coframe point)
        (actualPointwiseCartanTorsionTwoForm
          (holonomicCoframeFirstJetAt
            (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
              source current).coframe point)
          ((sourceActionGeneratedDiracDualCartanReactionCurrentRestart
            source current).gravityConnection point)) =
      diracDualFormNativeActionSpinResponseAt source
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current) point := by
  rw [
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection_selfGenerated
      source current point]
  exact
    diracDualFormNativeActionCartanConnectionAt_generates_spinResponse source
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        source current)
      point (by simpa using nondegenerate)

/-- A computed-`II+` Lorentz zero fiber is a fixed point of the action-native
Cartan connection producer.  This is a dependency theorem: it identifies an
already stationary connection with the restart output and creates no write. -/
theorem gravityConnection_eq_actionCartanConnectionAt_of_lorentzEulerThreeForm_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeSmooth : ContDiff ℝ ∞ configuration.coframe)
    (nondegenerate : Matrix.det (configuration.coframe point) ≠ 0)
    (connectionSkew : LorentzSkew (configuration.gravityConnection point))
    (simplicity : FormNativeGravitySimplicityEquation configuration)
    (lorentzZero :
      holonomicFormNativeLorentzEulerThreeForm source 0 configuration point =
        0) :
    configuration.gravityConnection point =
      diracDualFormNativeActionCartanConnectionAt source configuration point := by
  have restricted :
      restrictHolonomicConfigurationToIIPlus configuration = configuration := by
    apply StageNineHolonomicConfiguration.ext <;> try rfl
    funext candidate
    exact (simplicity candidate).symm
  have currentEquation :=
    (holonomicFormNativeLorentzEulerThreeForm_eq_zero_iff_current
      source 0 configuration point).1 lorentzZero
  have currentTorsionSpin :
      cartanTorsionThreeForm (configuration.coframe point)
          (actualPointwiseCartanTorsionTwoForm
            (holonomicCoframeFirstJetAt configuration.coframe point)
            (configuration.gravityConnection point)) =
        diracDualFormNativeActionSpinResponseAt source configuration point := by
    calc
      cartanTorsionThreeForm (configuration.coframe point)
          (actualPointwiseCartanTorsionTwoForm
            (holonomicCoframeFirstJetAt configuration.coframe point)
            (configuration.gravityConnection point)) =
          internalBivectorDualThreeForm
            (torsionCoframeWedgeThreeForm (configuration.coframe point)
              (pointwiseCartanTorsion
                (holonomicCoframeFirstJetAt configuration.coframe point)
                (configuration.gravityConnection point))) :=
        cartanTorsionThreeForm_actualPointwiseCartanTorsionTwoForm
          (configuration.coframe point)
          (holonomicCoframeFirstJetAt configuration.coframe point)
          (configuration.gravityConnection point)
      _ = holonomicGravityAuxiliaryExteriorCovariantDerivative
            configuration point := by
        symm
        calc
          holonomicGravityAuxiliaryExteriorCovariantDerivative
                configuration point =
              holonomicGravityAuxiliaryExteriorCovariantDerivative
                (restrictHolonomicConfigurationToIIPlus configuration) point := by
            rw [restricted]
          _ = internalBivectorDualThreeForm
                (torsionCoframeWedgeThreeForm
                  (configuration.coframe point)
                  (pointwiseCartanTorsion
                    (holonomicCoframeFirstJetAt configuration.coframe point)
                    (configuration.gravityConnection point))) := by
            change
              pointwisePhysicalBivectorExteriorCovariantDerivative
                  (configuration.gravityConnection point)
                  (holonomicGravityAuxiliaryJet
                    (restrictHolonomicConfigurationToIIPlus configuration)
                    point) = _
            rw [holonomicGravityAuxiliaryJet_restrictToIIPlus_of_coframeContDiff
              configuration coframeSmooth point]
            exact
              pointwisePhysicalIIPlus_exteriorCovariantDerivative_eq_torsionCoframe
                (holonomicCoframeFirstJetAt configuration.coframe point)
                (configuration.gravityConnection point) connectionSkew
      _ = formNativePhysicalSpinCurrentThreeForm source 0 point
            (toContinuumPointField configuration point) := currentEquation
      _ = diracDualFormNativeActionSpinResponseAt source configuration point := by
        unfold diracDualFormNativeActionSpinResponseAt
        rw [restricted]
  have generatedTorsionSpin :=
    diracDualFormNativeActionCartanConnectionAt_generates_spinResponse
      source configuration point nondegenerate
  have torsionEqual :
      actualPointwiseCartanTorsionTwoForm
          (holonomicCoframeFirstJetAt configuration.coframe point)
          (configuration.gravityConnection point) =
        actualPointwiseCartanTorsionTwoForm
          (holonomicCoframeFirstJetAt configuration.coframe point)
          (diracDualFormNativeActionCartanConnectionAt source configuration
            point) := by
    exact
      (cartanTorsionThreeForm_injective (configuration.coframe point)
        nondegenerate) (currentTorsionSpin.trans generatedTorsionSpin.symm)
  exact
    actualPointwiseCartanTorsionTwoForm_injective_on_lorentzSkew
      (holonomicCoframeFirstJetAt configuration.coframe point)
      nondegenerate (configuration.gravityConnection point)
      (diracDualFormNativeActionCartanConnectionAt source configuration point)
      connectionSkew
      (diracDualFormNativeActionCartanConnectionAt_lorentzSkew source
        configuration point nondegenerate)
      torsionEqual

/-- The current-native restart inhabits the Lorentz-skew connection domain
wherever its preserved coframe is nondegenerate.  Nondegeneracy is consumed
only by this producer-soundness readback; it is not an input to the restart. -/
theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_lorentzAdmissible
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate) :
    GravityConnectionLorentzAdmissible
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        source current) := by
  intro point
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  exact diracDualFormNativeActionCartanConnectionAt_lorentzSkew source
    current point (nondegenerate point)

/-- The pointwise Cartan response generated by the restart is the complete
computed-`II+` torsion--spin equation on that same actual. -/
theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_torsionSpinEquation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate) :
    FormNativeIIPlusTorsionSpinEquation source
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        source current) := by
  intro point
  rw [← cartanTorsionThreeForm_actualPointwiseCartanTorsionTwoForm]
  exact
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_typedTorsionSpinAt
      source current point (nondegenerate point)

/-- **Pointwise positive readback.**  At any nondegenerate point of a smooth
current, the source/action-native Cartan restart lands directly in the zero
fiber of the complete Lorentz Euler three-form.  The constructor remains the
same proof-free restart; smoothness and pointwise nondegeneracy enter only
when its actual derivative and Cartan inverse are read back. -/
theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_lorentzEulerThreeForm_zero_at_of_coframeContDiff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (coframeSmooth : ContDiff ℝ ∞ current.coframe)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    holonomicFormNativeLorentzEulerThreeForm source 0
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current) point =
      0 := by
  let final :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source current
  have finalRestricted :
      restrictHolonomicConfigurationToIIPlus final = final :=
    by
      apply StageNineHolonomicConfiguration.ext <;> rfl
  have finalLorentzSkew : LorentzSkew (final.gravityConnection point) := by
    change LorentzSkew
      (diracDualFormNativeActionCartanConnectionAt source current point)
    exact diracDualFormNativeActionCartanConnectionAt_lorentzSkew source
      current point nondegenerate
  have torsionSpin :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_typedTorsionSpinAt
      source current point nondegenerate
  apply
    (holonomicFormNativeLorentzEulerThreeForm_eq_zero_iff_current source 0
      final point).2
  calc
    holonomicGravityAuxiliaryExteriorCovariantDerivative final point =
        holonomicGravityAuxiliaryExteriorCovariantDerivative
          (restrictHolonomicConfigurationToIIPlus final) point := by
      rw [finalRestricted]
    _ = internalBivectorDualThreeForm
          (torsionCoframeWedgeThreeForm (final.coframe point)
            (pointwiseCartanTorsion
              (holonomicCoframeFirstJetAt final.coframe point)
              (final.gravityConnection point))) := by
      change
        pointwisePhysicalBivectorExteriorCovariantDerivative
            (final.gravityConnection point)
            (holonomicGravityAuxiliaryJet
              (restrictHolonomicConfigurationToIIPlus final) point) = _
      have finalCoframeSmooth :
          ContDiff ℝ ∞ final.coframe := by
        simpa [final] using coframeSmooth
      rw [holonomicGravityAuxiliaryJet_restrictToIIPlus_of_coframeContDiff
        final finalCoframeSmooth point]
      exact
        pointwisePhysicalIIPlus_exteriorCovariantDerivative_eq_torsionCoframe
          (holonomicCoframeFirstJetAt final.coframe point)
          (final.gravityConnection point) finalLorentzSkew
    _ = diracDualFormNativeActionSpinResponseAt source final point := by
      rw [← cartanTorsionThreeForm_actualPointwiseCartanTorsionTwoForm]
      simpa [final] using torsionSpin
    _ = formNativePhysicalSpinCurrentThreeForm source 0 point
          (toContinuumPointField final point) := by
      unfold diracDualFormNativeActionSpinResponseAt
      rw [finalRestricted]

/-- Componentwise holonomic smoothness supplies the coframe-only pointwise
mouth above.  This wrapper preserves the convenient whole-current interface
for already regular configurations. -/
theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_lorentzEulerThreeForm_zero_at
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    holonomicFormNativeLorentzEulerThreeForm source 0
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current) point =
      0 := by
  have coframeSmooth : ContDiff ℝ ∞ current.coframe := by
    apply contDiff_pi'
    intro row
    apply contDiff_pi'
    intro column
    exact smooth.1 row column
  exact
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_lorentzEulerThreeForm_zero_at_of_coframeContDiff
      source current coframeSmooth point nondegenerate

/-- Global corollary of the pointwise native Cartan zero-fiber theorem. -/
theorem
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_lorentzEulerThreeForm_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    holonomicFormNativeLorentzEulerThreeForm source 0
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          source current) =
      0 := by
  funext point
  exact
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_lorentzEulerThreeForm_zero_at
      source current smooth point (nondegenerate point)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanReactionCurrentRestart
