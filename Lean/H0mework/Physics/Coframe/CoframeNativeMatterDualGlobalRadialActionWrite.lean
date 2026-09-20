import H0mework.Physics.Coframe.CoframeNativeConjugateMatterOriginActionWrite
import H0mework.Physics.Jets.RadialCurveIntegralFirstJet

/-!
# Coframe-native global matter/dual radial action write

The current field generates its frame-time primal response at every
spacetime point.  The coframe row turns those responses into a genuine
one-form, and the canonical radial path compiler emits one whole matter
field.  The adjoint response is then recomputed on that primal output and
compiled in the same way.

Both constructors consume only the current.  They accept no residual,
support, target field, closedness law, branch, or zero-fiber receipt.
Closedness can later identify the emitted radial first jet with the original
one-form, but it is an acceptance law and is not part of the writer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCoframeNativeMatterDualGlobalRadialActionWrite

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCoframeNativeConjugateMatterFrameAction
open StageNineCoframeNativeConjugateMatterOriginActionWrite
open StageNineCoframeNativeMatterFrameAction
open StageNineCoframeNativeMatterOriginActionWrite
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDynamicBreakingVacuum
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineMatterVariation
open StageNineRadialCurveIntegralFirstJet

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-! ## Primal whole-field action write -/

/-- The branch-free frame-time derivative selected by the matter action at
one point of the current. -/
def globalFrameTimeMatterGeneratedDerivativeAt
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : DiracExteriorMatterCarrier :=
  actionGeneratedFrameTimeMatterDerivative
    (current.coframe point)
    (holonomicMatterCovariantDerivative current point)
    (scalarCoordinateEquiv.symm (current.scalar point))
    (current.matter point)

/-- The pointwise response still to be added to the current frame-time
matter derivative. -/
def globalFrameTimeMatterResponseAt
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : DiracExteriorMatterCarrier :=
  globalFrameTimeMatterGeneratedDerivativeAt current point -
    frameMatterDerivative (current.coframe point)
      (holonomicMatterCovariantDerivative current point) 0

@[simp] theorem globalFrameTimeMatterGeneratedDerivativeAt_origin
    (current : StageNineHolonomicConfiguration) :
    globalFrameTimeMatterGeneratedDerivativeAt current 0 =
      originFrameTimeMatterGeneratedDerivative current :=
  rfl

@[simp] theorem globalFrameTimeMatterResponseAt_origin
    (current : StageNineHolonomicConfiguration) :
    globalFrameTimeMatterResponseAt current 0 =
      originFrameTimeMatterResponse current :=
  rfl

/-- Current-owned response one-form.  Its value at `p` occupies exactly the
internal frame-time slot selected by `current.coframe p`. -/
def coframeNativeGlobalMatterResponseOneForm
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : BasePoint →L[ℝ] MatterCoordinateCarrier :=
  (coframeRowLinearFunctional (current.coframe point)).smulRight
    (matterCoordinateEquiv (globalFrameTimeMatterResponseAt current point))

/-- Canonical source-anchored radial integral of the emitted matter
response one-form. -/
def coframeNativeGlobalMatterRadialIncrement
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : MatterCoordinateCarrier :=
  ∫ᶜ contact in Path.segment (0 : BasePoint) point,
    coframeNativeGlobalMatterResponseOneForm current contact

/-- Whole-field primal write generated from the current action reads. -/
def actionGeneratedGlobalFrameTimeMatterActual
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  varyMatterCoordinates current
    (coframeNativeGlobalMatterRadialIncrement current) 1

@[simp] theorem coframeNativeGlobalMatterRadialIncrement_origin
    (current : StageNineHolonomicConfiguration) :
    coframeNativeGlobalMatterRadialIncrement current 0 = 0 := by
  simp [coframeNativeGlobalMatterRadialIncrement]

@[simp] theorem actionGeneratedGlobalFrameTimeMatterActual_coframe
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedGlobalFrameTimeMatterActual current).coframe =
      current.coframe :=
  rfl

@[simp] theorem
    actionGeneratedGlobalFrameTimeMatterActual_gravityConnection
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedGlobalFrameTimeMatterActual current).gravityConnection =
      current.gravityConnection :=
  rfl

@[simp] theorem
    actionGeneratedGlobalFrameTimeMatterActual_gravityAuxiliary
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedGlobalFrameTimeMatterActual current).gravityAuxiliary =
      current.gravityAuxiliary :=
  rfl

@[simp] theorem
    actionGeneratedGlobalFrameTimeMatterActual_gravitySimplicityMultiplier
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedGlobalFrameTimeMatterActual current
      ).gravitySimplicityMultiplier = current.gravitySimplicityMultiplier :=
  rfl

@[simp] theorem actionGeneratedGlobalFrameTimeMatterActual_gaugeConnection
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedGlobalFrameTimeMatterActual current).gaugeConnection =
      current.gaugeConnection :=
  rfl

@[simp] theorem actionGeneratedGlobalFrameTimeMatterActual_gaugeAuxiliary
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedGlobalFrameTimeMatterActual current).gaugeAuxiliary =
      current.gaugeAuxiliary :=
  rfl

@[simp] theorem actionGeneratedGlobalFrameTimeMatterActual_scalar
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedGlobalFrameTimeMatterActual current).scalar =
      current.scalar :=
  rfl

@[simp] theorem actionGeneratedGlobalFrameTimeMatterActual_conjugateMatter
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedGlobalFrameTimeMatterActual current).conjugateMatter =
      current.conjugateMatter :=
  rfl

theorem actionGeneratedGlobalFrameTimeMatterActual_matterCoordinates
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    matterCoordinateEquiv
        ((actionGeneratedGlobalFrameTimeMatterActual current).matter point) =
      matterCoordinateEquiv (current.matter point) +
        coframeNativeGlobalMatterRadialIncrement current point := by
  simp [actionGeneratedGlobalFrameTimeMatterActual, varyMatterCoordinates]

@[simp] theorem actionGeneratedGlobalFrameTimeMatterActual_matter_origin
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedGlobalFrameTimeMatterActual current).matter 0 =
      current.matter 0 := by
  apply matterCoordinateEquiv.injective
  simp [actionGeneratedGlobalFrameTimeMatterActual_matterCoordinates]

theorem actionGeneratedGlobalFrameTimeMatterActual_nondegenerate
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate) :
    (actionGeneratedGlobalFrameTimeMatterActual current).Nondegenerate := by
  simpa [StageNineHolonomicConfiguration.Nondegenerate] using nondegenerate

/-! ## Adjoint whole-field action write -/

/-- The drift-aware adjoint frame-time derivative generated on the supplied
current. -/
def globalFrameTimeConjugateMatterGeneratedDerivativeAt
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  holonomicDiracDualLiveCoframeConjugateMatterFrameActionVelocity current point

/-- Remaining adjoint frame-time response at one point. -/
def globalFrameTimeConjugateMatterResponseAt
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  globalFrameTimeConjugateMatterGeneratedDerivativeAt current point -
    holonomicFrameConjugateMatterDerivative current point 0

@[simp] theorem globalFrameTimeConjugateMatterGeneratedDerivativeAt_origin
    (current : StageNineHolonomicConfiguration) :
    globalFrameTimeConjugateMatterGeneratedDerivativeAt current 0 =
      originFrameTimeConjugateMatterGeneratedDerivative current :=
  rfl

@[simp] theorem globalFrameTimeConjugateMatterResponseAt_origin
    (current : StageNineHolonomicConfiguration) :
    globalFrameTimeConjugateMatterResponseAt current 0 =
      originFrameTimeConjugateMatterResponse current :=
  rfl

/-- Adjoint response one-form generated after the primal write. -/
def coframeNativeGlobalConjugateMatterResponseOneForm
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : BasePoint →L[ℝ] MatterCoordinateCarrier :=
  (coframeRowLinearFunctional (current.coframe point)).smulRight
    (matterDualCoordinates
      (globalFrameTimeConjugateMatterResponseAt current point))

/-- Canonical radial integral of the adjoint action response. -/
def coframeNativeGlobalConjugateMatterRadialIncrement
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : MatterCoordinateCarrier :=
  ∫ᶜ contact in Path.segment (0 : BasePoint) point,
    coframeNativeGlobalConjugateMatterResponseOneForm current contact

/-- Whole-field adjoint write generated on its supplied current. -/
def actionGeneratedGlobalFrameTimeConjugateMatterActual
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  varyConjugateMatterCoordinates current
    (coframeNativeGlobalConjugateMatterRadialIncrement current) 1

/-- Ordered primal-then-adjoint global action output.  The adjoint response is
computed on the emitted primal actual, never frozen on the input current. -/
def actionGeneratedGlobalFrameMatterDualActual
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  actionGeneratedGlobalFrameTimeConjugateMatterActual
    (actionGeneratedGlobalFrameTimeMatterActual current)

@[simp] theorem coframeNativeGlobalConjugateMatterRadialIncrement_origin
    (current : StageNineHolonomicConfiguration) :
    coframeNativeGlobalConjugateMatterRadialIncrement current 0 = 0 := by
  simp [coframeNativeGlobalConjugateMatterRadialIncrement]

@[simp] theorem actionGeneratedGlobalFrameTimeConjugateMatterActual_coframe
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedGlobalFrameTimeConjugateMatterActual current).coframe =
      current.coframe :=
  rfl

@[simp] theorem
    actionGeneratedGlobalFrameTimeConjugateMatterActual_gravityConnection
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedGlobalFrameTimeConjugateMatterActual current
      ).gravityConnection = current.gravityConnection :=
  rfl

@[simp] theorem
    actionGeneratedGlobalFrameTimeConjugateMatterActual_gravityAuxiliary
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedGlobalFrameTimeConjugateMatterActual current
      ).gravityAuxiliary = current.gravityAuxiliary :=
  rfl

@[simp] theorem
    actionGeneratedGlobalFrameTimeConjugateMatterActual_gravitySimplicityMultiplier
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedGlobalFrameTimeConjugateMatterActual current
      ).gravitySimplicityMultiplier = current.gravitySimplicityMultiplier :=
  rfl

@[simp] theorem
    actionGeneratedGlobalFrameTimeConjugateMatterActual_gaugeConnection
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedGlobalFrameTimeConjugateMatterActual current
      ).gaugeConnection = current.gaugeConnection :=
  rfl

@[simp] theorem actionGeneratedGlobalFrameTimeConjugateMatterActual_gaugeAuxiliary
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedGlobalFrameTimeConjugateMatterActual current
      ).gaugeAuxiliary = current.gaugeAuxiliary :=
  rfl

@[simp] theorem actionGeneratedGlobalFrameTimeConjugateMatterActual_scalar
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedGlobalFrameTimeConjugateMatterActual current).scalar =
      current.scalar :=
  rfl

@[simp] theorem actionGeneratedGlobalFrameTimeConjugateMatterActual_matter
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedGlobalFrameTimeConjugateMatterActual current).matter =
      current.matter :=
  rfl

theorem actionGeneratedGlobalFrameTimeConjugateMatterActual_coordinates
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicConjugateMatterCoordinates
        (actionGeneratedGlobalFrameTimeConjugateMatterActual current) point =
      holonomicConjugateMatterCoordinates current point +
        coframeNativeGlobalConjugateMatterRadialIncrement current point := by
  apply PiLp.ext
  intro index
  simp [holonomicConjugateMatterCoordinates,
    actionGeneratedGlobalFrameTimeConjugateMatterActual,
    varyConjugateMatterCoordinates, matterDualCoordinates,
    matterDualOfCoordinates_basis_apply]

@[simp] theorem actionGeneratedGlobalFrameTimeConjugateMatterActual_origin
    (current : StageNineHolonomicConfiguration) :
    (actionGeneratedGlobalFrameTimeConjugateMatterActual current
      ).conjugateMatter 0 = current.conjugateMatter 0 := by
  apply matterDualCoordinates_injective
  simpa [holonomicConjugateMatterCoordinates] using
    actionGeneratedGlobalFrameTimeConjugateMatterActual_coordinates current 0

theorem actionGeneratedGlobalFrameTimeConjugateMatterActual_nondegenerate
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate) :
    (actionGeneratedGlobalFrameTimeConjugateMatterActual current
      ).Nondegenerate := by
  simpa [StageNineHolonomicConfiguration.Nondegenerate] using nondegenerate

/-! ## Ordered whole-output custody -/

theorem actionGeneratedGlobalFrameMatterDualActual_fieldInventory
    (current : StageNineHolonomicConfiguration) :
    let primal := actionGeneratedGlobalFrameTimeMatterActual current
    let output := actionGeneratedGlobalFrameMatterDualActual current
    output.coframe = current.coframe ∧
      output.gravityConnection = current.gravityConnection ∧
      output.gravityAuxiliary = current.gravityAuxiliary ∧
      output.gravitySimplicityMultiplier =
        current.gravitySimplicityMultiplier ∧
      output.gaugeConnection = current.gaugeConnection ∧
      output.gaugeAuxiliary = current.gaugeAuxiliary ∧
      output.scalar = current.scalar ∧
      output.matter = primal.matter ∧
      output.conjugateMatter 0 = current.conjugateMatter 0 := by
  dsimp only [actionGeneratedGlobalFrameMatterDualActual]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    actionGeneratedGlobalFrameTimeConjugateMatterActual_origin _⟩

theorem actionGeneratedGlobalFrameMatterDualActual_nondegenerate
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate) :
    (actionGeneratedGlobalFrameMatterDualActual current).Nondegenerate :=
  actionGeneratedGlobalFrameTimeConjugateMatterActual_nondegenerate _
    (actionGeneratedGlobalFrameTimeMatterActual_nondegenerate current
      nondegenerate)

end

end
  SaturationMonoid.PhysicsCore.StageNineCoframeNativeMatterDualGlobalRadialActionWrite
