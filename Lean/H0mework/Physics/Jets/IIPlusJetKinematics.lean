import H0mework.Physics.CoframeJets.CoframeFirstJet
import H0mework.Physics.Lorentz.LorentzGeometricKinematics
import H0mework.Physics.Exterior.IIPlusFieldVariation
import H0mework.Physics.Geometry.IIPlusRestriction

/-!
# Actual `II+` jet and form-native KIN-1 specialization

This module closes the missing whole-field chain rule for the computed
restriction `B := II+(e)`.  It first proves that the actual Fréchet jet of the
restricted gravity-auxiliary field is exactly the native `D II+` image of the
actual primitive coframe jet.  It then specializes the already established
formulation-neutral KIN-1 identity on the same restricted actual:

```text
D_omega II+(e) = star_internal (T(omega,e) wedge e).
```

The restriction is a derived actual computed from the live coframe.  It is
not a source-native next state and does not prove that the unreduced input
already satisfies simplicity.  These results are kinematic transporters:
they consume no action equation, stationarity, torsion solution, source
receipt, branch choice, residual value, or fixed actual.  The Lorentz-skew
domain remains explicit.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineFormNativeIIPlusJetKinematics

open ProofFreeRicherAnholonomicSource
open StageNineCartanTangentSimplicityResponse
open StageNineCoframeFirstJet
open StageNineFormNativeLorentzGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineGravityBianchi
open StageNineHolonomicField
open StageNineIIPlusRestriction
open StageNineResidualLinearPlebanskiTorsionReduction
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

/-- Extensionality for the value and complete directional derivative stored
in a pointwise physical-bivector jet. -/
private theorem pointwisePhysicalBivectorJet_eq_of_fields_eq
    (first second : PointwisePhysicalBivectorJet)
    (value : first.value = second.value)
    (derivative : first.derivative = second.derivative) :
    first = second := by
  cases first with
  | mk firstValue firstDerivative =>
      cases second with
      | mk secondValue secondDerivative =>
          change firstValue = secondValue at value
          change firstDerivative = secondDerivative at derivative
          subst secondValue
          subst secondDerivative
          rfl

/-- Whole primitive coframe smoothness assembled from the componentwise
holonomic smoothness carrier. -/
private theorem holonomicCoframe_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    ContDiff ℝ ∞ configuration.coframe := by
  apply contDiff_pi'
  intro internal
  apply contDiff_pi'
  intro coordinate
  exact smooth.1 internal coordinate

/-- The actual whole-field directional derivative after computed `II+`
restriction is the native coframe tangent `D II+(e)[partial e]`. -/
theorem gravityAuxiliaryDirectionalDerivative_restrictToIIPlus
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (direction : LorentzianIndex) :
    gravityAuxiliaryDirectionalDerivative
        (restrictHolonomicConfigurationToIIPlus configuration)
        point direction =
      physicalIIPlusCoframeTangent (configuration.coframe point)
        ((holonomicCoframeFirstJetAt configuration.coframe point).derivative
          direction) := by
  have coframeSmooth : ContDiff ℝ ∞ configuration.coframe :=
    holonomicCoframe_contDiff configuration smooth
  have iiPlusSmooth : ContDiff ℝ ∞ fun candidate =>
      physicalIIPlusBivector (configuration.coframe candidate) :=
    physicalIIPlusBivector_contDiff.comp coframeSmooth
  funext internalPair spacetimePair
  have internalPairSmooth : ContDiff ℝ ∞ fun candidate =>
      physicalIIPlusBivector (configuration.coframe candidate)
        internalPair :=
    contDiff_pi.mp iiPlusSmooth internalPair
  calc
    (gravityAuxiliaryDirectionalDerivative
        (restrictHolonomicConfigurationToIIPlus configuration)
        point direction) internalPair spacetimePair =
      (fieldDirectionalDerivative
        (fun candidate =>
          physicalIIPlusBivector (configuration.coframe candidate))
        point direction) internalPair spacetimePair := rfl
    _ =
      (fieldDirectionalDerivative
        (fun candidate =>
          physicalIIPlusBivector (configuration.coframe candidate)
            internalPair)
        point direction) spacetimePair := by
          rw [fieldDirectionalDerivative_pi_apply
            (fun candidate =>
              physicalIIPlusBivector (configuration.coframe candidate))
            iiPlusSmooth point direction internalPair]
    _ =
      fieldDirectionalDerivative
        (fun candidate =>
          physicalIIPlusBivector (configuration.coframe candidate)
            internalPair spacetimePair)
        point direction := by
          rw [fieldDirectionalDerivative_pi_apply
            (fun candidate =>
              physicalIIPlusBivector (configuration.coframe candidate)
                internalPair)
            internalPairSmooth point direction spacetimePair]
    _ =
      physicalIIPlusCoframeTangent (configuration.coframe point)
          (coframeFieldDirectionalTangent configuration.coframe point
            direction)
        internalPair spacetimePair :=
      physicalIIPlusBivector_fieldDirectionalDerivative
        configuration.coframe smooth.1 point direction internalPair
          spacetimePair
    _ =
      physicalIIPlusCoframeTangent (configuration.coframe point)
          ((holonomicCoframeFirstJetAt configuration.coframe point).derivative
            direction)
        internalPair spacetimePair := by
      rfl

/-- Coframe-only form of the computed-`II+` chain rule.  This is the useful
mouth for native writes whose generated connection or other fields have not
yet been assigned a separate global regularity theorem: the derivative of
`B := II+(e)` depends only on the preserved smooth coframe. -/
theorem
    gravityAuxiliaryDirectionalDerivative_restrictToIIPlus_of_coframeContDiff
    (configuration : StageNineHolonomicConfiguration)
    (coframeSmooth : ContDiff ℝ ∞ configuration.coframe)
    (point : BasePoint) (direction : LorentzianIndex) :
    gravityAuxiliaryDirectionalDerivative
        (restrictHolonomicConfigurationToIIPlus configuration)
        point direction =
      physicalIIPlusCoframeTangent (configuration.coframe point)
        ((holonomicCoframeFirstJetAt configuration.coframe point).derivative
          direction) := by
  have iiPlusSmooth : ContDiff ℝ ∞ fun candidate =>
      physicalIIPlusBivector (configuration.coframe candidate) :=
    physicalIIPlusBivector_contDiff.comp coframeSmooth
  have componentSmooth :
      ∀ internal coordinate,
        ContDiff ℝ ∞ fun candidate =>
          configuration.coframe candidate internal coordinate := by
    intro internal coordinate
    exact contDiff_pi.mp (contDiff_pi.mp coframeSmooth internal) coordinate
  funext internalPair spacetimePair
  have internalPairSmooth : ContDiff ℝ ∞ fun candidate =>
      physicalIIPlusBivector (configuration.coframe candidate)
        internalPair :=
    contDiff_pi.mp iiPlusSmooth internalPair
  calc
    (gravityAuxiliaryDirectionalDerivative
        (restrictHolonomicConfigurationToIIPlus configuration)
        point direction) internalPair spacetimePair =
      (fieldDirectionalDerivative
        (fun candidate =>
          physicalIIPlusBivector (configuration.coframe candidate))
        point direction) internalPair spacetimePair := rfl
    _ =
      (fieldDirectionalDerivative
        (fun candidate =>
          physicalIIPlusBivector (configuration.coframe candidate)
            internalPair)
        point direction) spacetimePair := by
      rw [fieldDirectionalDerivative_pi_apply
        (fun candidate =>
          physicalIIPlusBivector (configuration.coframe candidate))
        iiPlusSmooth point direction internalPair]
    _ = fieldDirectionalDerivative
        (fun candidate =>
          physicalIIPlusBivector (configuration.coframe candidate)
            internalPair spacetimePair)
        point direction := by
      rw [fieldDirectionalDerivative_pi_apply
        (fun candidate =>
          physicalIIPlusBivector (configuration.coframe candidate)
            internalPair)
        internalPairSmooth point direction spacetimePair]
    _ = physicalIIPlusCoframeTangent (configuration.coframe point)
          (coframeFieldDirectionalTangent configuration.coframe point
            direction)
        internalPair spacetimePair :=
      physicalIIPlusBivector_fieldDirectionalDerivative
        configuration.coframe componentSmooth point direction internalPair
          spacetimePair
    _ = physicalIIPlusCoframeTangent (configuration.coframe point)
          ((holonomicCoframeFirstJetAt configuration.coframe point).derivative
            direction)
        internalPair spacetimePair := by
      rfl

/-- Coframe-only whole-jet seam corresponding to
`gravityAuxiliaryDirectionalDerivative_restrictToIIPlus_of_coframeContDiff`.
It avoids demanding irrelevant regularity from fields untouched by the
computed-`II+` derivative. -/
theorem holonomicGravityAuxiliaryJet_restrictToIIPlus_of_coframeContDiff
    (configuration : StageNineHolonomicConfiguration)
    (coframeSmooth : ContDiff ℝ ∞ configuration.coframe)
    (point : BasePoint) :
    holonomicGravityAuxiliaryJet
        (restrictHolonomicConfigurationToIIPlus configuration) point =
      pointwisePhysicalIIPlusJet
        (holonomicCoframeFirstJetAt configuration.coframe point) := by
  apply pointwisePhysicalBivectorJet_eq_of_fields_eq
  · rfl
  · funext direction
    exact
      gravityAuxiliaryDirectionalDerivative_restrictToIIPlus_of_coframeContDiff
        configuration coframeSmooth point direction

/-- The missing whole-field jet seam.  Both the value and all four actual
Fréchet derivative directions come from the same primitive coframe field. -/
theorem holonomicGravityAuxiliaryJet_restrictToIIPlus
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) (point : BasePoint) :
    holonomicGravityAuxiliaryJet
        (restrictHolonomicConfigurationToIIPlus configuration) point =
      pointwisePhysicalIIPlusJet
        (holonomicCoframeFirstJetAt configuration.coframe point) := by
  apply pointwisePhysicalBivectorJet_eq_of_fields_eq
  · rfl
  · funext direction
    exact gravityAuxiliaryDirectionalDerivative_restrictToIIPlus
      configuration smooth point direction

/-! ## Point-local `II+` jet transport

The source-generated radial coframe used by the living root is only required
to be differentiable at the exact compared contacts.  The following local
calculus therefore avoids strengthening a native occurrence to a global
`C∞` carrier merely to compare its already-generated first jet. -/

private theorem fieldDirectionalDerivative_pi_apply_of_differentiableAt
    {I V : Type*} [Fintype I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (field : BasePoint → I → V)
    (point : BasePoint) (direction : LorentzianIndex) (index : I)
    (fieldDifferentiableAt : DifferentiableAt ℝ field point) :
    (fieldDirectionalDerivative field point direction) index =
      fieldDirectionalDerivative (fun candidate => field candidate index)
        point direction := by
  unfold fieldDirectionalDerivative
  have derivativeEquality := fderiv_apply fieldDifferentiableAt index
  have applied := congrArg
    (fun derivative : BasePoint →L[ℝ] V =>
      derivative (coordinateDirection direction)) derivativeEquality
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply] using applied.symm

private theorem coframeWedge_differentiableAt_of_components
    (coframe : BasePoint → LorentzianCoframe)
    (point : BasePoint)
    (componentDifferentiable : ∀ internal coordinate,
      DifferentiableAt ℝ
        (fun candidate => coframe candidate internal coordinate) point)
    (internalPair spacetimePair : Fin 6) :
    DifferentiableAt ℝ
      (fun candidate => coframeWedge (coframe candidate)
        internalPair spacetimePair) point := by
  unfold coframeWedge
  exact
    ((componentDifferentiable (pairFirst internalPair)
        (pairFirst spacetimePair)).mul
      (componentDifferentiable (pairSecond internalPair)
        (pairSecond spacetimePair))).sub
    ((componentDifferentiable (pairFirst internalPair)
        (pairSecond spacetimePair)).mul
      (componentDifferentiable (pairSecond internalPair)
        (pairFirst spacetimePair)))

private theorem
    coframeWedge_fieldDirectionalDerivative_of_differentiableAt
    (coframe : BasePoint → LorentzianCoframe)
    (point : BasePoint)
    (componentDifferentiable : ∀ internal coordinate,
      DifferentiableAt ℝ
        (fun candidate => coframe candidate internal coordinate) point)
    (direction : LorentzianIndex)
    (internalPair spacetimePair : Fin 6) :
    fieldDirectionalDerivative
        (fun candidate =>
          coframeWedge (coframe candidate) internalPair spacetimePair)
        point direction =
      coframeWedgeTangent (coframe point)
          (coframeFieldDirectionalTangent coframe point direction)
        internalPair spacetimePair := by
  let firstInternal := pairFirst internalPair
  let secondInternal := pairSecond internalPair
  let firstSpacetime := pairFirst spacetimePair
  let secondSpacetime := pairSecond spacetimePair
  have firstFirst :=
    (componentDifferentiable firstInternal firstSpacetime).hasFDerivAt
  have secondSecond :=
    (componentDifferentiable secondInternal secondSpacetime).hasFDerivAt
  have firstSecond :=
    (componentDifferentiable firstInternal secondSpacetime).hasFDerivAt
  have secondFirst :=
    (componentDifferentiable secondInternal firstSpacetime).hasFDerivAt
  dsimp only [firstInternal, secondInternal, firstSpacetime,
    secondSpacetime] at firstFirst secondSecond firstSecond secondFirst
  unfold fieldDirectionalDerivative coframeWedge
    coframeWedgeTangent coframeFieldDirectionalTangent
  change
    (fderiv ℝ
        (((fun candidate =>
            coframe candidate (pairFirst internalPair)
              (pairFirst spacetimePair)) *
          fun candidate =>
            coframe candidate (pairSecond internalPair)
              (pairSecond spacetimePair)) -
        ((fun candidate =>
            coframe candidate (pairFirst internalPair)
              (pairSecond spacetimePair)) *
          fun candidate =>
            coframe candidate (pairSecond internalPair)
              (pairFirst spacetimePair)))
        point) (coordinateDirection direction) = _
  rw [((firstFirst.mul secondSecond).sub
    (firstSecond.mul secondFirst)).fderiv]
  simp [fieldDirectionalDerivative]
  ring

private theorem fieldDirectionalDerivative_neg_of_differentiableAt
    (field : BasePoint → ℝ) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ field point)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun candidate => -field candidate)
        point direction =
      -fieldDirectionalDerivative field point direction := by
  unfold fieldDirectionalDerivative
  change
    (fderiv ℝ (-field) point) (coordinateDirection direction) =
      -(fderiv ℝ field point) (coordinateDirection direction)
  rw [differentiable.hasFDerivAt.neg.fderiv]
  simp

private theorem physicalIIPlusBivector_field_differentiableAt
    (coframe : BasePoint → LorentzianCoframe)
    (point : BasePoint)
    (componentDifferentiable : ∀ internal coordinate,
      DifferentiableAt ℝ
        (fun candidate => coframe candidate internal coordinate) point) :
    DifferentiableAt ℝ
      (fun candidate => physicalIIPlusBivector (coframe candidate)) point := by
  apply differentiableAt_pi.mpr
  intro internalPair
  apply differentiableAt_pi.mpr
  intro spacetimePair
  fin_cases internalPair
  · simpa [physicalIIPlusBivector, internalBivectorDual,
      lorentzianCoframeHodge] using
      coframeWedge_differentiableAt_of_components coframe point
        componentDifferentiable 3 spacetimePair
  · simpa [physicalIIPlusBivector, internalBivectorDual,
      lorentzianCoframeHodge] using
      coframeWedge_differentiableAt_of_components coframe point
        componentDifferentiable 4 spacetimePair
  · simpa [physicalIIPlusBivector, internalBivectorDual,
      lorentzianCoframeHodge] using
      coframeWedge_differentiableAt_of_components coframe point
        componentDifferentiable 5 spacetimePair
  · simpa [physicalIIPlusBivector, internalBivectorDual,
      lorentzianCoframeHodge] using
      (coframeWedge_differentiableAt_of_components coframe point
        componentDifferentiable 0 spacetimePair).neg
  · simpa [physicalIIPlusBivector, internalBivectorDual,
      lorentzianCoframeHodge] using
      (coframeWedge_differentiableAt_of_components coframe point
        componentDifferentiable 1 spacetimePair).neg
  · simpa [physicalIIPlusBivector, internalBivectorDual,
      lorentzianCoframeHodge] using
      (coframeWedge_differentiableAt_of_components coframe point
        componentDifferentiable 2 spacetimePair).neg

private theorem
    physicalIIPlusBivector_fieldDirectionalDerivative_of_differentiableAt
    (coframe : BasePoint → LorentzianCoframe)
    (point : BasePoint)
    (componentDifferentiable : ∀ internal coordinate,
      DifferentiableAt ℝ
        (fun candidate => coframe candidate internal coordinate) point)
    (direction : LorentzianIndex)
    (internalPair spacetimePair : Fin 6) :
    fieldDirectionalDerivative
        (fun candidate =>
          physicalIIPlusBivector (coframe candidate)
            internalPair spacetimePair)
        point direction =
      physicalIIPlusCoframeTangent (coframe point)
          (coframeFieldDirectionalTangent coframe point direction)
        internalPair spacetimePair := by
  fin_cases internalPair
  · simpa [physicalIIPlusBivector, physicalIIPlusCoframeTangent,
      internalBivectorDual, lorentzianCoframeHodge] using
      coframeWedge_fieldDirectionalDerivative_of_differentiableAt
        coframe point componentDifferentiable direction 3 spacetimePair
  · simpa [physicalIIPlusBivector, physicalIIPlusCoframeTangent,
      internalBivectorDual, lorentzianCoframeHodge] using
      coframeWedge_fieldDirectionalDerivative_of_differentiableAt
        coframe point componentDifferentiable direction 4 spacetimePair
  · simpa [physicalIIPlusBivector, physicalIIPlusCoframeTangent,
      internalBivectorDual, lorentzianCoframeHodge] using
      coframeWedge_fieldDirectionalDerivative_of_differentiableAt
        coframe point componentDifferentiable direction 5 spacetimePair
  · simpa [physicalIIPlusBivector, physicalIIPlusCoframeTangent,
      internalBivectorDual, lorentzianCoframeHodge] using
      fieldDirectionalDerivative_neg_of_differentiableAt
        (fun candidate =>
          coframeWedge (coframe candidate) 0 spacetimePair)
        point
        (coframeWedge_differentiableAt_of_components coframe point
          componentDifferentiable 0 spacetimePair)
        direction |>.trans (congrArg Neg.neg
          (coframeWedge_fieldDirectionalDerivative_of_differentiableAt
            coframe point componentDifferentiable direction 0 spacetimePair))
  · simpa [physicalIIPlusBivector, physicalIIPlusCoframeTangent,
      internalBivectorDual, lorentzianCoframeHodge] using
      fieldDirectionalDerivative_neg_of_differentiableAt
        (fun candidate =>
          coframeWedge (coframe candidate) 1 spacetimePair)
        point
        (coframeWedge_differentiableAt_of_components coframe point
          componentDifferentiable 1 spacetimePair)
        direction |>.trans (congrArg Neg.neg
          (coframeWedge_fieldDirectionalDerivative_of_differentiableAt
            coframe point componentDifferentiable direction 1 spacetimePair))
  · simpa [physicalIIPlusBivector, physicalIIPlusCoframeTangent,
      internalBivectorDual, lorentzianCoframeHodge] using
      fieldDirectionalDerivative_neg_of_differentiableAt
        (fun candidate =>
          coframeWedge (coframe candidate) 2 spacetimePair)
        point
        (coframeWedge_differentiableAt_of_components coframe point
          componentDifferentiable 2 spacetimePair)
        direction |>.trans (congrArg Neg.neg
          (coframeWedge_fieldDirectionalDerivative_of_differentiableAt
            coframe point componentDifferentiable direction 2 spacetimePair))

private theorem pointwisePhysicalBivectorJet_eq_of_value_derivative_eq
    (first second : PointwisePhysicalBivectorJet)
    (value : first.value = second.value)
    (derivative : first.derivative = second.derivative) :
    first = second := by
  cases first
  cases second
  simp_all

/-- Two `II+` auxiliary fields with the same actual coframe first jet have
the same auxiliary jet at those contacts.  Only point-local differentiability
is consumed; no global smoothness, action equation, or target receipt is
introduced. -/
theorem holonomicGravityAuxiliaryJet_eq_of_iiPlus_of_coframeFirstJet_eq
    (first second : StageNineHolonomicConfiguration)
    (firstPoint secondPoint : BasePoint)
    (firstAuxiliary :
      first.gravityAuxiliary =
        fun candidate => physicalIIPlusBivector (first.coframe candidate))
    (secondAuxiliary :
      second.gravityAuxiliary =
        fun candidate => physicalIIPlusBivector (second.coframe candidate))
    (firstDifferentiable : ∀ internal coordinate,
      DifferentiableAt ℝ
        (fun candidate => first.coframe candidate internal coordinate)
        firstPoint)
    (secondDifferentiable : ∀ internal coordinate,
      DifferentiableAt ℝ
        (fun candidate => second.coframe candidate internal coordinate)
        secondPoint)
    (coframeJetEq :
      holonomicCoframeFirstJetAt first.coframe firstPoint =
        holonomicCoframeFirstJetAt second.coframe secondPoint) :
    holonomicGravityAuxiliaryJet first firstPoint =
      holonomicGravityAuxiliaryJet second secondPoint := by
  have coframeValueEq :
      first.coframe firstPoint = second.coframe secondPoint :=
    congrArg PointwiseLorentzianCoframeJet.coframe coframeJetEq
  apply pointwisePhysicalBivectorJet_eq_of_value_derivative_eq
  · change
      first.gravityAuxiliary firstPoint =
        second.gravityAuxiliary secondPoint
    rw [firstAuxiliary, secondAuxiliary]
    change
      physicalIIPlusBivector (first.coframe firstPoint) =
        physicalIIPlusBivector (second.coframe secondPoint)
    rw [coframeValueEq]
  · funext direction internalPair spacetimePair
    change
      (fieldDirectionalDerivative first.gravityAuxiliary firstPoint direction)
          internalPair spacetimePair =
        (fieldDirectionalDerivative second.gravityAuxiliary secondPoint direction)
          internalPair spacetimePair
    rw [firstAuxiliary, secondAuxiliary]
    rw [fieldDirectionalDerivative_pi_apply_of_differentiableAt
      (fun candidate => physicalIIPlusBivector (first.coframe candidate))
      firstPoint direction internalPair
      (physicalIIPlusBivector_field_differentiableAt first.coframe
        firstPoint firstDifferentiable)]
    rw [fieldDirectionalDerivative_pi_apply_of_differentiableAt
      (fun candidate =>
        physicalIIPlusBivector (first.coframe candidate) internalPair)
      firstPoint direction spacetimePair
      (differentiableAt_pi.mp
        (physicalIIPlusBivector_field_differentiableAt first.coframe
          firstPoint firstDifferentiable) internalPair)]
    rw [fieldDirectionalDerivative_pi_apply_of_differentiableAt
      (fun candidate => physicalIIPlusBivector (second.coframe candidate))
      secondPoint direction internalPair
      (physicalIIPlusBivector_field_differentiableAt second.coframe
        secondPoint secondDifferentiable)]
    rw [fieldDirectionalDerivative_pi_apply_of_differentiableAt
      (fun candidate =>
        physicalIIPlusBivector (second.coframe candidate) internalPair)
      secondPoint direction spacetimePair
      (differentiableAt_pi.mp
        (physicalIIPlusBivector_field_differentiableAt second.coframe
          secondPoint secondDifferentiable) internalPair)]
    rw [physicalIIPlusBivector_fieldDirectionalDerivative_of_differentiableAt
      first.coframe firstPoint firstDifferentiable direction internalPair
      spacetimePair]
    rw [physicalIIPlusBivector_fieldDirectionalDerivative_of_differentiableAt
      second.coframe secondPoint secondDifferentiable direction internalPair
      spacetimePair]
    have derivativeCoordinateEq := congrArg
      (fun jet => jet.derivative direction) coframeJetEq
    have tangentEq :
        coframeFieldDirectionalTangent first.coframe firstPoint direction =
          coframeFieldDirectionalTangent second.coframe secondPoint direction := by
      exact derivativeCoordinateEq
    rw [coframeValueEq, tangentEq]

@[simp] theorem restrictHolonomicConfigurationToIIPlus_gravityConnection
    (configuration : StageNineHolonomicConfiguration) :
    (restrictHolonomicConfigurationToIIPlus
      configuration).gravityConnection = configuration.gravityConnection :=
  rfl

/-- Computed `II+` restriction preserves exactly the existing Lorentz
admissibility domain because it does not replace the primitive connection. -/
theorem restrictHolonomicConfigurationToIIPlus_lorentzAdmissible_iff
    (configuration : StageNineHolonomicConfiguration) :
    GravityConnectionLorentzAdmissible
        (restrictHolonomicConfigurationToIIPlus configuration) ↔
      GravityConnectionLorentzAdmissible configuration :=
  Iff.rfl

/-- Actual KIN-1 on the same computed restricted configuration.  No second
variance raise, volume, spacetime Hodge, normalization, or convention sign is
inserted: both sides use the exact three-form carrier of the form-native
Lorentz Euler response. -/
theorem
    holonomicGravityAuxiliaryExteriorCovariantDerivative_restrictToIIPlus_eq_torsionCoframe
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (admissible : GravityConnectionLorentzAdmissible configuration)
    (point : BasePoint) :
    holonomicGravityAuxiliaryExteriorCovariantDerivative
        (restrictHolonomicConfigurationToIIPlus configuration) point =
      internalBivectorDualThreeForm
        (torsionCoframeWedgeThreeForm (configuration.coframe point)
          (pointwiseCartanTorsion
            (holonomicCoframeFirstJetAt configuration.coframe point)
            (configuration.gravityConnection point))) := by
  change
    pointwisePhysicalBivectorExteriorCovariantDerivative
        (configuration.gravityConnection point)
        (holonomicGravityAuxiliaryJet
          (restrictHolonomicConfigurationToIIPlus configuration) point) = _
  rw [holonomicGravityAuxiliaryJet_restrictToIIPlus configuration smooth point]
  exact
    pointwisePhysicalIIPlus_exteriorCovariantDerivative_eq_torsionCoframe
      (holonomicCoframeFirstJetAt configuration.coframe point)
      (configuration.gravityConnection point) (admissible point)

end

end
  SaturationMonoid.PhysicsCore.StageNineFormNativeIIPlusJetKinematics
