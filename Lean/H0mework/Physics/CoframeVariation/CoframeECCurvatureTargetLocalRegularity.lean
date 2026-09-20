import H0mework.Physics.CoframeVariation.CoframeECCurvatureNormalSection

/-!
# Local regularity of the coframe-relative EC curvature target

The coframe--EC action writer builds its curvature target from four pieces:
the live coframe, the current curvature, the live coframe-load coordinates,
and the nondegenerate coframe scale.  This module exposes that finite
coordinate dependency without unfolding a concrete action density.

These are transporter lemmas for an already generated target.  They accept
no target value, residual, branch, zero-fiber witness, or regularity receipt
for the target itself.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCoframeECCurvatureTargetLocalRegularity

open ProofFreeRicherAnholonomicSource
open StageNineCartanTangentSimplicityResponse
open StageNineDiracDualFormNativeCoframeECCurvatureNormalSection
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineFormNativeGaugeWedge
open StageNineGlobalIntegratedAction
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineTopologicalFourFormPairing

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private theorem gravityTopologicalWedgeCoefficient_contDiffAt_of_components
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞}
    (first second : E → PhysicalBivector)
    (center : E)
    (firstRegular : ∀ internalPair spacetimePair : Fin 6,
      ContDiffAt ℝ n
        (fun point => first point internalPair spacetimePair) center)
    (secondRegular : ∀ internalPair spacetimePair : Fin 6,
      ContDiffAt ℝ n
        (fun point => second point internalPair spacetimePair) center) :
    ContDiffAt ℝ n
      (fun point =>
        gravityTopologicalWedgeCoefficient
          (first point) (second point)) center := by
  unfold gravityTopologicalWedgeCoefficient
    orientedTwoFormWedgeCoefficient generatedTwoFormWedgeCoefficient
  apply ContDiffAt.sum
  intro internalPair _
  apply ContDiffAt.mul contDiffAt_const
  apply ContDiffAt.sum
  intro spacetimePair _
  exact
    (firstRegular internalPair spacetimePair).mul
      (secondRegular internalPair (twoFormComplement spacetimePair))

private theorem physicalIIPlusCoframeTangent_component_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞}
    (coframe variation : E → LorentzianCoframe)
    (center : E)
    (coframeRegular : ContDiffAt ℝ n coframe center)
    (variationRegular : ContDiffAt ℝ n variation center)
    (internalPair spacetimePair : Fin 6) :
    ContDiffAt ℝ n
      (fun point =>
        physicalIIPlusCoframeTangent
          (coframe point) (variation point) internalPair spacetimePair)
      center := by
  unfold physicalIIPlusCoframeTangent coframeWedgeTangent
    internalBivectorDual
  fin_cases internalPair <;> fin_cases spacetimePair <;>
    simp [lorentzianCoframeHodge] <;>
    fun_prop

/-- Coordinate regularity of the arbitrary-coframe EC observation follows
from regularity of the live coframe and raw curvature components. -/
theorem coframeDiracDualECCurvatureObservation_coordinate_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞}
    (coframe : E → LorentzianCoframe)
    (curvature : E → PhysicalBivector)
    (center : E)
    (coframeRegular : ContDiffAt ℝ n coframe center)
    (curvatureRegular : ContDiffAt ℝ n curvature center)
    (row column : LorentzianIndex) :
    ContDiffAt ℝ n
      (fun point =>
        coframeDiracDualECCurvatureObservation
          (coframe point) (curvature point)
          (coframeCoordinateDirection row column))
      center := by
  unfold coframeDiracDualECCurvatureObservation
  apply gravityTopologicalWedgeCoefficient_contDiffAt_of_components
    (fun point =>
      physicalIIPlusCoframeTangent
        (coframe point) (coframeCoordinateDirection row column))
    (fun point =>
      gravityInternalPairVarianceNormalization (curvature point))
    center
  · intro internalPair spacetimePair
    exact physicalIIPlusCoframeTangent_component_contDiffAt
      coframe (fun _ => coframeCoordinateDirection row column) center
      coframeRegular contDiffAt_const internalPair spacetimePair
  · intro internalPair spacetimePair
    simp only [gravityInternalPairVarianceNormalization_apply]
    exact contDiffAt_const.mul
      (contDiffAt_pi.mp
        (contDiffAt_pi.mp curvatureRegular internalPair) spacetimePair)

/-- Pulling a covector through the live coframe preserves coordinate
regularity.  The proof uses the fixed matrix-coordinate inventory rather
than unfolding the continuous-linear-map implementation. -/
theorem coframeRelativeECCovector_coordinate_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞}
    (coframe : E → LorentzianCoframe)
    (observation : E → (LorentzianCoframe →L[ℝ] ℝ))
    (center : E)
    (coframeRegular : ContDiffAt ℝ n coframe center)
    (observationRegular : ∀ row column : LorentzianIndex,
      ContDiffAt ℝ n
        (fun point =>
          observation point (coframeCoordinateDirection row column))
        center)
    (row column : LorentzianIndex) :
    ContDiffAt ℝ n
      (fun point =>
        coframeRelativeECCovector (coframe point) (observation point)
          (coframeCoordinateDirection row column))
      center := by
  rw [show
    (fun point =>
      coframeRelativeECCovector (coframe point) (observation point)
        (coframeCoordinateDirection row column)) =
      fun point =>
        ∑ middle : LorentzianIndex,
          (coframe point) column middle *
            observation point (coframeCoordinateDirection row middle) by
    funext point
    unfold coframeRelativeECCovector coframeRightMultiplication
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
      AddHom.coe_mk]
    rw [show
      coframeCoordinateDirection row column * coframe point =
        ∑ middle : LorentzianIndex,
          (coframe point) column middle •
            coframeCoordinateDirection row middle by
      ext output input
      classical
      by_cases output = row
      · subst output
        simp [coframeCoordinateDirection, Matrix.mul_apply,
          Matrix.sum_apply, Matrix.single_apply]
      · have row_ne_output : row ≠ output := Ne.symm ‹output ≠ row›
        simp [coframeCoordinateDirection, Matrix.mul_apply,
          Matrix.sum_apply, row_ne_output]]
    simp]
  apply ContDiffAt.sum
  intro middle _
  exact
    (contDiffAt_pi.mp
      (contDiffAt_pi.mp coframeRegular column) middle).mul
      (observationRegular row middle)

private theorem identityDiracDualECCurvatureNormalSection_component_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞}
    (observation : E → (LorentzianCoframe →L[ℝ] ℝ))
    (center : E)
    (observationRegular : ∀ row column : LorentzianIndex,
      ContDiffAt ℝ n
        (fun point =>
          observation point (coframeCoordinateDirection row column))
        center)
    (internalPair spacetimePair : Fin 6) :
    ContDiffAt ℝ n
      (fun point =>
        identityDiracDualECCurvatureNormalSection (observation point)
          internalPair spacetimePair)
      center := by
  unfold identityDiracDualECCurvatureNormalSection
    linearPlebanskiMultiplierOfCoframeResponse
    linearPlebanskiCoframeResponseOfStress
    linearPlebanskiTraceReverse
    coframeCovectorCoordinates coframeCoordinateDirection
    physicalIIPlusCoframeTangent coframeWedgeTangent
  fin_cases internalPair <;> fin_cases spacetimePair <;>
    simp [internalBivectorDual, lorentzianCoframeHodge,
      Matrix.one_apply, pairFirst, pairSecond, Fin.sum_univ_four] <;>
    fun_prop (disch := exact observationRegular _ _)

private theorem coframeDiracDualECCurvatureOfRelative_component_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞}
    (coframe : E → LorentzianCoframe)
    (relative : E → PhysicalBivector)
    (center : E)
    (coframeRegular : ContDiffAt ℝ n coframe center)
    (relativeRegular : ContDiffAt ℝ n relative center)
    (scaleNonzero :
      coframeTwoFormWedgeScale (coframe center).transpose ≠ 0)
    (internalPair spacetimePair : Fin 6) :
    ContDiffAt ℝ n
      (fun point =>
        coframeDiracDualECCurvatureOfRelative
          (coframe point) (relative point) internalPair spacetimePair)
      center := by
  unfold coframeDiracDualECCurvatureOfRelative
    coframeTwoFormWedgeScale
    orientedTwoFormWedgeCoefficient generatedTwoFormWedgeCoefficient
    physicalBivectorSpacetimeCoframeTwoFormLinear coframeTwoFormLinear
    coframeWedge
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply,
    smul_eq_mul, Matrix.transpose_apply,
    gravityInternalPairVarianceNormalization_apply]
  fun_prop (disch := exact scaleNonzero)

/-- Component regularity of the canonical coframe-normal section depends
only on the coframe, the covector's sixteen coordinates, and the live
nonzero wedge scale. -/
theorem coframeDiracDualECCurvatureNormalSection_component_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞}
    (coframe : E → LorentzianCoframe)
    (observation : E → (LorentzianCoframe →L[ℝ] ℝ))
    (center : E)
    (coframeRegular : ContDiffAt ℝ n coframe center)
    (observationRegular : ∀ row column : LorentzianIndex,
      ContDiffAt ℝ n
        (fun point =>
          observation point (coframeCoordinateDirection row column))
        center)
    (scaleNonzero :
      coframeTwoFormWedgeScale (coframe center).transpose ≠ 0)
    (internalPair spacetimePair : Fin 6) :
    ContDiffAt ℝ n
      (fun point =>
        coframeDiracDualECCurvatureNormalSection
          (coframe point) (observation point)
          internalPair spacetimePair)
      center := by
  unfold coframeDiracDualECCurvatureNormalSection
  apply coframeDiracDualECCurvatureOfRelative_component_contDiffAt
    coframe
    (fun point =>
      identityDiracDualECCurvatureNormalSection
        (coframeRelativeECCovector (coframe point) (observation point)))
    center coframeRegular
  · apply contDiffAt_pi'
    intro targetInternalPair
    apply contDiffAt_pi'
    intro targetSpacetimePair
    apply identityDiracDualECCurvatureNormalSection_component_contDiffAt
    intro row column
    exact coframeRelativeECCovector_coordinate_contDiffAt
      coframe observation center coframeRegular observationRegular row column
  · exact scaleNonzero

/-- The complete faithful target is locally regular once the already
generated live coframe, current curvature, and load coordinates are locally
regular. -/
theorem coframeDiracDualECCurvatureTarget_component_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞}
    (coframe : E → LorentzianCoframe)
    (current : E → PhysicalBivector)
    (observation : E → (LorentzianCoframe →L[ℝ] ℝ))
    (center : E)
    (coframeRegular : ContDiffAt ℝ n coframe center)
    (currentRegular : ContDiffAt ℝ n current center)
    (observationRegular : ∀ row column : LorentzianIndex,
      ContDiffAt ℝ n
        (fun point =>
          observation point (coframeCoordinateDirection row column))
        center)
    (scaleNonzero :
      coframeTwoFormWedgeScale (coframe center).transpose ≠ 0)
    (internalPair spacetimePair : Fin 6) :
    ContDiffAt ℝ n
      (fun point =>
        coframeDiracDualECCurvatureTarget
          (coframe point) (current point) (observation point)
          internalPair spacetimePair)
      center := by
  unfold coframeDiracDualECCurvatureTarget
    coframeDiracDualECCurvatureKernelPart
  exact
    ((contDiffAt_pi.mp
        (contDiffAt_pi.mp currentRegular internalPair) spacetimePair).sub
      (coframeDiracDualECCurvatureNormalSection_component_contDiffAt
        coframe
        (fun point =>
          coframeDiracDualECCurvatureObservation
            (coframe point) (current point))
        center coframeRegular
        (fun row column =>
          coframeDiracDualECCurvatureObservation_coordinate_contDiffAt
            coframe current center coframeRegular currentRegular row column)
        scaleNonzero internalPair spacetimePair)).add
      (coframeDiracDualECCurvatureNormalSection_component_contDiffAt
        coframe observation center coframeRegular observationRegular
        scaleNonzero internalPair spacetimePair)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCoframeECCurvatureTargetLocalRegularity
