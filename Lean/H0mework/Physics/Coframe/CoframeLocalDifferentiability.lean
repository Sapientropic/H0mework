import H0mework.Physics.Coframe.CoframeVariation

/-!
# S9-C3e1: actual local coframe differentiability and stress producer

This module differentiates the common generated local density through the
primitive coframe slot on the nondegenerate branch opened by C3e0.  Each
gravity, gauge, scalar, and exterior-matter contribution is reduced to its
actual finite-coordinate dependence on the coframe, its inverse, or the
coframe-generated Hodge operator.  No stress tensor, sector derivative, or
differentiability certificate is accepted as input.

The total local stress covector is defined only after differentiability is
proved.  Its product rule retains the volume contribution of terms such as the
scalar potential and Yukawa density even when their inner-density coframe
derivative vanishes.  This is a local Fréchet-derivative checkpoint; the
integrated derivative, weak equation, and pointwise coframe equation remain
later producer gates.
-/

namespace SaturationMonoid.PhysicsCore.StageNineCoframeLocalDifferentiability

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCoframeVariation
open SU7MotherLieAlgebra
open EmpiricalReferenceScaleCouplingBoundary
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7ExteriorBreakingYukawa
open DiracExteriorMatterAction
open DiracCliffordRepresentation
open scoped ContDiff ComplexConjugate Matrix.Norms.Elementwise

noncomputable section

set_option maxHeartbeats 1200000

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

def coframeLocalDensity
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (coframe : LorentzianCoframe) : ℝ :=
  generatedUnifiedLocalDensityAtBoundary source
    (sourceGeneratedUnifiedCouplings source) 0 point
    (withCoframe field coframe)

theorem coframeWedge_contDiff :
    ContDiff ℝ ∞ (coframeWedge : LorentzianCoframe → PhysicalBivector) := by
  apply contDiff_pi'
  intro internalPair
  apply contDiff_pi'
  intro spacetimePair
  unfold coframeWedge
  fun_prop

theorem physicalIIPlusBivector_contDiff :
    ContDiff ℝ ∞
      (physicalIIPlusBivector : LorentzianCoframe → PhysicalBivector) := by
  apply contDiff_pi'
  intro internalPair
  apply contDiff_pi'
  intro spacetimePair
  fin_cases internalPair
  · simpa [physicalIIPlusBivector, internalBivectorDual,
      lorentzianCoframeHodge] using
      (contDiff_pi.mp
        (contDiff_pi.mp coframeWedge_contDiff 3) spacetimePair)
  · simpa [physicalIIPlusBivector, internalBivectorDual,
      lorentzianCoframeHodge] using
      (contDiff_pi.mp
        (contDiff_pi.mp coframeWedge_contDiff 4) spacetimePair)
  · simpa [physicalIIPlusBivector, internalBivectorDual,
      lorentzianCoframeHodge] using
      (contDiff_pi.mp
        (contDiff_pi.mp coframeWedge_contDiff 5) spacetimePair)
  · simpa [physicalIIPlusBivector, internalBivectorDual,
      lorentzianCoframeHodge] using
      (contDiff_pi.mp
        (contDiff_pi.mp coframeWedge_contDiff 0) spacetimePair).neg
  · simpa [physicalIIPlusBivector, internalBivectorDual,
      lorentzianCoframeHodge] using
      (contDiff_pi.mp
        (contDiff_pi.mp coframeWedge_contDiff 1) spacetimePair).neg
  · simpa [physicalIIPlusBivector, internalBivectorDual,
      lorentzianCoframeHodge] using
      (contDiff_pi.mp
        (contDiff_pi.mp coframeWedge_contDiff 2) spacetimePair).neg

theorem lorentzianMetricOfCoframe_contDiff :
    ContDiff ℝ ∞
      (lorentzianMetricOfCoframe : LorentzianCoframe → LorentzianMetric) := by
  apply contDiff_pi'
  intro row
  apply contDiff_pi'
  intro column
  simp only [lorentzianMetricOfCoframe, Matrix.mul_apply,
    Matrix.transpose_apply]
  apply ContDiff.sum
  intro middle _
  apply ContDiff.mul
  · apply ContDiff.sum
    intro internal _
    exact (contDiff_pi.mp
      (contDiff_pi.mp contDiff_id internal) row).mul contDiff_const
  · exact contDiff_pi.mp (contDiff_pi.mp contDiff_id middle) column

theorem lorentzianMetric_inv_contDiffAt
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    ContDiffAt ℝ ∞
      (fun candidate : LorentzianCoframe =>
        (lorentzianMetricOfCoframe candidate)⁻¹) coframe := by
  have metricNondegenerate :
      Matrix.det (lorentzianMetricOfCoframe coframe) ≠ 0 :=
    PointwiseLorentzianCoframeJet.metric_det_ne_zero_of_coframe
      { coframe := coframe, derivative := 0 } nondegenerate
  exact (coframe_inv_contDiffAt
      (lorentzianMetricOfCoframe coframe) metricNondegenerate).comp
    coframe lorentzianMetricOfCoframe_contDiff.contDiffAt

theorem inverseCoframeDiracGamma_contDiffAt
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (direction : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun candidate : LorentzianCoframe =>
        inverseCoframeDiracGamma
          { coframe := candidate, derivative := 0 } direction) coframe := by
  apply contDiffAt_pi'
  intro row
  apply contDiffAt_pi'
  intro column
  unfold inverseCoframeDiracGamma
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply ContDiffAt.sum
  intro internal _
  have inverseEntrySmooth : ContDiffAt ℝ ∞
      (fun candidate : LorentzianCoframe =>
        candidate⁻¹ direction internal) coframe :=
    contDiffAt_pi.mp
      (contDiffAt_pi.mp
        (coframe_inv_contDiffAt coframe nondegenerate) direction) internal
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp
      coframe inverseEntrySmooth).mul contDiffAt_const

theorem coframeMatterCoordinate_sum_single
    (matter : MatterCoordinateCarrier) :
    matter = ∑ index : MatterCoordinateIndex,
      matter index • EuclideanSpace.single index (1 : ℂ) := by
  apply PiLp.ext
  intro index
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  symm
  rw [Fintype.sum_eq_single index]
  · simp
  · intro candidate candidateNe
    simp [Pi.single_eq_of_ne candidateNe.symm]

theorem coframeMatterDual_coordinate_expansion
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (matter : MatterCoordinateCarrier) :
    dual (matterCoordinateEquiv.symm matter) =
      ∑ index : MatterCoordinateIndex,
        matter index *
          dual (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ))) := by
  conv_lhs => rw [coframeMatterCoordinate_sum_single matter]
  simp only [map_sum, map_smul, smul_eq_mul]

theorem coframeDiracMatrixMatterAction_add_matrix
    (first second : DiracMatrix)
    (matter : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction (first + second) matter =
      diracMatrixMatterAction first matter +
        diracMatrixMatterAction second matter := by
  funext row
  simp [diracMatrixMatterAction, add_smul, Finset.sum_add_distrib]

theorem coframeDiracMatrixMatterAction_smul_matrix
    (parameter : ℂ) (matrix : DiracMatrix)
    (matter : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction (parameter • matrix) matter =
      parameter • diracMatrixMatterAction matrix matter := by
  funext row
  change
    (∑ column : DiracSpinorIndex,
      (parameter * matrix row column) • matter column) =
      parameter •
        ∑ column : DiracSpinorIndex, matrix row column • matter column
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro column _
  simp [smul_smul]

def coframeDiracMatrixMatterCoordinateBilinear :
    DiracMatrix →ₗ[ℂ]
      MatterCoordinateCarrier →ₗ[ℂ] MatterCoordinateCarrier where
  toFun matrix :=
    { toFun := fun matter =>
        matterCoordinateEquiv
          (diracMatrixMatterAction matrix
            (matterCoordinateEquiv.symm matter))
      map_add' := by
        intro first second
        simp only [map_add]
      map_smul' := by
        intro parameter matter
        simp only [map_smul, RingHom.id_apply] }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro matter
    change
      matterCoordinateEquiv
          (diracMatrixMatterAction (first + second)
            (matterCoordinateEquiv.symm matter)) =
        matterCoordinateEquiv
            (diracMatrixMatterAction first
              (matterCoordinateEquiv.symm matter)) +
          matterCoordinateEquiv
            (diracMatrixMatterAction second
              (matterCoordinateEquiv.symm matter))
    rw [coframeDiracMatrixMatterAction_add_matrix, map_add]
  map_smul' := by
    intro parameter matrix
    apply LinearMap.ext
    intro matter
    change
      matterCoordinateEquiv
          (diracMatrixMatterAction (parameter • matrix)
            (matterCoordinateEquiv.symm matter)) =
        parameter •
          matterCoordinateEquiv
            (diracMatrixMatterAction matrix
              (matterCoordinateEquiv.symm matter))
    rw [coframeDiracMatrixMatterAction_smul_matrix, map_smul]

theorem coframeTwoFormLinear_apply_contDiff
    (form : StageNineBlockwiseConstitutive.GaugeTwoForm)
    (output : Fin 6) :
    ContDiff ℝ ∞ (fun coframe : LorentzianCoframe =>
      coframeTwoFormLinear coframe form output) := by
  change ContDiff ℝ ∞ (fun coframe : LorentzianCoframe =>
    ∑ input : Fin 6,
      coframeWedge coframe output input * form input)
  apply ContDiff.sum
  intro input _
  exact (contDiff_pi.mp
      (contDiff_pi.mp coframeWedge_contDiff output) input).mul
    contDiff_const

theorem coframeGaugeSpacetimeHodgeLinear_apply_contDiffAt
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (form : StageNineBlockwiseConstitutive.GaugeTwoForm)
    (output : Fin 6) :
    ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
      coframeGaugeSpacetimeHodgeLinear candidate form output) coframe := by
  have inverseWedgeSmooth : ContDiffAt ℝ ∞
      (fun candidate : LorentzianCoframe => coframeWedge candidate⁻¹)
      coframe :=
    coframeWedge_contDiff.contDiffAt.comp coframe
      (coframe_inv_contDiffAt coframe nondegenerate)
  change ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
    ∑ input : Fin 6,
      coframeWedge candidate⁻¹ output input *
        lorentzianCoframeHodge
          (fun internalPair =>
            ∑ spacetimePair : Fin 6,
              coframeWedge candidate internalPair spacetimePair *
                form spacetimePair)
          input) coframe
  apply ContDiffAt.sum
  intro input _
  apply ContDiffAt.mul
  · exact contDiffAt_pi.mp
      (contDiffAt_pi.mp inverseWedgeSmooth output) input
  · fin_cases input
    · change ContDiffAt ℝ ∞
        (fun candidate => coframeTwoFormLinear candidate form 3) coframe
      exact (coframeTwoFormLinear_apply_contDiff form 3).contDiffAt
    · change ContDiffAt ℝ ∞
        (fun candidate => coframeTwoFormLinear candidate form 4) coframe
      exact (coframeTwoFormLinear_apply_contDiff form 4).contDiffAt
    · change ContDiffAt ℝ ∞
        (fun candidate => coframeTwoFormLinear candidate form 5) coframe
      exact (coframeTwoFormLinear_apply_contDiff form 5).contDiffAt
    · change ContDiffAt ℝ ∞
        (fun candidate => -coframeTwoFormLinear candidate form 0) coframe
      exact (coframeTwoFormLinear_apply_contDiff form 0).neg.contDiffAt
    · change ContDiffAt ℝ ∞
        (fun candidate => -coframeTwoFormLinear candidate form 1) coframe
      exact (coframeTwoFormLinear_apply_contDiff form 1).neg.contDiffAt
    · change ContDiffAt ℝ ∞
        (fun candidate => -coframeTwoFormLinear candidate form 2) coframe
      exact (coframeTwoFormLinear_apply_contDiff form 2).neg.contDiffAt

theorem coframeTwoFormLinear_apply_contDiffAt_of
    (coframe : LorentzianCoframe)
    (form : LorentzianCoframe →
      StageNineBlockwiseConstitutive.GaugeTwoForm)
    (formSmooth : ∀ input : Fin 6, ContDiffAt ℝ ∞
      (fun candidate => form candidate input) coframe)
    (output : Fin 6) :
    ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
      coframeTwoFormLinear candidate (form candidate) output) coframe := by
  change ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
    ∑ input : Fin 6,
      coframeWedge candidate output input * form candidate input) coframe
  apply ContDiffAt.sum
  intro input _
  exact (contDiff_pi.mp
      (contDiff_pi.mp coframeWedge_contDiff output) input).contDiffAt.mul
    (formSmooth input)

theorem coframeTwoFormMetricPairing_contDiffAt_of
    (coframe : LorentzianCoframe)
    (first second : LorentzianCoframe →
      StageNineBlockwiseConstitutive.GaugeTwoForm)
    (firstSmooth : ∀ input : Fin 6, ContDiffAt ℝ ∞
      (fun candidate => first candidate input) coframe)
    (secondSmooth : ∀ input : Fin 6, ContDiffAt ℝ ∞
      (fun candidate => second candidate input) coframe) :
    ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
      coframeTwoFormMetricPairing candidate
        (first candidate) (second candidate)) coframe := by
  change ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
    ∑ pair : Fin 6,
      lorentzianTwoFormSign pair *
        coframeTwoFormLinear candidate (first candidate) pair *
        coframeTwoFormLinear candidate (second candidate) pair) coframe
  apply ContDiffAt.sum
  intro pair _
  exact (contDiffAt_const.mul
      (coframeTwoFormLinear_apply_contDiffAt_of
        coframe first firstSmooth pair)).mul
    (coframeTwoFormLinear_apply_contDiffAt_of
      coframe second secondSmooth pair)

theorem gravityCoframePairing_contDiffAt_of
    (coframe : LorentzianCoframe)
    (first second : LorentzianCoframe → PhysicalBivector)
    (firstSmooth : ∀ internal spacetime : Fin 6, ContDiffAt ℝ ∞
      (fun candidate => first candidate internal spacetime) coframe)
    (secondSmooth : ∀ internal spacetime : Fin 6, ContDiffAt ℝ ∞
      (fun candidate => second candidate internal spacetime) coframe) :
    ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
      gravityCoframePairing candidate
        (first candidate) (second candidate)) coframe := by
  unfold gravityCoframePairing
  apply ContDiffAt.sum
  intro internal _
  exact contDiffAt_const.mul
    (coframeTwoFormMetricPairing_contDiffAt_of coframe
      (fun candidate => first candidate internal)
      (fun candidate => second candidate internal)
      (firstSmooth internal) (secondSmooth internal))

theorem gravitySpacetimeHodge_component_contDiffAt
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (bivector : PhysicalBivector)
    (internal spacetime : Fin 6) :
    ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
      gravitySpacetimeHodge candidate bivector internal spacetime) coframe := by
  exact coframeGaugeSpacetimeHodgeLinear_apply_contDiffAt
    coframe nondegenerate (bivector internal) spacetime

theorem generatedGravityBFDensity_withCoframe_contDiffAt
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
      generatedGravityBFDensity (withCoframe field candidate))
      field.coframe := by
  change ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
    gravityCoframePairing candidate field.gravityAuxiliary
        (gravitySpacetimeHodge candidate field.gravityCurvature) -
      (1 / 2 : ℝ) *
        gravityCoframePairing candidate field.gravityAuxiliary
          (gravitySpacetimeHodge candidate
            (StageNineBlockwiseConstitutive.gravityInternalDualEquiv
              field.gravityAuxiliary)))
    field.coframe
  apply ContDiffAt.sub
  · exact gravityCoframePairing_contDiffAt_of field.coframe
      (fun _ => field.gravityAuxiliary)
      (fun candidate =>
        gravitySpacetimeHodge candidate field.gravityCurvature)
      (fun _ _ => contDiffAt_const)
      (fun internal spacetime =>
        gravitySpacetimeHodge_component_contDiffAt field.coframe
          nondegenerate field.gravityCurvature internal spacetime)
  · exact contDiffAt_const.mul
      (gravityCoframePairing_contDiffAt_of field.coframe
        (fun _ => field.gravityAuxiliary)
        (fun candidate => gravitySpacetimeHodge candidate
          (StageNineBlockwiseConstitutive.gravityInternalDualEquiv
            field.gravityAuxiliary))
        (fun _ _ => contDiffAt_const)
        (fun internal spacetime =>
          gravitySpacetimeHodge_component_contDiffAt field.coframe
            nondegenerate
            (StageNineBlockwiseConstitutive.gravityInternalDualEquiv
              field.gravityAuxiliary)
            internal spacetime))

theorem generatedGravitySimplicityDensity_withCoframe_contDiff
    (field : StageNineContinuumPointField) :
    ContDiff ℝ ∞ (fun candidate : LorentzianCoframe =>
      generatedGravitySimplicityDensity
        (withCoframe field candidate)) := by
  unfold generatedGravitySimplicityDensity
  unfold gravitySimplicityMultiplierPairing
  apply ContDiff.sum
  intro internal _
  apply ContDiff.sum
  intro spacetime _
  have residualSmooth : ContDiff ℝ ∞ (fun candidate : LorentzianCoframe =>
      field.gravityAuxiliary internal spacetime -
        physicalIIPlusBivector candidate internal spacetime) := by
    exact contDiff_const.sub
      (contDiff_pi.mp (contDiff_pi.mp
        physicalIIPlusBivector_contDiff
        internal) spacetime)
  exact contDiff_const.mul (residualSmooth.pow 2)

theorem generatedScalarKineticDensity_withCoframe_contDiffAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
      generatedScalarKineticDensity source 0 point
        (withCoframe field candidate)) field.coframe := by
  have metricInverseSmooth :=
    lorentzianMetric_inv_contDiffAt field.coframe nondegenerate
  change ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
    (1 / 2 : ℝ) *
      ∑ first : LorentzianIndex,
        ∑ second : LorentzianIndex,
          (lorentzianMetricOfCoframe candidate)⁻¹ first second *
            scalarCoordinatePairingRe
              (scalarFrameRelativeCovariantDerivative source 0 point
                field.scalarCovariantDerivative first)
              (scalarFrameRelativeCovariantDerivative source 0 point
                field.scalarCovariantDerivative second)) field.coframe
  apply ContDiffAt.mul contDiffAt_const
  apply ContDiffAt.sum
  intro first _
  apply ContDiffAt.sum
  intro second _
  exact (contDiffAt_pi.mp
      (contDiffAt_pi.mp metricInverseSmooth first) second).mul
    contDiffAt_const

theorem generatedContinuumMatterVector_withCoframe_coordinate_contDiffAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞
      (fun candidate : LorentzianCoframe =>
        matterCoordinateEquiv
          (generatedContinuumMatterVector source 0 point
            (withCoframe field candidate))) field.coframe := by
  have kineticDirectionSmooth : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ ∞
        (fun candidate : LorentzianCoframe =>
          matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := candidate, derivative := 0 } direction)
              (matterDerivativeFrameRelative source 0 point
                field.matterCovariantDerivative direction))) field.coframe := by
    intro direction
    let derivativeCoordinates : MatterCoordinateCarrier :=
      matterCoordinateEquiv
        (matterDerivativeFrameRelative source 0 point
          field.matterCovariantDerivative direction)
    let actionLinear : DiracMatrix →L[ℝ] MatterCoordinateCarrier :=
      ((LinearMap.flip coframeDiracMatrixMatterCoordinateBilinear)
        derivativeCoordinates).toContinuousLinearMap.restrictScalars ℝ
    have actionSmooth : ContDiffAt ℝ ∞
        (fun candidate : LorentzianCoframe =>
          matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := candidate, derivative := 0 } direction)
              (matterCoordinateEquiv.symm derivativeCoordinates)))
        field.coframe := by
      change ContDiffAt ℝ ∞
        (fun candidate : LorentzianCoframe =>
          actionLinear
            (inverseCoframeDiracGamma
              { coframe := candidate, derivative := 0 } direction)) field.coframe
      exact actionLinear.contDiff.contDiffAt.comp field.coframe
        (inverseCoframeDiracGamma_contDiffAt field.coframe
          nondegenerate direction)
    simpa only [derivativeCoordinates,
      matterCoordinateEquiv.symm_apply_apply] using actionSmooth
  have kineticSmooth : ContDiffAt ℝ ∞
      (fun candidate : LorentzianCoframe =>
        Complex.I •
          ∑ direction : LorentzianIndex,
            matterCoordinateEquiv
              (diracMatrixMatterAction
                (inverseCoframeDiracGamma
                  { coframe := candidate, derivative := 0 } direction)
                (matterDerivativeFrameRelative source 0 point
                  field.matterCovariantDerivative direction))) field.coframe := by
    exact
      (contDiffAt_const : ContDiffAt ℝ ∞
        (fun _ : LorentzianCoframe => (Complex.I : ℂ)) field.coframe).smul
        (ContDiffAt.sum fun direction _ => kineticDirectionSmooth direction)
  have yukawaSmooth : ContDiffAt ℝ ∞
      (fun _ : LorentzianCoframe =>
        matterCoordinateEquiv
          (chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm
              (scalarFrameRelativeCoordinates source 0 point field.scalar))
            (matterFrameRelative source 0 point field.matter))) field.coframe :=
    contDiffAt_const
  unfold generatedContinuumMatterVector
  simp only [withCoframe, map_add, map_smul, map_sum]
  exact kineticSmooth.add yukawaSmooth

theorem generatedContinuumMatterDensity_withCoframe_contDiffAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞
      (fun candidate : LorentzianCoframe =>
        generatedContinuumMatterDensity source 0 point
          (withCoframe field candidate)) field.coframe := by
  let vector := fun candidate : LorentzianCoframe =>
    generatedContinuumMatterVector source 0 point
      (withCoframe field candidate)
  let dual : Module.Dual ℂ DiracExteriorMatterCarrier :=
    matterDualFrameRelative source 0 point field.conjugateMatter
  have vectorCoordinateSmooth : ContDiffAt ℝ ∞
      (fun candidate : LorentzianCoframe =>
        matterCoordinateEquiv (vector candidate)) field.coframe :=
    generatedContinuumMatterVector_withCoframe_coordinate_contDiffAt
      source point field nondegenerate
  have pairingSumSmooth : ContDiffAt ℝ ∞
      (fun candidate : LorentzianCoframe =>
        ∑ index : MatterCoordinateIndex,
          matterCoordinateEquiv (vector candidate) index *
            dual (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ)))) field.coframe := by
    apply ContDiffAt.sum
    intro index _
    let coordinateLinear : MatterCoordinateCarrier →L[ℝ] ℂ :=
      (PiLp.projₗ (𝕜 := ℂ) 2
        (fun _ : MatterCoordinateIndex => ℂ) index)
        |>.toContinuousLinearMap |>.restrictScalars ℝ
    have coordinateSmooth : ContDiffAt ℝ ∞
        (fun candidate : LorentzianCoframe =>
          matterCoordinateEquiv (vector candidate) index) field.coframe :=
      coordinateLinear.contDiff.contDiffAt.comp field.coframe
        vectorCoordinateSmooth
    exact coordinateSmooth.mul contDiffAt_const
  have dualPairingSmooth : ContDiffAt ℝ ∞
      (fun candidate : LorentzianCoframe => dual (vector candidate))
        field.coframe := by
    rw [show (fun candidate : LorentzianCoframe => dual (vector candidate)) =
        fun candidate => ∑ index : MatterCoordinateIndex,
          matterCoordinateEquiv (vector candidate) index *
            dual (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) by
      funext candidate
      simpa only [matterCoordinateEquiv.symm_apply_apply] using
        coframeMatterDual_coordinate_expansion dual
          (matterCoordinateEquiv (vector candidate))]
    exact pairingSumSmooth
  have realPairingSmooth : ContDiffAt ℝ ∞
      (fun candidate : LorentzianCoframe =>
        (dual (vector candidate)).re) field.coframe :=
    Complex.reCLM.contDiff.contDiffAt.comp field.coframe dualPairingSmooth
  simpa only [generatedContinuumMatterDensity, withCoframe, vector, dual] using
    realPairingSmooth

theorem coframeGaugeOperatorCoefficient_contDiff
    (output input : Fin 6) :
    ContDiff ℝ ∞ (fun candidate : LorentzianCoframe =>
      gaugeOperatorCoefficient (coframeTwoFormLinear candidate)
        output input) := by
  unfold gaugeOperatorCoefficient
  exact coframeTwoFormLinear_apply_contDiff
    (fun candidate => if candidate = input then 1 else 0) output

theorem coframeHodgeOperatorCoefficient_contDiffAt
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (output input : Fin 6) :
    ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
      gaugeOperatorCoefficient
        (coframeGaugeSpacetimeHodgeLinear candidate) output input) coframe := by
  unfold gaugeOperatorCoefficient
  exact coframeGaugeSpacetimeHodgeLinear_apply_contDiffAt
    coframe nondegenerate
    (fun candidate => if candidate = input then 1 else 0) output

theorem scaledCoframeHodgeOperatorCoefficient_contDiffAt
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (coupling : ℝ) (output input : Fin 6) :
    ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
      gaugeOperatorCoefficient
        (coupling • coframeGaugeSpacetimeHodgeLinear candidate)
        output input) coframe := by
  change ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
    coupling * gaugeOperatorCoefficient
      (coframeGaugeSpacetimeHodgeLinear candidate) output input) coframe
  exact contDiffAt_const.mul
    (coframeHodgeOperatorCoefficient_contDiffAt
      coframe nondegenerate output input)

theorem coframeSpecialUnitaryLiePairing_add_left
    {n : Type*} [Fintype n] [DecidableEq n]
    (first second residual : SpecialUnitaryLieMatrix n) :
    specialUnitaryLiePairing (first + second) residual =
      specialUnitaryLiePairing first residual +
        specialUnitaryLiePairing second residual := by
  simp [specialUnitaryLiePairing, Matrix.add_mul, Matrix.trace_add]
  ring

theorem coframeSpecialUnitaryLiePairing_add_right
    {n : Type*} [Fintype n] [DecidableEq n]
    (first second residual : SpecialUnitaryLieMatrix n) :
    specialUnitaryLiePairing residual (first + second) =
      specialUnitaryLiePairing residual first +
        specialUnitaryLiePairing residual second := by
  simp [specialUnitaryLiePairing, Matrix.mul_add, Matrix.trace_add]
  ring

theorem coframeSpecialUnitaryLiePairing_smul_left
    {n : Type*} [Fintype n] [DecidableEq n]
    (parameter : ℝ) (first residual : SpecialUnitaryLieMatrix n) :
    specialUnitaryLiePairing (parameter • first) residual =
      parameter * specialUnitaryLiePairing first residual := by
  simp [specialUnitaryLiePairing, Matrix.trace_smul]

theorem coframeSpecialUnitaryLiePairing_smul_right
    {n : Type*} [Fintype n] [DecidableEq n]
    (parameter : ℝ) (first residual : SpecialUnitaryLieMatrix n) :
    specialUnitaryLiePairing residual (parameter • first) =
      parameter * specialUnitaryLiePairing residual first := by
  simp [specialUnitaryLiePairing, Matrix.trace_smul]

theorem coframeHyperchargeLiePairing_add_left
    (first second residual : HyperchargeLieScalar) :
    hyperchargeLiePairing (first + second) residual =
      hyperchargeLiePairing first residual +
        hyperchargeLiePairing second residual := by
  simp [hyperchargeLiePairing]
  ring

theorem coframeHyperchargeLiePairing_add_right
    (first second residual : HyperchargeLieScalar) :
    hyperchargeLiePairing residual (first + second) =
      hyperchargeLiePairing residual first +
        hyperchargeLiePairing residual second := by
  simp [hyperchargeLiePairing]
  ring

theorem coframeHyperchargeLiePairing_smul_left
    (parameter : ℝ) (first residual : HyperchargeLieScalar) :
    hyperchargeLiePairing (parameter • first) residual =
      parameter * hyperchargeLiePairing first residual := by
  simp [hyperchargeLiePairing]
  ring

theorem coframeHyperchargeLiePairing_smul_right
    (parameter : ℝ) (first residual : HyperchargeLieScalar) :
    hyperchargeLiePairing residual (parameter • first) =
      parameter * hyperchargeLiePairing residual first := by
  simp [hyperchargeLiePairing]
  ring

theorem specialUnitaryLiePairing_sum_left
    {n : Type*} [Fintype n] [DecidableEq n]
    {ι : Type*} [Fintype ι]
    (first : ι → SpecialUnitaryLieMatrix n)
    (second : SpecialUnitaryLieMatrix n) :
    specialUnitaryLiePairing (∑ index, first index) second =
      ∑ index, specialUnitaryLiePairing (first index) second := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [specialUnitaryLiePairing]
  | @insert index indices fresh induction =>
      rw [Finset.sum_insert fresh, Finset.sum_insert fresh,
        coframeSpecialUnitaryLiePairing_add_left, induction]

theorem specialUnitaryLiePairing_sum_right
    {n : Type*} [Fintype n] [DecidableEq n]
    {ι : Type*} [Fintype ι]
    (first : SpecialUnitaryLieMatrix n)
    (second : ι → SpecialUnitaryLieMatrix n) :
    specialUnitaryLiePairing first (∑ index, second index) =
      ∑ index, specialUnitaryLiePairing first (second index) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [specialUnitaryLiePairing]
  | @insert index indices fresh induction =>
      rw [Finset.sum_insert fresh, Finset.sum_insert fresh,
        coframeSpecialUnitaryLiePairing_add_right, induction]

theorem hyperchargeLiePairing_sum_left
    {ι : Type*} [Fintype ι]
    (first : ι → HyperchargeLieScalar)
    (second : HyperchargeLieScalar) :
    hyperchargeLiePairing (∑ index, first index) second =
      ∑ index, hyperchargeLiePairing (first index) second := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [hyperchargeLiePairing]
  | @insert index indices fresh induction =>
      rw [Finset.sum_insert fresh, Finset.sum_insert fresh,
        coframeHyperchargeLiePairing_add_left, induction]

theorem hyperchargeLiePairing_sum_right
    {ι : Type*} [Fintype ι]
    (first : HyperchargeLieScalar)
    (second : ι → HyperchargeLieScalar) :
    hyperchargeLiePairing first (∑ index, second index) =
      ∑ index, hyperchargeLiePairing first (second index) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [hyperchargeLiePairing]
  | @insert index indices fresh induction =>
      rw [Finset.sum_insert fresh, Finset.sum_insert fresh,
        coframeHyperchargeLiePairing_add_right, induction]

attribute [fun_prop] coframeGaugeOperatorCoefficient_contDiff
  coframeHodgeOperatorCoefficient_contDiffAt
  scaledCoframeHodgeOperatorCoefficient_contDiffAt

theorem specialUnitaryGaugeCurvaturePairing_contDiffAt
    {n : Type*} [Fintype n] [DecidableEq n]
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (curvature auxiliary : Fin 6 → SpecialUnitaryLieMatrix n) :
    ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
      generatedGaugeTwoFormMetricPairing
        (@specialUnitaryLiePairing n _ _) candidate auxiliary
        (liftGaugeTwoFormOperator
          (coframeGaugeSpacetimeHodgeLinear candidate) curvature)) coframe := by
  unfold generatedGaugeTwoFormMetricPairing liftGaugeTwoFormOperator
  simp_rw [specialUnitaryLiePairing_sum_left,
    specialUnitaryLiePairing_sum_right,
    coframeSpecialUnitaryLiePairing_smul_left,
    coframeSpecialUnitaryLiePairing_smul_right]
  simp_rw [specialUnitaryLiePairing_sum_right,
    coframeSpecialUnitaryLiePairing_smul_right]
  apply ContDiffAt.sum
  intro pair _
  apply ContDiffAt.mul contDiffAt_const
  apply ContDiffAt.sum
  intro auxiliaryInput _
  apply ContDiffAt.sum
  intro hodgeOutput _
  exact (coframeGaugeOperatorCoefficient_contDiff
      pair auxiliaryInput).contDiffAt.mul
    ((coframeGaugeOperatorCoefficient_contDiff
      pair hodgeOutput).contDiffAt.mul (by
        apply ContDiffAt.sum
        intro curvatureInput _
        exact (coframeHodgeOperatorCoefficient_contDiffAt
          coframe nondegenerate hodgeOutput curvatureInput).mul
            contDiffAt_const))

theorem specialUnitaryGaugeConstitutivePairing_contDiffAt
    {n : Type*} [Fintype n] [DecidableEq n]
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (coupling : ℝ)
    (auxiliary : Fin 6 → SpecialUnitaryLieMatrix n) :
    ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
      generatedGaugeTwoFormMetricPairing
        (@specialUnitaryLiePairing n _ _) candidate auxiliary
        (liftGaugeTwoFormOperator
          (coframeGaugeSpacetimeHodgeLinear candidate)
          (liftGaugeTwoFormOperator
            (coupling • coframeGaugeSpacetimeHodgeLinear candidate)
            auxiliary))) coframe := by
  unfold generatedGaugeTwoFormMetricPairing liftGaugeTwoFormOperator
  simp_rw [specialUnitaryLiePairing_sum_left,
    specialUnitaryLiePairing_sum_right,
    coframeSpecialUnitaryLiePairing_smul_left,
    coframeSpecialUnitaryLiePairing_smul_right]
  simp_rw [specialUnitaryLiePairing_sum_right,
    coframeSpecialUnitaryLiePairing_smul_right]
  simp_rw [specialUnitaryLiePairing_sum_right,
    coframeSpecialUnitaryLiePairing_smul_right]
  apply ContDiffAt.sum
  intro pair _
  apply ContDiffAt.mul contDiffAt_const
  apply ContDiffAt.sum
  intro firstAuxiliaryInput _
  apply ContDiffAt.sum
  intro coframeOutput _
  exact (coframeGaugeOperatorCoefficient_contDiff
      pair firstAuxiliaryInput).contDiffAt.mul
    ((coframeGaugeOperatorCoefficient_contDiff
      pair coframeOutput).contDiffAt.mul (by
        apply ContDiffAt.sum
        intro hodgeOutput _
        exact (coframeHodgeOperatorCoefficient_contDiffAt
            coframe nondegenerate coframeOutput hodgeOutput).mul (by
          apply ContDiffAt.sum
          intro secondAuxiliaryInput _
          exact (scaledCoframeHodgeOperatorCoefficient_contDiffAt
              coframe nondegenerate coupling hodgeOutput
                secondAuxiliaryInput).mul contDiffAt_const)))

theorem generatedSpecialUnitaryGaugeSectorBFDensity_contDiffAt
    {n : Type*} [Fintype n] [DecidableEq n]
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (coupling : ℝ)
    (curvature auxiliary : Fin 6 → SpecialUnitaryLieMatrix n) :
    ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
      generatedGaugeSectorBFDensity
        (@specialUnitaryLiePairing n _ _) candidate
        (coframeGaugeSpacetimeHodgeLinear candidate)
        (coupling • coframeGaugeSpacetimeHodgeLinear candidate)
        curvature auxiliary) coframe := by
  unfold generatedGaugeSectorBFDensity
  exact (specialUnitaryGaugeCurvaturePairing_contDiffAt
      coframe nondegenerate curvature auxiliary).sub
    (contDiffAt_const.mul
      (specialUnitaryGaugeConstitutivePairing_contDiffAt
        coframe nondegenerate coupling auxiliary))

theorem generatedStrongGaugeSector_withCoframe_contDiffAt
    (boundary : EmpiricalReferenceScaleCouplings)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
      generatedGaugeSectorBFDensity
        (@specialUnitaryLiePairing (Fin 3) _ _) candidate
        (coframeGaugeSpacetimeHodgeLinear candidate)
        ((boundary.strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear candidate)
        (fun pair => (field.gaugeCurvature pair).1)
        (fun pair => (field.gaugeAuxiliary pair).1)) field.coframe :=
  generatedSpecialUnitaryGaugeSectorBFDensity_contDiffAt
    field.coframe nondegenerate
      (boundary.strongCouplingSquared : ℝ)
      (fun pair => (field.gaugeCurvature pair).1)
      (fun pair => (field.gaugeAuxiliary pair).1)

theorem generatedWeakGaugeSector_withCoframe_contDiffAt
    (boundary : EmpiricalReferenceScaleCouplings)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
      generatedGaugeSectorBFDensity
        (@specialUnitaryLiePairing (Fin 2) _ _) candidate
        (coframeGaugeSpacetimeHodgeLinear candidate)
        ((boundary.weakCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear candidate)
        (fun pair => (field.gaugeCurvature pair).2.1)
        (fun pair => (field.gaugeAuxiliary pair).2.1)) field.coframe :=
  generatedSpecialUnitaryGaugeSectorBFDensity_contDiffAt
    field.coframe nondegenerate
      (boundary.weakCouplingSquared : ℝ)
      (fun pair => (field.gaugeCurvature pair).2.1)
      (fun pair => (field.gaugeAuxiliary pair).2.1)

theorem hyperchargeGaugeCurvaturePairing_contDiffAt
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (curvature auxiliary : Fin 6 → HyperchargeLieScalar) :
    ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
      generatedGaugeTwoFormMetricPairing hyperchargeLiePairing candidate
        auxiliary
        (liftGaugeTwoFormOperator
          (coframeGaugeSpacetimeHodgeLinear candidate) curvature)) coframe := by
  unfold generatedGaugeTwoFormMetricPairing liftGaugeTwoFormOperator
  simp_rw [hyperchargeLiePairing_sum_left,
    hyperchargeLiePairing_sum_right,
    coframeHyperchargeLiePairing_smul_left,
    coframeHyperchargeLiePairing_smul_right]
  simp_rw [hyperchargeLiePairing_sum_right,
    coframeHyperchargeLiePairing_smul_right]
  apply ContDiffAt.sum
  intro pair _
  apply ContDiffAt.mul contDiffAt_const
  apply ContDiffAt.sum
  intro auxiliaryInput _
  apply ContDiffAt.sum
  intro hodgeOutput _
  exact (coframeGaugeOperatorCoefficient_contDiff
      pair auxiliaryInput).contDiffAt.mul
    ((coframeGaugeOperatorCoefficient_contDiff
      pair hodgeOutput).contDiffAt.mul (by
        apply ContDiffAt.sum
        intro curvatureInput _
        exact (coframeHodgeOperatorCoefficient_contDiffAt
          coframe nondegenerate hodgeOutput curvatureInput).mul
            contDiffAt_const))

theorem hyperchargeGaugeConstitutivePairing_contDiffAt
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (coupling : ℝ)
    (auxiliary : Fin 6 → HyperchargeLieScalar) :
    ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
      generatedGaugeTwoFormMetricPairing hyperchargeLiePairing candidate
        auxiliary
        (liftGaugeTwoFormOperator
          (coframeGaugeSpacetimeHodgeLinear candidate)
          (liftGaugeTwoFormOperator
            (coupling • coframeGaugeSpacetimeHodgeLinear candidate)
            auxiliary))) coframe := by
  unfold generatedGaugeTwoFormMetricPairing liftGaugeTwoFormOperator
  simp_rw [hyperchargeLiePairing_sum_left,
    hyperchargeLiePairing_sum_right,
    coframeHyperchargeLiePairing_smul_left,
    coframeHyperchargeLiePairing_smul_right]
  simp_rw [hyperchargeLiePairing_sum_right,
    coframeHyperchargeLiePairing_smul_right]
  simp_rw [hyperchargeLiePairing_sum_right,
    coframeHyperchargeLiePairing_smul_right]
  apply ContDiffAt.sum
  intro pair _
  apply ContDiffAt.mul contDiffAt_const
  apply ContDiffAt.sum
  intro firstAuxiliaryInput _
  apply ContDiffAt.sum
  intro coframeOutput _
  exact (coframeGaugeOperatorCoefficient_contDiff
      pair firstAuxiliaryInput).contDiffAt.mul
    ((coframeGaugeOperatorCoefficient_contDiff
      pair coframeOutput).contDiffAt.mul (by
        apply ContDiffAt.sum
        intro hodgeOutput _
        exact (coframeHodgeOperatorCoefficient_contDiffAt
            coframe nondegenerate coframeOutput hodgeOutput).mul (by
          apply ContDiffAt.sum
          intro secondAuxiliaryInput _
          exact (scaledCoframeHodgeOperatorCoefficient_contDiffAt
              coframe nondegenerate coupling hodgeOutput
                secondAuxiliaryInput).mul contDiffAt_const)))

theorem generatedHyperchargeGaugeSectorBFDensity_contDiffAt
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (coupling : ℝ)
    (curvature auxiliary : Fin 6 → HyperchargeLieScalar) :
    ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
      generatedGaugeSectorBFDensity hyperchargeLiePairing candidate
        (coframeGaugeSpacetimeHodgeLinear candidate)
        (coupling • coframeGaugeSpacetimeHodgeLinear candidate)
        curvature auxiliary) coframe := by
  unfold generatedGaugeSectorBFDensity
  exact (hyperchargeGaugeCurvaturePairing_contDiffAt
      coframe nondegenerate curvature auxiliary).sub
    (contDiffAt_const.mul
      (hyperchargeGaugeConstitutivePairing_contDiffAt
        coframe nondegenerate coupling auxiliary))

theorem generatedHyperchargeGaugeSector_withCoframe_contDiffAt
    (boundary : EmpiricalReferenceScaleCouplings)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
      generatedGaugeSectorBFDensity hyperchargeLiePairing candidate
        (coframeGaugeSpacetimeHodgeLinear candidate)
        ((boundary.hyperchargeCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear candidate)
        (fun pair => (field.gaugeCurvature pair).2.2)
        (fun pair => (field.gaugeAuxiliary pair).2.2)) field.coframe :=
  generatedHyperchargeGaugeSectorBFDensity_contDiffAt
    field.coframe nondegenerate
      (boundary.hyperchargeCouplingSquared : ℝ)
      (fun pair => (field.gaugeCurvature pair).2.2)
      (fun pair => (field.gaugeAuxiliary pair).2.2)

theorem generatedVolumeDensity_withCoframe_contDiffAt
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
      generatedVolumeDensity (withCoframe field candidate)) field.coframe := by
  change ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
    abs (Matrix.det candidate)) field.coframe
  exact coframe_volume_contDiffAt field.coframe nondegenerate

theorem generatedUnifiedLocalDensityNonGravityCore_withCoframe_contDiffAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
      generatedUnifiedLocalDensityNonGravityCoreAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (withCoframe field candidate)) field.coframe := by
  let boundary := sourceGeneratedUnifiedCouplings source
  change ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
    generatedGaugeSectorBFDensity
        (@specialUnitaryLiePairing (Fin 3) _ _) candidate
        (coframeGaugeSpacetimeHodgeLinear candidate)
        ((boundary.strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear candidate)
        (fun pair => (field.gaugeCurvature pair).1)
        (fun pair => (field.gaugeAuxiliary pair).1) +
      generatedGaugeSectorBFDensity
        (@specialUnitaryLiePairing (Fin 2) _ _) candidate
        (coframeGaugeSpacetimeHodgeLinear candidate)
        ((boundary.weakCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear candidate)
        (fun pair => (field.gaugeCurvature pair).2.1)
        (fun pair => (field.gaugeAuxiliary pair).2.1) +
      generatedGaugeSectorBFDensity hyperchargeLiePairing candidate
        (coframeGaugeSpacetimeHodgeLinear candidate)
        ((boundary.hyperchargeCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear candidate)
        (fun pair => (field.gaugeCurvature pair).2.2)
        (fun pair => (field.gaugeAuxiliary pair).2.2) +
      generatedScalarKineticDensity source 0 point
        (withCoframe field candidate) -
      generatedScalarPotential source 0 point field.scalar +
      generatedContinuumMatterDensity source 0 point
        (withCoframe field candidate)) field.coframe
  exact (((
      (generatedStrongGaugeSector_withCoframe_contDiffAt
        boundary field nondegenerate).add
      (generatedWeakGaugeSector_withCoframe_contDiffAt
        boundary field nondegenerate)).add
      (generatedHyperchargeGaugeSector_withCoframe_contDiffAt
        boundary field nondegenerate)).add
      (generatedScalarKineticDensity_withCoframe_contDiffAt
        source point field nondegenerate)).sub contDiffAt_const |>.add
      (generatedContinuumMatterDensity_withCoframe_contDiffAt
        source point field nondegenerate)

theorem generatedUnifiedLocalDensityCore_withCoframe_contDiffAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
      generatedUnifiedLocalDensityCoreAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (withCoframe field candidate)) field.coframe := by
  unfold generatedUnifiedLocalDensityCoreAtBoundary
  exact (generatedGravityBFDensity_withCoframe_contDiffAt
      field nondegenerate).add
    (generatedUnifiedLocalDensityNonGravityCore_withCoframe_contDiffAt
      source point field nondegenerate)

def coframeLocalInnerDensity
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (coframe : LorentzianCoframe) : ℝ :=
  generatedGravitySimplicityDensity (withCoframe field coframe) +
    generatedUnifiedLocalDensityCoreAtBoundary source
      (sourceGeneratedUnifiedCouplings source) 0 point
      (withCoframe field coframe)

theorem coframeLocalInnerDensity_contDiffAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞ (coframeLocalInnerDensity source point field)
      field.coframe := by
  exact (generatedGravitySimplicityDensity_withCoframe_contDiff
      field).contDiffAt.add
    (generatedUnifiedLocalDensityCore_withCoframe_contDiffAt
      source point field nondegenerate)

theorem coframeLocalDensity_contDiffAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    ContDiffAt ℝ ∞ (coframeLocalDensity source point field)
      field.coframe := by
  change ContDiffAt ℝ ∞ (fun candidate : LorentzianCoframe =>
    generatedVolumeDensity (withCoframe field candidate) *
      coframeLocalInnerDensity source point field candidate) field.coframe
  exact (generatedVolumeDensity_withCoframe_contDiffAt
      field nondegenerate).mul
    (coframeLocalInnerDensity_contDiffAt
      source point field nondegenerate)

def coframeVolumeStressCovector
    (field : StageNineContinuumPointField) : LorentzianCoframe →L[ℝ] ℝ :=
  fderiv ℝ
    (fun candidate : LorentzianCoframe =>
      generatedVolumeDensity (withCoframe field candidate)) field.coframe

def coframeLocalInnerStressCovector
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField) : LorentzianCoframe →L[ℝ] ℝ :=
  fderiv ℝ (coframeLocalInnerDensity source point field) field.coframe

def coframeLocalStressCovector
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField) : LorentzianCoframe →L[ℝ] ℝ :=
  fderiv ℝ (coframeLocalDensity source point field) field.coframe

theorem generatedVolumeDensity_withCoframe_hasFDerivAt
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    HasFDerivAt
      (fun candidate : LorentzianCoframe =>
        generatedVolumeDensity (withCoframe field candidate))
      (coframeVolumeStressCovector field) field.coframe :=
  ((generatedVolumeDensity_withCoframe_contDiffAt field nondegenerate).differentiableAt
    (by simp)).hasFDerivAt

theorem coframeLocalInnerDensity_hasFDerivAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    HasFDerivAt (coframeLocalInnerDensity source point field)
      (coframeLocalInnerStressCovector source point field) field.coframe :=
  ((coframeLocalInnerDensity_contDiffAt source point field
    nondegenerate).differentiableAt (by simp)).hasFDerivAt

theorem coframeLocalDensity_hasFDerivAt
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    HasFDerivAt (coframeLocalDensity source point field)
      (coframeLocalStressCovector source point field) field.coframe :=
  ((coframeLocalDensity_contDiffAt source point field
    nondegenerate).differentiableAt (by simp)).hasFDerivAt

theorem coframeLocalStressCovector_product_rule
    (source : SmoothUnifiedSource) (point : BasePoint)
    (field : StageNineContinuumPointField)
    (nondegenerate : Matrix.det field.coframe ≠ 0) :
    coframeLocalStressCovector source point field =
      generatedVolumeDensity (withCoframe field field.coframe) •
          coframeLocalInnerStressCovector source point field +
        coframeLocalInnerDensity source point field field.coframe •
          coframeVolumeStressCovector field := by
  have productDerivative :=
    (generatedVolumeDensity_withCoframe_hasFDerivAt
      field nondegenerate).mul
    (coframeLocalInnerDensity_hasFDerivAt
      source point field nondegenerate)
  exact (coframeLocalDensity_hasFDerivAt
    source point field nondegenerate).unique productDerivative

end

end SaturationMonoid.PhysicsCore.StageNineCoframeLocalDifferentiability
