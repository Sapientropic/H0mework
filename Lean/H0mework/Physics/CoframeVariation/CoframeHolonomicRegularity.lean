import H0mework.Physics.CoframeVariation.CoframeLocalVariation
import H0mework.Physics.Holonomic.CoframeFormRegularity
import H0mework.Physics.DualVariation.ConjugateMatterVariation

/-!
# Joint coframe regularity of the Dirac-dual form-native root

This module lifts the repaired coframe-local producer to a jointly varying
spacetime point and live coframe.  The gravity BF, direct constraint, and
gauge constitutive family reuse their formulation-neutral joint calculus.
The scalar, kinetic, and repaired Yukawa family is rebuilt from the new root:
the kinetic vector sees the live inverse coframe, the repaired Yukawa vector
is generated bilinearly from the live scalar and matter fields, and the same
independent dual and volume density evaluate their sum.

The terminal theorem is analytic regularity of the actual new density.  It is
not an equation, stationarity certificate, integrability receipt, or
stationary actual.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCoframeHolonomicRegularity

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCoframeGravityGaugeRegularity
open StageNineCoframeLocalDifferentiability
open StageNineCoframeScalarMatterRegularity
open StageNineCoframeVariation
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracKineticLocalSpinDensity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeCoframeHolonomicRegularity
open StageNineFormNativeMotherAction
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterCovariantDerivativeAffine
open StageNineScalarLocalSpinDensity
open SU7ExteriorBreakingYukawa
open SU7ExteriorMatterRepresentation
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

/-! ## Repaired forward-vector regularity -/

/-- Joint smoothness of the kinetic-only vector before a Yukawa epoch is
selected. -/
theorem generatedContinuumMatterKineticVector_pointCoframe_coordinate_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (candidateNondegenerate : Matrix.det candidate ≠ 0) :
    ContDiffAt ℝ ∞
      (fun pair : BasePoint × LorentzianCoframe =>
        matterCoordinateEquiv
          (generatedContinuumMatterKineticVector source 0 pair.1
            (withCoframe
              (toContinuumPointField configuration pair.1) pair.2)))
      (point, candidate) := by
  have gammaSmooth : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ ∞
        (fun pair : BasePoint × LorentzianCoframe =>
          inverseCoframeDiracGamma
            { coframe := pair.2, derivative := 0 } direction)
        (point, candidate) := by
    intro direction
    have outer : ContDiffAt ℝ ∞
        (fun coframe : LorentzianCoframe =>
          inverseCoframeDiracGamma
            { coframe := coframe, derivative := 0 } direction) candidate :=
      inverseCoframeDiracGamma_contDiffAt candidate
        candidateNondegenerate direction
    rw [show (fun pair : BasePoint × LorentzianCoframe =>
        inverseCoframeDiracGamma
          { coframe := pair.2, derivative := 0 } direction) =
      (fun coframe : LorentzianCoframe =>
        inverseCoframeDiracGamma
          { coframe := coframe, derivative := 0 } direction) ∘
        (fun pair : BasePoint × LorentzianCoframe => pair.2) by rfl]
    exact outer.comp (point, candidate) contDiffAt_snd
  have derivativeSmooth : ∀ direction : LorentzianIndex,
      ContDiff ℝ ∞
        (fun pair : BasePoint × LorentzianCoframe =>
          matterCoordinateEquiv
            (holonomicMatterCovariantDerivative configuration pair.1
              direction)) := by
    intro direction
    exact (holonomicMatterCovariantDerivative_coordinate_contDiff_local
      configuration smooth direction).comp contDiff_fst
  have kineticDirectionSmooth : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ ∞
        (fun pair : BasePoint × LorentzianCoframe =>
          matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := pair.2, derivative := 0 } direction)
              (holonomicMatterCovariantDerivative configuration pair.1
                direction)))
        (point, candidate) := by
    intro direction
    have actualGamma := gammaSmooth direction
    have actualDerivative : ContDiffAt ℝ ∞
        (fun pair : BasePoint × LorentzianCoframe =>
          matterCoordinateEquiv
            (holonomicMatterCovariantDerivative configuration pair.1
              direction)) (point, candidate) :=
      (derivativeSmooth direction).contDiffAt
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp (point, candidate) actualGamma).clm_apply
          actualDerivative
    change ContDiffAt ℝ ∞
      (fun pair : BasePoint × LorentzianCoframe =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := pair.2, derivative := 0 } direction)
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv
                (holonomicMatterCovariantDerivative configuration pair.1
                  direction))))) (point, candidate) at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  simp only [generatedContinuumMatterKineticVector,
    matterCovariantDerivativeVariationVector,
    matterCovariantDerivativeKineticSum,
    matterDerivativeFrameRelative, matterFrameRelative_zeroChart_local,
    withCoframe, toContinuumPointField]
  simp only [map_smul, map_sum]
  exact
    (contDiffAt_const : ContDiffAt ℝ ∞
      (fun _ : BasePoint × LorentzianCoframe => (Complex.I : ℂ))
      (point, candidate)).smul
      (ContDiffAt.sum fun direction _ => kineticDirectionSmooth direction)

theorem diracDualYukawaCoordinate_add_right
    (scalar : ScalarCoordinateCarrier)
    (first second : MatterCoordinateCarrier) :
    matterCoordinateEquiv
        (diracDualRightChiralYukawaAction
          (scalarCoordinateEquiv.symm scalar)
          (matterCoordinateEquiv.symm (first + second))) =
      matterCoordinateEquiv
          (diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm scalar)
            (matterCoordinateEquiv.symm first)) +
        matterCoordinateEquiv
          (diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm scalar)
            (matterCoordinateEquiv.symm second)) := by
  simp only [map_add]

theorem diracDualYukawaCoordinate_real_smul_right
    (scalar : ScalarCoordinateCarrier) (parameter : ℝ)
    (matter : MatterCoordinateCarrier) :
    matterCoordinateEquiv
        (diracDualRightChiralYukawaAction
          (scalarCoordinateEquiv.symm scalar)
          (matterCoordinateEquiv.symm (parameter • matter))) =
      parameter •
        matterCoordinateEquiv
          (diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm scalar)
            (matterCoordinateEquiv.symm matter)) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [map_smul]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) parameter _).symm

/-- Real-scalar bilinear form of the repaired Yukawa coordinate operator,
used by joint real Fréchet calculus. -/
def diracDualYukawaCoordinateRealBilinear :
    ScalarCoordinateCarrier →ₗ[ℝ]
      MatterCoordinateCarrier →ₗ[ℝ] MatterCoordinateCarrier where
  toFun scalar :=
    { toFun := fun matter =>
        matterCoordinateEquiv
          (diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm scalar)
            (matterCoordinateEquiv.symm matter))
      map_add' := by
        intro first second
        exact diracDualYukawaCoordinate_add_right scalar first second
      map_smul' := by
        intro parameter matter
        exact diracDualYukawaCoordinate_real_smul_right
          scalar parameter matter }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro matter
    change
      matterCoordinateEquiv
          (diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm (first + second))
            (matterCoordinateEquiv.symm matter)) =
        matterCoordinateEquiv
            (diracDualRightChiralYukawaAction
              (scalarCoordinateEquiv.symm first)
              (matterCoordinateEquiv.symm matter)) +
          matterCoordinateEquiv
            (diracDualRightChiralYukawaAction
              (scalarCoordinateEquiv.symm second)
              (matterCoordinateEquiv.symm matter))
    rw [scalarCoordinateEquiv.symm.map_add,
      diracDualRightChiralYukawaAction_add, LinearMap.add_apply, map_add]
  map_smul' := by
    intro parameter scalar
    apply LinearMap.ext
    intro matter
    change
      matterCoordinateEquiv
          (diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm (parameter • scalar))
            (matterCoordinateEquiv.symm matter)) =
        parameter •
          matterCoordinateEquiv
            (diracDualRightChiralYukawaAction
              (scalarCoordinateEquiv.symm scalar)
              (matterCoordinateEquiv.symm matter))
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rw [scalarCoordinateEquiv.symm.map_smul,
      diracDualRightChiralYukawaAction_smul,
      LinearMap.smul_apply, map_smul]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) parameter _).symm

/-- The repaired Yukawa vector is a genuine joint bilinear readout of the
primitive smooth scalar and matter fields. -/
theorem generatedContinuumDiracDualYukawaVector_pointCoframe_coordinate_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (candidate : LorentzianCoframe) :
    ContDiffAt ℝ ∞
      (fun pair : BasePoint × LorentzianCoframe =>
        matterCoordinateEquiv
          (generatedContinuumDiracDualYukawaVector source 0 pair.1
            (withCoframe
              (toContinuumPointField configuration pair.1) pair.2)))
      (point, candidate) := by
  have scalarSmooth : ContDiff ℝ ∞ configuration.scalar :=
    smooth.2.2.2.2.2.2.1
  have matterSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv (configuration.matter point) :=
    smooth.2.2.2.2.2.2.2.1
  have scalarOnProduct : ContDiff ℝ ∞ fun pair :
      BasePoint × LorentzianCoframe => configuration.scalar pair.1 :=
    scalarSmooth.comp contDiff_fst
  have matterOnProduct : ContDiff ℝ ∞ fun pair :
      BasePoint × LorentzianCoframe =>
        matterCoordinateEquiv (configuration.matter pair.1) :=
    matterSmooth.comp contDiff_fst
  have actual :=
    (diracDualYukawaCoordinateRealBilinear.toContinuousBilinearMap.contDiff.comp
      scalarOnProduct).clm_apply matterOnProduct
  change ContDiff ℝ ∞ fun pair : BasePoint × LorentzianCoframe =>
    matterCoordinateEquiv
      (diracDualRightChiralYukawaAction
        (scalarCoordinateEquiv.symm (configuration.scalar pair.1))
        (matterCoordinateEquiv.symm
          (matterCoordinateEquiv (configuration.matter pair.1)))) at actual
  have repairedSmooth : ContDiff ℝ ∞ fun pair :
      BasePoint × LorentzianCoframe =>
        matterCoordinateEquiv
          (diracDualRightChiralYukawaAction
            (scalarCoordinateEquiv.symm (configuration.scalar pair.1))
            (configuration.matter pair.1)) := by
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  simpa only [generatedContinuumDiracDualYukawaVector,
    scalarFrameRelativeCoordinates_zeroChart_local,
    matterFrameRelative_zeroChart_local, withCoframe,
    toContinuumPointField] using repairedSmooth.contDiffAt

/-- Complete repaired kinetic-plus-Yukawa vector regularity on the joint
carrier. -/
theorem generatedContinuumDiracDualMatterVector_pointCoframe_coordinate_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (candidateNondegenerate : Matrix.det candidate ≠ 0) :
    ContDiffAt ℝ ∞
      (fun pair : BasePoint × LorentzianCoframe =>
        matterCoordinateEquiv
          (generatedContinuumDiracDualMatterVector source 0 pair.1
            (withCoframe
              (toContinuumPointField configuration pair.1) pair.2)))
      (point, candidate) := by
  unfold generatedContinuumDiracDualMatterVector
  simp only [map_add]
  exact
    (generatedContinuumMatterKineticVector_pointCoframe_coordinate_contDiffAt
      source configuration smooth point candidate candidateNondegenerate).add
    (generatedContinuumDiracDualYukawaVector_pointCoframe_coordinate_contDiffAt
      source configuration smooth point candidate)

/-! ## Densitized repaired matter regularity -/

private theorem generatedVolumeDensity_pointCoframe_contDiffAt
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (nondegenerate : Matrix.det candidate ≠ 0) :
    ContDiffAt ℝ 1
      (fun joint : CoframeJoint =>
        generatedVolumeDensity
          (withCoframe
            (toContinuumPointField configuration joint.1) joint.2))
      (point, candidate) := by
  change ContDiffAt ℝ 1 (fun joint : CoframeJoint =>
    abs (Matrix.det joint.2)) (point, candidate)
  have jointInfinite : ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
      abs (Matrix.det joint.2)) (point, candidate) :=
    (coframe_volume_contDiffAt candidate nondegenerate).comp
      (point, candidate) contDiffAt_snd
  exact jointInfinite.of_le (by norm_num)

theorem generatedDensitizedContinuumDiracDualMatterDensity_pointCoframe_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (candidateNondegenerate : Matrix.det candidate ≠ 0) :
    ContDiffAt ℝ 1
      (fun pair : BasePoint × LorentzianCoframe =>
        generatedDensitizedContinuumDiracDualMatterDensity source 0 pair.1
          (withCoframe
            (toContinuumPointField configuration pair.1) pair.2))
      (point, candidate) := by
  let vector := fun pair : BasePoint × LorentzianCoframe =>
    generatedContinuumDiracDualMatterVector source 0 pair.1
      (withCoframe
        (toContinuumPointField configuration pair.1) pair.2)
  have vectorCoordinateSmooth : ContDiffAt ℝ ∞
      (fun pair : BasePoint × LorentzianCoframe =>
        matterCoordinateEquiv (vector pair)) (point, candidate) :=
    generatedContinuumDiracDualMatterVector_pointCoframe_coordinate_contDiffAt
      source configuration smooth point candidate candidateNondegenerate
  have dualCoordinateSmooth : ∀ index : MatterCoordinateIndex,
      ContDiff ℝ ∞
        (fun pair : BasePoint × LorentzianCoframe =>
          configuration.conjugateMatter pair.1
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ)))) := by
    intro index
    exact (smooth.2.2.2.2.2.2.2.2 index).comp contDiff_fst
  have pairingSumSmooth : ContDiffAt ℝ ∞
      (fun pair : BasePoint × LorentzianCoframe =>
        ∑ index : MatterCoordinateIndex,
          matterCoordinateEquiv (vector pair) index *
            configuration.conjugateMatter pair.1
              (matterCoordinateEquiv.symm
                (EuclideanSpace.single index (1 : ℂ))))
      (point, candidate) := by
    apply ContDiffAt.sum
    intro index _
    have vectorEntrySmooth : ContDiffAt ℝ ∞
        (fun pair : BasePoint × LorentzianCoframe =>
          matterCoordinateEquiv (vector pair) index) (point, candidate) := by
      fun_prop
    exact vectorEntrySmooth.mul (dualCoordinateSmooth index).contDiffAt
  have dualPairingSmooth : ContDiffAt ℝ ∞
      (fun pair : BasePoint × LorentzianCoframe =>
        configuration.conjugateMatter pair.1 (vector pair))
      (point, candidate) := by
    rw [show (fun pair : BasePoint × LorentzianCoframe =>
        configuration.conjugateMatter pair.1 (vector pair)) =
      fun pair => ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv (vector pair) index *
          configuration.conjugateMatter pair.1
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) by
      funext pair
      simpa only [matterCoordinateEquiv.symm_apply_apply] using
        coframeMatterDual_coordinate_expansion
          (configuration.conjugateMatter pair.1)
          (matterCoordinateEquiv (vector pair))]
    exact pairingSumSmooth
  have realPairingSmooth : ContDiffAt ℝ 1
      (fun pair : BasePoint × LorentzianCoframe =>
        (configuration.conjugateMatter pair.1 (vector pair)).re)
      (point, candidate) :=
    (Complex.reCLM.contDiff.contDiffAt.comp (point, candidate)
      dualPairingSmooth).of_le (by norm_num)
  have exactDensity :
      (fun pair : BasePoint × LorentzianCoframe =>
        generatedDensitizedContinuumDiracDualMatterDensity source 0 pair.1
          (withCoframe
            (toContinuumPointField configuration pair.1) pair.2)) =
      fun pair =>
        generatedVolumeDensity
            (withCoframe
              (toContinuumPointField configuration pair.1) pair.2) *
          (configuration.conjugateMatter pair.1 (vector pair)).re := by
    funext pair
    rw [generatedDensitizedContinuumDiracDualMatterDensity_eq_vectorPairing]
    simp only [matterDualFrameRelative_zeroChart_local,
      withCoframe, toContinuumPointField, vector]
  rw [exactDensity]
  exact (generatedVolumeDensity_pointCoframe_contDiffAt configuration
    point candidate candidateNondegenerate).mul realPairingSmooth

theorem generatedDensitizedContinuumScalarDensity_pointCoframe_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (candidateNondegenerate : Matrix.det candidate ≠ 0) :
    ContDiffAt ℝ 1
      (fun pair : BasePoint × LorentzianCoframe =>
        generatedDensitizedContinuumScalarDensity source 0 pair.1
          (withCoframe
            (toContinuumPointField configuration pair.1) pair.2))
      (point, candidate) := by
  unfold generatedDensitizedContinuumScalarDensity
  exact (generatedVolumeDensity_pointCoframe_contDiffAt configuration
    point candidate candidateNondegenerate).mul
    ((generatedScalarKineticDensity_pointCoframe_contDiffAt source
      configuration smooth point candidate candidateNondegenerate).sub
      (generatedScalarPotential_pointCoframe_contDiffAt source
        configuration smooth point candidate))

/-! ## Direct new-root joint assembly -/

def holonomicDiracDualFormNativeCoframeMatterDensity
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (joint : CoframeJoint) : ℝ :=
  generatedDiracDualFormNativeMatterDensity source 0 joint.1
    (withCoframe
      (toContinuumPointField configuration joint.1) joint.2)

def holonomicDiracDualFormNativeCoframeLocalDensityFamily
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (candidate : LorentzianCoframe) : ℝ :=
  diracDualFormNativeCoframeLocalDensity source point
    (toContinuumPointField configuration point) candidate

theorem holonomicDiracDualFormNativeCoframeLocalDensityFamily_eq_sector_sum
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (joint : CoframeJoint) :
    Function.uncurry
        (holonomicDiracDualFormNativeCoframeLocalDensityFamily source
          configuration) joint =
      holonomicFormNativeCoframeGravityGaugeDensity source configuration
          joint +
        holonomicDiracDualFormNativeCoframeMatterDensity source configuration
          joint := by
  unfold holonomicDiracDualFormNativeCoframeLocalDensityFamily
    diracDualFormNativeCoframeLocalDensity
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
    holonomicFormNativeCoframeGravityGaugeDensity
    holonomicDiracDualFormNativeCoframeMatterDensity
  rfl

theorem holonomicDiracDualFormNativeCoframeMatterDensity_joint_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (nondegenerate : Matrix.det candidate ≠ 0) :
    ContDiffAt ℝ 1
      (holonomicDiracDualFormNativeCoframeMatterDensity source configuration)
      (point, candidate) := by
  unfold holonomicDiracDualFormNativeCoframeMatterDensity
    generatedDiracDualFormNativeMatterDensity
  exact
    (generatedDensitizedContinuumScalarDensity_pointCoframe_contDiffAt source
      configuration smooth point candidate nondegenerate).add
    (generatedDensitizedContinuumDiracDualMatterDensity_pointCoframe_contDiffAt
      source configuration smooth point candidate nondegenerate)

/-- Joint `C¹` regularity of the repaired root at every nondegenerate live
coframe. -/
theorem holonomicDiracDualFormNativeCoframeLocalDensityFamily_joint_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (nondegenerate : Matrix.det candidate ≠ 0) :
    ContDiffAt ℝ 1
      (Function.uncurry
        (holonomicDiracDualFormNativeCoframeLocalDensityFamily source
          configuration))
      (point, candidate) := by
  rw [show Function.uncurry
      (holonomicDiracDualFormNativeCoframeLocalDensityFamily source
        configuration) =
      fun joint : CoframeJoint =>
        holonomicFormNativeCoframeGravityGaugeDensity source configuration
            joint +
          holonomicDiracDualFormNativeCoframeMatterDensity source
            configuration joint by
    funext joint
    exact
      holonomicDiracDualFormNativeCoframeLocalDensityFamily_eq_sector_sum
        source configuration joint]
  exact
    (holonomicFormNativeCoframeGravityGaugeDensity_joint_contDiffAt source
      configuration smooth point candidate nondegenerate).add
    (holonomicDiracDualFormNativeCoframeMatterDensity_joint_contDiffAt source
      configuration smooth point candidate nondegenerate)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCoframeHolonomicRegularity
