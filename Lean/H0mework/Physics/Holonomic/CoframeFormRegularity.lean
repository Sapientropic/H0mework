import H0mework.Physics.Coframe.CoframeGravityGaugeRegularity
import H0mework.Physics.Coframe.CoframeScalarMatterRegularity
import H0mework.Physics.Coframe.CoframeLocalVariation

/-!
# Joint coframe regularity of the form-native action candidate

This module derives joint regularity in the spacetime point and a live
candidate coframe for the active form-native action candidate.  It rebuilds
the action-specific assembly from its metric-free four-form pairings:

```text
gravity BF + direct holonomic reaction + direct gauge BF/constitutive
  + volume * (scalar kinetic - potential + Dirac--Yukawa).
```

Only finite-coordinate smoothness generated from a primitive smooth
holonomic configuration is reused.  In particular, no terminal regularity
receipt from the historical coframe-paired action is consumed.  The final
theorem is an analytic producer for this candidate action; it is not an
Euler--Lagrange equation, stationarity certificate, critical-locus theorem,
or grant of root-action authority.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineFormNativeCoframeHolonomicRegularity

open EmpiricalReferenceScaleCouplingBoundary
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCoframeGravityGaugeRegularity
open StageNineCoframeLocalDifferentiability
open StageNineCoframeScalarMatterRegularity
open StageNineCoframeVariation
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeCoframeLocalVariation
open StageNineFormNativeMotherAction
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineTopologicalFourFormPairing
open StageNineTopologicalGravityCurvatureVariancePairing
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! ## Form-native finite-coordinate pairing calculus -/

/-- Componentwise smooth bivector families have a jointly smooth same-variance
metric-free four-form pairing.  This finite-coordinate lemma carries no
action or field-equation receipt. -/
theorem gravityTopologicalWedgeCoefficient_joint_contDiffAt
    (center : CoframeJoint)
    (first second : CoframeJoint → PhysicalBivector)
    (firstSmooth : ∀ internal spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint => first joint internal spacetime) center)
    (secondSmooth : ∀ internal spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint => second joint internal spacetime) center) :
    ContDiffAt ℝ ∞ (fun joint =>
      gravityTopologicalWedgeCoefficient (first joint) (second joint))
      center := by
  unfold gravityTopologicalWedgeCoefficient
    orientedTwoFormWedgeCoefficient generatedTwoFormWedgeCoefficient
  apply ContDiffAt.sum
  intro internal _
  apply ContDiffAt.mul contDiffAt_const
  apply ContDiffAt.sum
  intro spacetime _
  exact (firstSmooth internal spacetime).mul
    (secondSmooth internal (twoFormComplement spacetime))

/-- Componentwise smooth contravariant/lowered bivector families have a
jointly smooth mixed-variance four-form pairing.  Consumers must reach this
mouth through the authoritative once-only variance seam when starting from
historical lowered curvature. -/
theorem gravityTopologicalMixedWedgeCoefficient_joint_contDiffAt
    (center : CoframeJoint)
    (first second : CoframeJoint → PhysicalBivector)
    (firstSmooth : ∀ internal spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint => first joint internal spacetime) center)
    (secondSmooth : ∀ internal spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint => second joint internal spacetime) center) :
    ContDiffAt ℝ ∞ (fun joint =>
      gravityTopologicalMixedWedgeCoefficient
        (first joint) (second joint)) center := by
  unfold gravityTopologicalMixedWedgeCoefficient
    orientedTwoFormWedgeCoefficient generatedTwoFormWedgeCoefficient
  apply ContDiffAt.sum
  intro internal _
  apply ContDiffAt.sum
  intro spacetime _
  exact (firstSmooth internal spacetime).mul
    (secondSmooth internal (twoFormComplement spacetime))

private theorem specialUnitaryFormNativeWedge_joint_contDiffAt
    {n : Type*} [Fintype n] [DecidableEq n]
    (center : CoframeJoint)
    (first second : CoframeJoint → Fin 6 → SpecialUnitaryLieMatrix n)
    (firstSmooth : ContDiffAt ℝ ∞ first center)
    (secondSmooth : ContDiffAt ℝ ∞ second center) :
    ContDiffAt ℝ ∞ (fun joint =>
      generatedTwoFormWedgeCoefficient
        (@specialUnitaryLiePairing n _ _)
        (first joint) (second joint)) center := by
  unfold generatedTwoFormWedgeCoefficient
  apply ContDiffAt.sum
  intro spacetime _
  exact specialUnitaryLiePairing_joint_contDiffAt center
    (fun joint => first joint spacetime)
    (fun joint => second joint (twoFormComplement spacetime))
    (contDiffAt_pi.mp firstSmooth spacetime)
    (contDiffAt_pi.mp secondSmooth (twoFormComplement spacetime))

private theorem hyperchargeFormNativeWedge_joint_contDiffAt
    (center : CoframeJoint)
    (first second : CoframeJoint → Fin 6 → HyperchargeLieScalar)
    (firstValueSmooth : ∀ spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint => (first joint spacetime).1) center)
    (secondValueSmooth : ∀ spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint => (second joint spacetime).1) center) :
    ContDiffAt ℝ ∞ (fun joint =>
      generatedTwoFormWedgeCoefficient hyperchargeLiePairing
        (first joint) (second joint)) center := by
  unfold generatedTwoFormWedgeCoefficient
  apply ContDiffAt.sum
  intro spacetime _
  exact hyperchargeLiePairing_joint_contDiffAt center
    (fun joint => first joint spacetime)
    (fun joint => second joint (twoFormComplement spacetime))
    (firstValueSmooth spacetime)
    (secondValueSmooth (twoFormComplement spacetime))

private theorem specialUnitaryFormNativeConstitutive_joint_contDiffAt
    {n : Type*} [Fintype n] [DecidableEq n]
    (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0)
    (coupling : ℝ)
    (auxiliary : CoframeJoint → Fin 6 → SpecialUnitaryLieMatrix n)
    (auxiliarySmooth : ContDiffAt ℝ ∞ auxiliary center) :
    ContDiffAt ℝ ∞ (fun joint =>
      generatedTwoFormWedgeCoefficient
        (@specialUnitaryLiePairing n _ _) (auxiliary joint)
        (liftGaugeTwoFormOperator
          (coupling • coframeGaugeSpacetimeHodgeLinear joint.2)
          (auxiliary joint))) center := by
  unfold generatedTwoFormWedgeCoefficient liftGaugeTwoFormOperator
  simp_rw [specialUnitaryLiePairing_sum_right,
    coframeSpecialUnitaryLiePairing_smul_right]
  apply ContDiffAt.sum
  intro spacetime _
  apply ContDiffAt.sum
  intro input _
  exact (jointScaledCoframeHodgeOperatorCoefficient_contDiffAt center
      nondegenerate coupling (twoFormComplement spacetime) input).mul
    (specialUnitaryLiePairing_joint_contDiffAt center
      (fun joint => auxiliary joint spacetime)
      (fun joint => auxiliary joint input)
      (contDiffAt_pi.mp auxiliarySmooth spacetime)
      (contDiffAt_pi.mp auxiliarySmooth input))

private theorem hyperchargeFormNativeConstitutive_joint_contDiffAt
    (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0)
    (coupling : ℝ)
    (auxiliary : CoframeJoint → Fin 6 → HyperchargeLieScalar)
    (auxiliaryValueSmooth : ∀ spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint => (auxiliary joint spacetime).1) center) :
    ContDiffAt ℝ ∞ (fun joint =>
      generatedTwoFormWedgeCoefficient hyperchargeLiePairing
        (auxiliary joint)
        (liftGaugeTwoFormOperator
          (coupling • coframeGaugeSpacetimeHodgeLinear joint.2)
          (auxiliary joint))) center := by
  unfold generatedTwoFormWedgeCoefficient liftGaugeTwoFormOperator
  simp_rw [hyperchargeLiePairing_sum_right,
    coframeHyperchargeLiePairing_smul_right]
  apply ContDiffAt.sum
  intro spacetime _
  apply ContDiffAt.sum
  intro input _
  exact (jointScaledCoframeHodgeOperatorCoefficient_contDiffAt center
      nondegenerate coupling (twoFormComplement spacetime) input).mul
    (hyperchargeLiePairing_joint_contDiffAt center
      (fun joint => auxiliary joint spacetime)
      (fun joint => auxiliary joint input)
      (auxiliaryValueSmooth spacetime)
      (auxiliaryValueSmooth input))

private theorem specialUnitaryFormNativeGaugeSector_joint_contDiffAt
    {n : Type*} [Fintype n] [DecidableEq n]
    (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0)
    (coupling : ℝ)
    (curvature auxiliary : CoframeJoint →
      Fin 6 → SpecialUnitaryLieMatrix n)
    (curvatureSmooth : ContDiffAt ℝ ∞ curvature center)
    (auxiliarySmooth : ContDiffAt ℝ ∞ auxiliary center) :
    ContDiffAt ℝ ∞ (fun joint =>
      generatedFormNativeGaugeSectorBFDensity
        (@specialUnitaryLiePairing n _ _)
        (coupling • coframeGaugeSpacetimeHodgeLinear joint.2)
        (curvature joint) (auxiliary joint)) center := by
  unfold generatedFormNativeGaugeSectorBFDensity
  exact (specialUnitaryFormNativeWedge_joint_contDiffAt center auxiliary
      curvature auxiliarySmooth curvatureSmooth).sub
    (contDiffAt_const.mul
      (specialUnitaryFormNativeConstitutive_joint_contDiffAt center
        nondegenerate coupling auxiliary auxiliarySmooth))

private theorem hyperchargeFormNativeGaugeSector_joint_contDiffAt
    (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0)
    (coupling : ℝ)
    (curvature auxiliary : CoframeJoint →
      Fin 6 → HyperchargeLieScalar)
    (curvatureValueSmooth : ∀ spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint => (curvature joint spacetime).1) center)
    (auxiliaryValueSmooth : ∀ spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint => (auxiliary joint spacetime).1) center) :
    ContDiffAt ℝ ∞ (fun joint =>
      generatedFormNativeGaugeSectorBFDensity hyperchargeLiePairing
        (coupling • coframeGaugeSpacetimeHodgeLinear joint.2)
        (curvature joint) (auxiliary joint)) center := by
  unfold generatedFormNativeGaugeSectorBFDensity
  exact (hyperchargeFormNativeWedge_joint_contDiffAt center auxiliary
      curvature auxiliaryValueSmooth curvatureValueSmooth).sub
    (contDiffAt_const.mul
      (hyperchargeFormNativeConstitutive_joint_contDiffAt center
        nondegenerate coupling auxiliary auxiliaryValueSmooth))

/-! ## Direct form-native gravity and gauge sectors -/

theorem generatedFormNativeGravityBFDensity_joint_contDiffAt
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (center : CoframeJoint) :
    ContDiffAt ℝ ∞ (fun joint =>
      generatedFormNativeGravityBFDensity
        (withCoframe
          (toContinuumPointField configuration joint.1) joint.2)) center := by
  have auxiliarySmooth : ∀ internal spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
        configuration.gravityAuxiliary joint.1 internal spacetime) center :=
    fun internal spacetime =>
      (smooth.2.2.1 internal spacetime).contDiffAt.comp center contDiffAt_fst
  have curvatureSmooth : ∀ internal spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
        holonomicGravityCurvature configuration joint.1
          internal spacetime) center :=
    fun internal spacetime =>
      (holonomicGravityCurvature_component_contDiff configuration smooth
        internal spacetime).contDiffAt.comp center contDiffAt_fst
  have dualAuxiliarySmooth : ∀ internal spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
        gravityInternalDualEquiv
          (configuration.gravityAuxiliary joint.1)
          internal spacetime) center :=
    fun internal spacetime =>
      (contDiff_pi.mp (contDiff_pi.mp
        (holonomicGravityInternalDualAuxiliary_contDiff configuration smooth)
        internal) spacetime).contDiffAt.comp center contDiffAt_fst
  have bfSmooth : ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
      gravityTopologicalBFCoefficient
        (configuration.gravityAuxiliary joint.1)
        (holonomicGravityCurvature configuration joint.1)) center := by
    rw [show (fun joint : CoframeJoint =>
        gravityTopologicalBFCoefficient
          (configuration.gravityAuxiliary joint.1)
          (holonomicGravityCurvature configuration joint.1)) =
      fun joint => gravityTopologicalMixedWedgeCoefficient
        (configuration.gravityAuxiliary joint.1)
        (holonomicGravityCurvature configuration joint.1) by
      funext joint
      exact gravityTopologicalBFCoefficient_eq_mixed _ _]
    exact gravityTopologicalMixedWedgeCoefficient_joint_contDiffAt center
      (fun joint => configuration.gravityAuxiliary joint.1)
      (fun joint => holonomicGravityCurvature configuration joint.1)
      auxiliarySmooth curvatureSmooth
  have constitutiveSmooth : ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
      gravityTopologicalWedgeCoefficient
        (configuration.gravityAuxiliary joint.1)
        (gravityInternalDualEquiv
          (configuration.gravityAuxiliary joint.1))) center :=
    gravityTopologicalWedgeCoefficient_joint_contDiffAt center
      (fun joint => configuration.gravityAuxiliary joint.1)
      (fun joint => gravityInternalDualEquiv
        (configuration.gravityAuxiliary joint.1))
      auxiliarySmooth dualAuxiliarySmooth
  have scaledConstitutiveSmooth : ContDiffAt ℝ ∞
      (fun joint : CoframeJoint => (1 / 2 : ℝ) *
        gravityTopologicalWedgeCoefficient
          (configuration.gravityAuxiliary joint.1)
          (gravityInternalDualEquiv
            (configuration.gravityAuxiliary joint.1))) center :=
    contDiffAt_const.mul constitutiveSmooth
  have actual := bfSmooth.sub scaledConstitutiveSmooth
  simpa only [generatedFormNativeGravityBFDensity, withCoframe,
    toContinuumPointField] using actual

theorem generatedFormNativeGravityConstraintDensity_joint_contDiffAt
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (center : CoframeJoint) :
    ContDiffAt ℝ ∞ (fun joint =>
      generatedFormNativeGravityConstraintDensity
        (withCoframe
          (toContinuumPointField configuration joint.1) joint.2)) center := by
  have multiplierSmooth : ∀ internal spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
        configuration.gravitySimplicityMultiplier joint.1
          internal spacetime) center :=
    fun internal spacetime =>
      (smooth.2.2.2.1 internal spacetime).contDiffAt.comp
        center contDiffAt_fst
  have residualSmooth : ∀ internal spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
        configuration.gravityAuxiliary joint.1 internal spacetime -
          physicalIIPlusBivector joint.2 internal spacetime) center := by
    intro internal spacetime
    exact ((smooth.2.2.1 internal spacetime).contDiffAt.comp
        center contDiffAt_fst).sub
      ((contDiff_pi.mp (contDiff_pi.mp physicalIIPlusBivector_contDiff
        internal) spacetime).contDiffAt.comp center contDiffAt_snd)
  have actual := gravityTopologicalWedgeCoefficient_joint_contDiffAt center
    (fun joint => configuration.gravitySimplicityMultiplier joint.1)
    (fun joint => configuration.gravityAuxiliary joint.1 -
      physicalIIPlusBivector joint.2)
    multiplierSmooth residualSmooth
  simpa only [generatedFormNativeGravityConstraintDensity,
    generatedGravitySimplicityResidual, withCoframe,
    toContinuumPointField] using actual

theorem generatedFormNativeGaugeDensityAtBoundary_joint_contDiffAt
    (boundary : EmpiricalReferenceScaleCouplings)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (center : CoframeJoint)
    (nondegenerate : Matrix.det center.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun joint =>
      generatedFormNativeGaugeDensityAtBoundary boundary
        (withCoframe
          (toContinuumPointField configuration joint.1) joint.2)) center := by
  have strongCurvatureSmooth : ContDiffAt ℝ ∞
      (fun joint : CoframeJoint => fun spacetime =>
        (holonomicGaugeCurvature configuration joint.1 spacetime).1)
      center :=
    (holonomicStrongCurvature_contDiff configuration smooth).contDiffAt.comp
      center contDiffAt_fst
  have weakCurvatureSmooth : ContDiffAt ℝ ∞
      (fun joint : CoframeJoint => fun spacetime =>
        (holonomicGaugeCurvature configuration joint.1 spacetime).2.1)
      center :=
    (holonomicWeakCurvature_contDiff configuration smooth).contDiffAt.comp
      center contDiffAt_fst
  have strongAuxiliarySmooth : ContDiffAt ℝ ∞
      (fun joint : CoframeJoint => fun spacetime =>
        (configuration.gaugeAuxiliary joint.1 spacetime).1) center :=
    (holonomicStrongAuxiliary_contDiff configuration smooth).contDiffAt.comp
      center contDiffAt_fst
  have weakAuxiliarySmooth : ContDiffAt ℝ ∞
      (fun joint : CoframeJoint => fun spacetime =>
        (configuration.gaugeAuxiliary joint.1 spacetime).2.1) center :=
    (holonomicWeakAuxiliary_contDiff configuration smooth).contDiffAt.comp
      center contDiffAt_fst
  have hyperchargeCurvatureSmooth : ∀ spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
        (holonomicGaugeCurvature configuration joint.1 spacetime).2.2.1)
        center :=
    fun spacetime =>
      (holonomicHyperchargeCurvature_component_contDiff configuration smooth
        spacetime).contDiffAt.comp center contDiffAt_fst
  have hyperchargeAuxiliarySmooth : ∀ spacetime : Fin 6,
      ContDiffAt ℝ ∞ (fun joint : CoframeJoint =>
        (configuration.gaugeAuxiliary joint.1 spacetime).2.2.1) center :=
    fun spacetime =>
      (holonomicHyperchargeAuxiliary_component_contDiff configuration smooth
        spacetime).contDiffAt.comp center contDiffAt_fst
  have strongSmooth := specialUnitaryFormNativeGaugeSector_joint_contDiffAt
    center nondegenerate (boundary.strongCouplingSquared : ℝ)
    (fun joint spacetime =>
      (holonomicGaugeCurvature configuration joint.1 spacetime).1)
    (fun joint spacetime =>
      (configuration.gaugeAuxiliary joint.1 spacetime).1)
    strongCurvatureSmooth strongAuxiliarySmooth
  have weakSmooth := specialUnitaryFormNativeGaugeSector_joint_contDiffAt
    center nondegenerate (boundary.weakCouplingSquared : ℝ)
    (fun joint spacetime =>
      (holonomicGaugeCurvature configuration joint.1 spacetime).2.1)
    (fun joint spacetime =>
      (configuration.gaugeAuxiliary joint.1 spacetime).2.1)
    weakCurvatureSmooth weakAuxiliarySmooth
  have hyperchargeSmooth :=
    hyperchargeFormNativeGaugeSector_joint_contDiffAt center nondegenerate
      (boundary.hyperchargeCouplingSquared : ℝ)
      (fun joint spacetime =>
        (holonomicGaugeCurvature configuration joint.1 spacetime).2.2)
      (fun joint spacetime =>
        (configuration.gaugeAuxiliary joint.1 spacetime).2.2)
      hyperchargeCurvatureSmooth hyperchargeAuxiliarySmooth
  have actual := (strongSmooth.add weakSmooth).add hyperchargeSmooth
  simpa only [generatedFormNativeGaugeDensityAtBoundary,
    gaugeConstitutiveOperatorAtBoundary, withCoframe,
    toContinuumPointField] using actual

/-! ## Candidate action assembly -/

/-- The three form-native gravity/gauge blocks before the independent matter
volume factor is installed. -/
def holonomicFormNativeCoframeGravityGaugeDensity
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (joint : CoframeJoint) : ℝ :=
  generatedFormNativeGravityBFDensity
      (withCoframe
        (toContinuumPointField configuration joint.1) joint.2) +
    generatedFormNativeGravityConstraintDensity
      (withCoframe
        (toContinuumPointField configuration joint.1) joint.2) +
    generatedFormNativeGaugeDensityAtBoundary
      (sourceGeneratedUnifiedCouplings source)
      (withCoframe
        (toContinuumPointField configuration joint.1) joint.2)

/-- The scalar and Dirac--Yukawa block with its own live coordinate volume. -/
def holonomicFormNativeCoframeMatterDensity
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (joint : CoframeJoint) : ℝ :=
  generatedFormNativeMatterDensity source 0 joint.1
    (withCoframe
      (toContinuumPointField configuration joint.1) joint.2)

/-- The active candidate density as a family in the base point and an
independently selected coframe. -/
def holonomicFormNativeCoframeLocalDensityFamily
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (candidate : LorentzianCoframe) : ℝ :=
  formNativeCoframeLocalDensity source point
    (toContinuumPointField configuration point) candidate

theorem holonomicFormNativeCoframeMatterDensity_eq_volume_mul_scalarMatter
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (joint : CoframeJoint) :
    holonomicFormNativeCoframeMatterDensity source configuration joint =
      generatedVolumeDensity
          (withCoframe
            (toContinuumPointField configuration joint.1) joint.2) *
        (generatedScalarKineticDensity source 0 joint.1
              (withCoframe
                (toContinuumPointField configuration joint.1) joint.2) -
          generatedScalarPotential source 0 joint.1
              (withCoframe
                (toContinuumPointField configuration joint.1) joint.2).scalar +
          generatedContinuumMatterDensity source 0 joint.1
              (withCoframe
                (toContinuumPointField configuration joint.1) joint.2)) := by
  rfl

theorem holonomicFormNativeCoframeLocalDensityFamily_eq_sector_sum
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (joint : CoframeJoint) :
    Function.uncurry
        (holonomicFormNativeCoframeLocalDensityFamily source configuration)
        joint =
      holonomicFormNativeCoframeGravityGaugeDensity source configuration
          joint +
        holonomicFormNativeCoframeMatterDensity source configuration joint := by
  unfold holonomicFormNativeCoframeLocalDensityFamily
    formNativeCoframeLocalDensity
    sourceGeneratedFormNativeUnifiedLocalDensity
    generatedFormNativeUnifiedLocalDensityAtBoundary
    holonomicFormNativeCoframeGravityGaugeDensity
    holonomicFormNativeCoframeMatterDensity
  rfl

theorem holonomicFormNativeCoframeGravityGaugeDensity_joint_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (nondegenerate : Matrix.det candidate ≠ 0) :
    ContDiffAt ℝ 1
      (holonomicFormNativeCoframeGravityGaugeDensity source configuration)
      (point, candidate) := by
  have gravityBFSmooth :=
    generatedFormNativeGravityBFDensity_joint_contDiffAt configuration smooth
      (point, candidate)
  have constraintSmooth :=
    generatedFormNativeGravityConstraintDensity_joint_contDiffAt
      configuration smooth (point, candidate)
  have gaugeSmooth :=
    generatedFormNativeGaugeDensityAtBoundary_joint_contDiffAt
      (sourceGeneratedUnifiedCouplings source) configuration smooth
      (point, candidate) nondegenerate
  unfold holonomicFormNativeCoframeGravityGaugeDensity
  exact ((gravityBFSmooth.add constraintSmooth).add gaugeSmooth).of_le
    (by norm_num)

theorem holonomicFormNativeCoframeMatterDensity_joint_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (nondegenerate : Matrix.det candidate ≠ 0) :
    ContDiffAt ℝ 1
      (holonomicFormNativeCoframeMatterDensity source configuration)
      (point, candidate) := by
  have volumeSmooth : ContDiffAt ℝ 1
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
  have scalarMatterSmooth :=
    generatedScalarMatterSector_pointCoframe_contDiffAt source configuration
      smooth point candidate nondegenerate
  rw [show holonomicFormNativeCoframeMatterDensity source configuration =
      fun joint : CoframeJoint =>
        generatedVolumeDensity
            (withCoframe
              (toContinuumPointField configuration joint.1) joint.2) *
          (generatedScalarKineticDensity source 0 joint.1
                (withCoframe
                  (toContinuumPointField configuration joint.1) joint.2) -
            generatedScalarPotential source 0 joint.1
                (withCoframe
                  (toContinuumPointField configuration joint.1) joint.2).scalar +
            generatedContinuumMatterDensity source 0 joint.1
                (withCoframe
                  (toContinuumPointField configuration joint.1) joint.2)) by
    funext joint
    exact holonomicFormNativeCoframeMatterDensity_eq_volume_mul_scalarMatter
      source configuration joint]
  exact volumeSmooth.mul scalarMatterSmooth

/-- Joint `C¹` regularity of the active form-native candidate at every
nondegenerate live coframe.  The only physical premise is primitive
configuration smoothness; nondegeneracy selects the analytic inverse-frame
branch. -/
theorem holonomicFormNativeCoframeLocalDensityFamily_joint_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (nondegenerate : Matrix.det candidate ≠ 0) :
    ContDiffAt ℝ 1
      (Function.uncurry
        (holonomicFormNativeCoframeLocalDensityFamily source configuration))
      (point, candidate) := by
  rw [show Function.uncurry
      (holonomicFormNativeCoframeLocalDensityFamily source configuration) =
        fun joint : CoframeJoint =>
          holonomicFormNativeCoframeGravityGaugeDensity source configuration
              joint +
            holonomicFormNativeCoframeMatterDensity source configuration
              joint by
    funext joint
    exact holonomicFormNativeCoframeLocalDensityFamily_eq_sector_sum
      source configuration joint]
  exact
    (holonomicFormNativeCoframeGravityGaugeDensity_joint_contDiffAt source
      configuration smooth point candidate nondegenerate).add
    (holonomicFormNativeCoframeMatterDensity_joint_contDiffAt source
      configuration smooth point candidate nondegenerate)

end

end
  SaturationMonoid.PhysicsCore.StageNineFormNativeCoframeHolonomicRegularity
