import H0mework.Physics.DiracCovariance.Covariance
import H0mework.Physics.Matter.MatterCovariantDerivativeAffine
import H0mework.Physics.Lorentz.SpinLorentzOrientation

/-!
# Pointwise local-Spin covariance of the Dirac kinetic density

This module follows the already generated primitive local-Spin action through
the exact pointwise kinetic consumer chain: frame-relative derivative,
inverse-coframe gamma, kinetic vector, transformed dual evaluation, and
volume density.  The historical Yukawa summand is deliberately excluded: its
root operator has a separate unresolved jurisdiction, so it cannot be hidden
inside this kinetic checkpoint.

The final theorem consumes the generic same-actual covariant derivative
producer.  Intermediate `_of_covariantDerivative` lemmas are algebraic
assembly helpers only; the public root-facing result does not accept a
covariance receipt.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracKineticLocalSpinDensity

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCoframeSpinRepresentation
open StageNineDiracKineticLocalSpinConnection
open StageNineDiracKineticLocalSpinCovariance
open StageNineDiracKineticLocalSpinDifferential
open StageNineDiracKineticSpinJurisdiction
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalBundle
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterCovariantDerivativeAffine
open StageNineSpinLorentzOrientation
open StageNineSpinMatterBundle

open scoped ContDiff MatrixGroups

noncomputable section

set_option autoImplicit false

/-- Removing the source-generated internal frame from a matter field
commutes with the finite Spin action because the two representations act on
independent factors. -/
theorem matterFrameRelative_spin_covariant
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (point : BasePoint)
    (groupElement : SpinPlus13)
    (matter : DiracExteriorMatterCarrier) :
    matterFrameRelative source chart point
        (spinDiracMatterRepresentation groupElement matter) =
      spinDiracMatterRepresentation groupElement
        (matterFrameRelative source chart point matter) := by
  unfold matterFrameRelative
  exact
    (LinearMap.congr_fun
      (spinDiracMatter_commutes_internal groupElement
        (generatedScalarFrame source chart point)⁻¹)
      matter).symm

/-- Removing the source-generated internal frame commutes with the finite
Spin action because the two representations act on independent factors. -/
theorem matterDerivativeFrameRelative_spin_covariant
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (point : BasePoint)
    (groupElement : SpinPlus13)
    (derivative : LorentzianIndex → DiracExteriorMatterCarrier) :
    matterDerivativeFrameRelative source chart point
        (fun direction =>
          spinDiracMatterRepresentation groupElement
            (derivative direction)) =
      fun direction =>
        spinDiracMatterRepresentation groupElement
          (matterDerivativeFrameRelative source chart point
            derivative direction) := by
  funext direction
  exact matterFrameRelative_spin_covariant source chart point groupElement
    (derivative direction)

/-- The kinetic vector occurring in the current continuum matter density,
split off before the historical Yukawa term. -/
def generatedContinuumMatterKineticVector
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField) :
    DiracExteriorMatterCarrier :=
  matterCovariantDerivativeVariationVector source chart point field
    field.matterCovariantDerivative

/-- The kinetic vector descends through the source-generated internal gauge
chart after both its derivative and coframe are read in the same chart. -/
theorem generatedContinuumMatterKineticVector_overlap
    (source : SmoothUnifiedSource)
    (initial terminal : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField) :
    generatedContinuumMatterKineticVector source terminal point
        (transportContinuumPointField source initial terminal point field) =
      generatedContinuumMatterKineticVector source initial point field := by
  have derivativeEquality :
      matterDerivativeFrameRelative source terminal point
          (transportContinuumPointField source initial terminal point
            field).matterCovariantDerivative =
        matterDerivativeFrameRelative source initial point
          field.matterCovariantDerivative := by
    funext direction
    exact matterFrameRelative_overlap source initial terminal point
      (field.matterCovariantDerivative direction)
  unfold generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  rw [derivativeEquality]
  rfl

/-- Algebraic assembly of the kinetic-vector covariance after the primitive
covariant derivative has been generated.  The supplied equality is kept in
this explicitly named helper and is not the root-facing theorem mouth. -/
private theorem generatedContinuumMatterKineticVector_localSpin_covariant_of
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (covariantDerivative :
      ∀ direction : LorentzianIndex,
        holonomicMatterCovariantDerivative
            (localSpinDiracKineticAction spinField configuration)
            point direction =
          spinDiracMatterRepresentation (spinField point)
            (holonomicMatterCovariantDerivative
              configuration point direction)) :
    generatedContinuumMatterKineticVector source chart point
        (toContinuumPointField
          (localSpinDiracKineticAction spinField configuration) point) =
      spinDiracMatterRepresentation (spinField point)
        (generatedContinuumMatterKineticVector source chart point
          (toContinuumPointField configuration point)) := by
  have coframeEquality :
      (toContinuumPointField
          (localSpinDiracKineticAction spinField configuration)
          point).coframe =
        spinLorentzCoframeRepresentation
          (spinWeylDual (spinField point))
          (toContinuumPointField configuration point).coframe := by
    simpa only [toContinuumPointField] using
      localSpinDiracKineticAction_coframe
        spinField configuration point
  have derivativeEquality :
      (toContinuumPointField
          (localSpinDiracKineticAction spinField configuration)
          point).matterCovariantDerivative =
        fun direction =>
          spinDiracMatterRepresentation (spinField point)
            ((toContinuumPointField configuration point)
              |>.matterCovariantDerivative direction) := by
    funext direction
    simpa only [toContinuumPointField] using
      covariantDerivative direction
  have frameDerivativeEquality :
      matterDerivativeFrameRelative source chart point
          ((toContinuumPointField
            (localSpinDiracKineticAction spinField configuration)
            point).matterCovariantDerivative) =
        fun direction =>
          spinDiracMatterRepresentation (spinField point)
            (matterDerivativeFrameRelative source chart point
              (toContinuumPointField configuration point
                |>.matterCovariantDerivative)
              direction) := by
    rw [derivativeEquality]
    exact matterDerivativeFrameRelative_spin_covariant
      source chart point (spinField point)
      (toContinuumPointField configuration point
        |>.matterCovariantDerivative)
  have summandEquality (direction : LorentzianIndex) :
      diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe :=
                (toContinuumPointField
                  (localSpinDiracKineticAction spinField configuration)
                  point).coframe,
              derivative := 0 }
            direction)
          (matterDerivativeFrameRelative source chart point
            (toContinuumPointField
              (localSpinDiracKineticAction spinField configuration)
              point).matterCovariantDerivative
            direction) =
        spinDiracMatterRepresentation (spinField point)
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe :=
                  (toContinuumPointField configuration point).coframe,
                derivative := 0 }
              direction)
            (matterDerivativeFrameRelative source chart point
              (toContinuumPointField configuration point
                |>.matterCovariantDerivative)
              direction)) := by
    rw [coframeEquality, congrFun frameDerivativeEquality direction]
    exact
      inverseCoframeDiracGamma_matterAction_spinWeylDual_equivariant
        (spinField point)
        { coframe := (toContinuumPointField configuration point).coframe,
          derivative := 0 }
        direction
        (matterDerivativeFrameRelative source chart point
          (toContinuumPointField configuration point
            |>.matterCovariantDerivative)
          direction)
  unfold generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  have sumEquality :
      (∑ direction : LorentzianIndex,
          diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe :=
                  (toContinuumPointField
                    (localSpinDiracKineticAction spinField configuration)
                    point).coframe,
                derivative := 0 }
              direction)
            (matterDerivativeFrameRelative source chart point
              (toContinuumPointField
                (localSpinDiracKineticAction spinField configuration)
                point).matterCovariantDerivative
              direction)) =
        ∑ direction : LorentzianIndex,
          spinDiracMatterRepresentation (spinField point)
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe :=
                    (toContinuumPointField configuration point).coframe,
                  derivative := 0 }
                direction)
              (matterDerivativeFrameRelative source chart point
                (toContinuumPointField configuration point
                  |>.matterCovariantDerivative)
                direction)) := by
    exact Finset.sum_congr rfl fun direction _ => summandEquality direction
  rw [sumEquality, ← map_sum, ← map_smul]

/-- Root-facing kinetic-vector covariance generated from the primitive local
Spin action.  Unlike the private algebraic assembly lemma, this theorem does
not accept a derivative-covariance receipt. -/
theorem generatedContinuumMatterKineticVector_localSpin_covariant
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (spinSmooth : LocalSpinFieldSmooth spinField)
    (matterSmooth : ContDiff ℝ ∞ (fun candidate =>
      matterCoordinateEquiv (configuration.matter candidate)))
    (point : BasePoint)
    (connectionSkew :
      LorentzSkew (configuration.gravityConnection point)) :
    generatedContinuumMatterKineticVector source chart point
        (toContinuumPointField
          (localSpinDiracKineticAction spinField configuration) point) =
      spinDiracMatterRepresentation (spinField point)
        (generatedContinuumMatterKineticVector source chart point
          (toContinuumPointField configuration point)) := by
  exact generatedContinuumMatterKineticVector_localSpin_covariant_of
    source chart spinField configuration point
    (fun direction =>
      holonomicMatterCovariantDerivative_localSpin_covariant
        spinField configuration spinSmooth matterSmooth point direction
        connectionSkew)

/-- The inverse-transformed dual cancels the finite Spin action after the
source-generated internal frame is restored. -/
theorem matterDualFrameRelative_spin_evaluation_invariant
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (point : BasePoint)
    (groupElement : SpinPlus13)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (field : DiracExteriorMatterCarrier) :
    matterDualFrameRelative source chart point
        (dual.comp
          (spinDiracMatterRepresentation groupElement⁻¹))
        (spinDiracMatterRepresentation groupElement field) =
      matterDualFrameRelative source chart point dual field := by
  unfold matterDualFrameRelative
  simp only [LinearMap.comp_apply]
  have commute :
      diracExteriorMatterGaugeRepresentation
          (generatedScalarFrame source chart point)
          (spinDiracMatterRepresentation groupElement field) =
        spinDiracMatterRepresentation groupElement
          (diracExteriorMatterGaugeRepresentation
            (generatedScalarFrame source chart point) field) :=
    (LinearMap.congr_fun
      (spinDiracMatter_commutes_internal groupElement
        (generatedScalarFrame source chart point))
      field).symm
  rw [commute, ← Module.End.mul_apply, ← map_mul]
  simp

/-- The generated local Spin action preserves the actual pointwise volume
density. -/
theorem generatedVolumeDensity_localSpinDiracKineticAction
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    generatedVolumeDensity
        (toContinuumPointField
          (localSpinDiracKineticAction spinField configuration) point) =
      generatedVolumeDensity
        (toContinuumPointField configuration point) := by
  change
    abs
        (Matrix.det
          ((localSpinDiracKineticAction spinField configuration)
            |>.coframe point)) =
      abs (Matrix.det (configuration.coframe point))
  rw [localSpinDiracKineticAction_coframe,
    spinLorentzCoframe_det]

/-- Pointwise densitized kinetic-only matter density.  This is exactly the
kinetic contribution consumed by the unified density after its outer volume
factor, with no historical Yukawa term included. -/
def generatedDensitizedContinuumMatterKineticDensity
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField) : ℝ :=
  generatedVolumeDensity field *
    (matterDualFrameRelative source chart point field.conjugateMatter
      (generatedContinuumMatterKineticVector
        source chart point field)).re

/-- Exact source-chart descent of the separately densitized kinetic block. -/
theorem generatedDensitizedContinuumMatterKineticDensity_overlap
    (source : SmoothUnifiedSource)
    (initial terminal : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField) :
    generatedDensitizedContinuumMatterKineticDensity source terminal point
        (transportContinuumPointField source initial terminal point field) =
      generatedDensitizedContinuumMatterKineticDensity source initial point
        field := by
  have dualEquality :
      matterDualFrameRelative source terminal point
          (transportContinuumPointField source initial terminal point
            field).conjugateMatter =
        matterDualFrameRelative source initial point field.conjugateMatter :=
    matterDualFrameRelative_overlap source initial terminal point
      field.conjugateMatter
  have vectorEquality := generatedContinuumMatterKineticVector_overlap
    source initial terminal point field
  unfold generatedDensitizedContinuumMatterKineticDensity
  rw [dualEquality, vectorEquality]
  rfl

/-- Algebraic density assembly from an already generated covariant
derivative equality.  The public theorem below supplies that equality from
the primitive action and its smoothness/skew domain. -/
private theorem
    generatedDensitizedContinuumMatterKineticDensity_localSpin_invariant_of
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (covariantDerivative :
      ∀ direction : LorentzianIndex,
        holonomicMatterCovariantDerivative
            (localSpinDiracKineticAction spinField configuration)
            point direction =
          spinDiracMatterRepresentation (spinField point)
            (holonomicMatterCovariantDerivative
              configuration point direction)) :
    generatedDensitizedContinuumMatterKineticDensity source chart point
        (toContinuumPointField
          (localSpinDiracKineticAction spinField configuration) point) =
      generatedDensitizedContinuumMatterKineticDensity source chart point
        (toContinuumPointField configuration point) := by
  have conjugateEquality :
      (toContinuumPointField
          (localSpinDiracKineticAction spinField configuration)
          point).conjugateMatter =
        (configuration.conjugateMatter point).comp
          (spinDiracMatterRepresentation (spinField point)⁻¹) := by
    simpa only [toContinuumPointField] using
      localSpinDiracKineticAction_conjugateMatter
        spinField configuration point
  unfold generatedDensitizedContinuumMatterKineticDensity
  rw [generatedVolumeDensity_localSpinDiracKineticAction]
  rw [generatedContinuumMatterKineticVector_localSpin_covariant_of
    source chart spinField configuration point covariantDerivative]
  rw [conjugateEquality]
  rw [matterDualFrameRelative_spin_evaluation_invariant]
  simp only [toContinuumPointField]

/-- Root-facing K1--K7 closure: the same primitive smooth local Spin field
generates the transformed coframe, matter, dual, and inhomogeneous connection;
the resulting densitized kinetic-only density is pointwise invariant. -/
theorem generatedDensitizedContinuumMatterKineticDensity_localSpin_invariant
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (spinSmooth : LocalSpinFieldSmooth spinField)
    (matterSmooth : ContDiff ℝ ∞ (fun candidate =>
      matterCoordinateEquiv (configuration.matter candidate)))
    (point : BasePoint)
    (connectionSkew :
      LorentzSkew (configuration.gravityConnection point)) :
    generatedDensitizedContinuumMatterKineticDensity source chart point
        (toContinuumPointField
          (localSpinDiracKineticAction spinField configuration) point) =
      generatedDensitizedContinuumMatterKineticDensity source chart point
        (toContinuumPointField configuration point) := by
  exact
    generatedDensitizedContinuumMatterKineticDensity_localSpin_invariant_of
      source chart spinField configuration point
      (fun direction =>
        holonomicMatterCovariantDerivative_localSpin_covariant
          spinField configuration spinSmooth matterSmooth point direction
          connectionSkew)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracKineticLocalSpinDensity
