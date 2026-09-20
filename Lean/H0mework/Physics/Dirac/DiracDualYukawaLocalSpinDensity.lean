import H0mework.Physics.Dirac.DiracDualYukawaSpinJurisdiction
import H0mework.Physics.DiracCovariance.Density

/-!
# Repaired Dirac-dual Yukawa density

The historical Stage-9 matter density used a cross-chiral Dirac matrix that
fails the already fixed finite Spin representation.  This module installs
the replacement generated in the Dirac-dual jurisdiction into the actual
Stage-9 frame-relative point-field consumer, then proves both gauge-chart
descent and arbitrary pointwise local-Spin invariance.

No root action is changed here.  The operator producer remains in the
Dirac-dual jurisdiction module; these declarations are its frame-relative
consumer/readout and covariance transporter, needed before the unique
form-native action epoch can be reopened.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualYukawaLocalSpinDensity

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracKineticLocalSpinConnection
open StageNineDiracKineticLocalSpinDensity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalBundle
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineSpinMatterBundle
open SU7ExteriorBreakingYukawa

open scoped MatrixGroups

noncomputable section

set_option autoImplicit false

/-- Frame-relative repaired Yukawa vector generated from the current scalar
and matter fields.  The barred-left carrier remains the independent dual and
is therefore not inserted into this vector operator. -/
def generatedContinuumDiracDualYukawaVector
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField) :
    DiracExteriorMatterCarrier :=
  diracDualRightChiralYukawaAction
      (scalarCoordinateEquiv.symm
        (scalarFrameRelativeCoordinates source chart point field.scalar))
    (matterFrameRelative source chart point field.matter)

/-- Densitized real Yukawa coefficient for the independent Dirac dual. -/
def generatedDensitizedContinuumDiracDualYukawaDensity
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField) : ℝ :=
  generatedVolumeDensity field *
    (matterDualFrameRelative source chart point field.conjugateMatter
      (generatedContinuumDiracDualYukawaVector
        source chart point field)).re

/-- The repaired Yukawa vector descends through the already generated
internal gauge chart because all three of its inputs are reduced to the same
source-owned frame. -/
theorem generatedContinuumDiracDualYukawaVector_overlap
    (source : SmoothUnifiedSource)
    (initial terminal : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField) :
    generatedContinuumDiracDualYukawaVector source terminal point
        (transportContinuumPointField source initial terminal point field) =
      generatedContinuumDiracDualYukawaVector source initial point field := by
  have scalarEquality :
      scalarFrameRelativeCoordinates source terminal point
          (transportContinuumPointField source initial terminal point
            field).scalar =
        scalarFrameRelativeCoordinates source initial point field.scalar :=
    scalarFrameRelativeCoordinates_overlap source initial terminal point
      field.scalar
  have matterEquality :
      matterFrameRelative source terminal point
          (transportContinuumPointField source initial terminal point
            field).matter =
        matterFrameRelative source initial point field.matter :=
    matterFrameRelative_overlap source initial terminal point field.matter
  unfold generatedContinuumDiracDualYukawaVector
  rw [scalarEquality, matterEquality]

/-- The repaired densitized Yukawa coefficient has the same exact gauge-chart
descent as the rest of the form-native action. -/
theorem generatedDensitizedContinuumDiracDualYukawaDensity_overlap
    (source : SmoothUnifiedSource)
    (initial terminal : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField) :
    generatedDensitizedContinuumDiracDualYukawaDensity source terminal point
        (transportContinuumPointField source initial terminal point field) =
      generatedDensitizedContinuumDiracDualYukawaDensity source initial point
        field := by
  have dualEquality :
      matterDualFrameRelative source terminal point
          (transportContinuumPointField source initial terminal point
            field).conjugateMatter =
        matterDualFrameRelative source initial point field.conjugateMatter :=
    matterDualFrameRelative_overlap source initial terminal point
      field.conjugateMatter
  have vectorEquality :=
    generatedContinuumDiracDualYukawaVector_overlap source initial terminal
      point field
  unfold generatedDensitizedContinuumDiracDualYukawaDensity
  rw [dualEquality, vectorEquality]
  rfl

/-- The actual point-field Yukawa vector intertwines the finite Spin action
chosen by the primitive local-Spin operator. -/
theorem generatedContinuumDiracDualYukawaVector_localSpin_covariant
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    generatedContinuumDiracDualYukawaVector source chart point
        (toContinuumPointField
          (localSpinDiracKineticAction spinField configuration) point) =
      spinDiracMatterRepresentation (spinField point)
        (generatedContinuumDiracDualYukawaVector source chart point
          (toContinuumPointField configuration point)) := by
  have scalarEquality :
      scalarFrameRelativeCoordinates source chart point
          (toContinuumPointField
            (localSpinDiracKineticAction spinField configuration)
            point).scalar =
        scalarFrameRelativeCoordinates source chart point
          (toContinuumPointField configuration point).scalar := by
    rfl
  have matterEquality :
      matterFrameRelative source chart point
          (toContinuumPointField
            (localSpinDiracKineticAction spinField configuration)
            point).matter =
        spinDiracMatterRepresentation (spinField point)
          (matterFrameRelative source chart point
            (toContinuumPointField configuration point).matter) := by
    change
      matterFrameRelative source chart point
          (spinDiracMatterRepresentation (spinField point)
            (configuration.matter point)) = _
    exact matterFrameRelative_spin_covariant source chart point
      (spinField point) (configuration.matter point)
  unfold generatedContinuumDiracDualYukawaVector
  rw [scalarEquality, matterEquality]
  exact LinearMap.congr_fun
    (diracDualRightChiralYukawaAction_spin_equivariant
      (spinField point)
      (scalarCoordinateEquiv.symm
        (scalarFrameRelativeCoordinates source chart point
          (toContinuumPointField configuration point).scalar)))
    (matterFrameRelative source chart point
      (toContinuumPointField configuration point).matter)

/-- Root-ready algebraic Yukawa closure: the same primitive local action
transports the coframe volume, matter, and inverse dual, so the repaired
densitized coefficient is pointwise invariant without any smoothness or
covariance receipt. -/
theorem
    generatedDensitizedContinuumDiracDualYukawaDensity_localSpin_invariant
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    generatedDensitizedContinuumDiracDualYukawaDensity source chart point
        (toContinuumPointField
          (localSpinDiracKineticAction spinField configuration) point) =
      generatedDensitizedContinuumDiracDualYukawaDensity source chart point
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
  unfold generatedDensitizedContinuumDiracDualYukawaDensity
  rw [generatedVolumeDensity_localSpinDiracKineticAction]
  rw [generatedContinuumDiracDualYukawaVector_localSpin_covariant]
  rw [conjugateEquality]
  rw [matterDualFrameRelative_spin_evaluation_invariant]
  simp only [toContinuumPointField]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualYukawaLocalSpinDensity
