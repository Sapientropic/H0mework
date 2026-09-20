import H0mework.Physics.Exterior.GlobalIntegratedAction

/-!
# Formulation-neutral matter covariant-derivative affine law

The Dirac--Yukawa density is affine in the matter covariant-derivative slot.
This module isolates that representation identity from every gravity or gauge
action formulation.  It changes only the derived covariant-derivative readout
of one continuum point field; no primitive connection, source datum, action,
stationarity certificate, or equation is accepted here.

Both the historical gauge/Lorentz action modules and the form-native action
epoch may consume this seam without importing one another's action law.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineMatterCovariantDerivativeAffine

open ProofFreeRicherAnholonomicSource
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open DiracExteriorMatterAction
open SU7ExteriorBreakingYukawa

noncomputable section

set_option autoImplicit false

/-- Readout update of the matter covariant-derivative slot only. -/
def withMatterCovariantDerivative
    (field : StageNineContinuumPointField)
    (matterDerivative : LorentzianIndex -> DiracExteriorMatterCarrier) :
    StageNineContinuumPointField :=
  { field with matterCovariantDerivative := matterDerivative }

@[simp] theorem withMatterCovariantDerivative_coframe
    (field : StageNineContinuumPointField)
    (matterDerivative : LorentzianIndex -> DiracExteriorMatterCarrier) :
    (withMatterCovariantDerivative field matterDerivative).coframe =
      field.coframe :=
  rfl

@[simp] theorem withMatterCovariantDerivative_volume
    (field : StageNineContinuumPointField)
    (matterDerivative : LorentzianIndex -> DiracExteriorMatterCarrier) :
    generatedVolumeDensity
        (withMatterCovariantDerivative field matterDerivative) =
      generatedVolumeDensity field :=
  rfl

theorem matterFrameRelative_add
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (first second : DiracExteriorMatterCarrier) :
    matterFrameRelative source chart point (first + second) =
      matterFrameRelative source chart point first +
        matterFrameRelative source chart point second := by
  unfold matterFrameRelative
  exact map_add _ first second

theorem matterFrameRelative_real_smul
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (parameter : ℝ)
    (matter : DiracExteriorMatterCarrier) :
    matterFrameRelative source chart point (parameter • matter) =
      parameter • matterFrameRelative source chart point matter := by
  unfold matterFrameRelative
  change
    (diracExteriorMatterGaugeRepresentation
      (generatedScalarFrame source chart point)⁻¹)
        ((parameter : ℂ) • matter) =
      (parameter : ℂ) •
        (diracExteriorMatterGaugeRepresentation
          (generatedScalarFrame source chart point)⁻¹) matter
  exact map_smul _ _ _

theorem matterDerivativeFrameRelative_add
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint)
    (first second : LorentzianIndex -> DiracExteriorMatterCarrier) :
    matterDerivativeFrameRelative source chart point (first + second) =
      matterDerivativeFrameRelative source chart point first +
        matterDerivativeFrameRelative source chart point second := by
  funext direction
  exact matterFrameRelative_add source chart point _ _

theorem matterDerivativeFrameRelative_real_smul
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (parameter : ℝ)
    (derivative : LorentzianIndex -> DiracExteriorMatterCarrier) :
    matterDerivativeFrameRelative source chart point
        (parameter • derivative) =
      parameter • matterDerivativeFrameRelative source chart point derivative := by
  funext direction
  exact matterFrameRelative_real_smul source chart point parameter _

theorem matterDerivativeFrameRelative_smul
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (parameter : ℂ)
    (derivative : LorentzianIndex -> DiracExteriorMatterCarrier) :
    matterDerivativeFrameRelative source chart point
        (parameter • derivative) =
      parameter • matterDerivativeFrameRelative source chart point derivative := by
  funext direction
  unfold matterDerivativeFrameRelative matterFrameRelative
  exact
    (diracExteriorMatterGaugeRepresentation
      (generatedScalarFrame source chart point)⁻¹).map_smul
        parameter (derivative direction)

/-- The kinetic part of the matter vector evaluated on an arbitrary
covariant-derivative increment. -/
def matterCovariantDerivativeKineticSum
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (derivative : LorentzianIndex -> DiracExteriorMatterCarrier) :
    DiracExteriorMatterCarrier :=
  ∑ direction : LorentzianIndex,
    diracMatrixMatterAction
      (inverseCoframeDiracGamma
        { coframe := field.coframe, derivative := 0 } direction)
      (matterDerivativeFrameRelative source chart point derivative direction)

theorem matterCovariantDerivativeKineticSum_add
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (first second : LorentzianIndex -> DiracExteriorMatterCarrier) :
    matterCovariantDerivativeKineticSum source chart point field
        (first + second) =
      matterCovariantDerivativeKineticSum source chart point field first +
        matterCovariantDerivativeKineticSum source chart point field second := by
  unfold matterCovariantDerivativeKineticSum
  simp only [matterDerivativeFrameRelative_add, Pi.add_apply, map_add,
    Finset.sum_add_distrib]

theorem matterCovariantDerivativeKineticSum_real_smul
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (parameter : ℝ)
    (derivative : LorentzianIndex -> DiracExteriorMatterCarrier) :
    matterCovariantDerivativeKineticSum source chart point field
        (parameter • derivative) =
      parameter • matterCovariantDerivativeKineticSum source chart point field
        derivative := by
  change
    matterCovariantDerivativeKineticSum source chart point field
        ((parameter : ℂ) • derivative) =
      (parameter : ℂ) •
        matterCovariantDerivativeKineticSum source chart point field derivative
  unfold matterCovariantDerivativeKineticSum
  simp only [matterDerivativeFrameRelative_smul, Pi.smul_apply, map_smul]
  rw [Finset.smul_sum]

theorem matterCovariantDerivativeKineticSum_smul
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (parameter : ℂ)
    (derivative : LorentzianIndex -> DiracExteriorMatterCarrier) :
    matterCovariantDerivativeKineticSum source chart point field
        (parameter • derivative) =
      parameter • matterCovariantDerivativeKineticSum source chart point field
        derivative := by
  unfold matterCovariantDerivativeKineticSum
  simp only [matterDerivativeFrameRelative_smul, Pi.smul_apply, map_smul]
  rw [Finset.smul_sum]

/-- Matter-vector response generated by a covariant-derivative increment. -/
def matterCovariantDerivativeVariationVector
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (variation : LorentzianIndex -> DiracExteriorMatterCarrier) :
    DiracExteriorMatterCarrier :=
  Complex.I •
    matterCovariantDerivativeKineticSum source chart point field variation

theorem matterCovariantDerivativeVariationVector_add
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (first second : LorentzianIndex -> DiracExteriorMatterCarrier) :
    matterCovariantDerivativeVariationVector source chart point field
        (first + second) =
      matterCovariantDerivativeVariationVector source chart point field first +
        matterCovariantDerivativeVariationVector source chart point field
          second := by
  unfold matterCovariantDerivativeVariationVector
  rw [matterCovariantDerivativeKineticSum_add, smul_add]

/-- Real local matter-density coefficient generated by the same increment. -/
def matterCovariantDerivativeFirstVariationDensity
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (variation : LorentzianIndex -> DiracExteriorMatterCarrier) : ℝ :=
  (matterDualFrameRelative source chart point field.conjugateMatter
    (matterCovariantDerivativeVariationVector source chart point field
      variation)).re

theorem matterCovariantDerivativeFirstVariationDensity_add
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (first second : LorentzianIndex -> DiracExteriorMatterCarrier) :
    matterCovariantDerivativeFirstVariationDensity source chart point field
        (first + second) =
      matterCovariantDerivativeFirstVariationDensity source chart point field
          first +
        matterCovariantDerivativeFirstVariationDensity source chart point field
          second := by
  unfold matterCovariantDerivativeFirstVariationDensity
  rw [matterCovariantDerivativeVariationVector_add, map_add]
  exact Complex.add_re _ _

theorem generatedContinuumMatterVector_withMatterCovariantDerivative_affine
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (variation : LorentzianIndex -> DiracExteriorMatterCarrier)
    (parameter : ℝ) :
    generatedContinuumMatterVector source chart point
        (withMatterCovariantDerivative field
          (field.matterCovariantDerivative + parameter • variation)) =
      generatedContinuumMatterVector source chart point field +
        parameter • matterCovariantDerivativeVariationVector
          source chart point field variation := by
  unfold generatedContinuumMatterVector
    matterCovariantDerivativeVariationVector
  let yukawa :=
    chiralExteriorYukawaAction
      (scalarCoordinateEquiv.symm
        (scalarFrameRelativeCoordinates source chart point field.scalar))
      (matterFrameRelative source chart point field.matter)
  change
    Complex.I •
          matterCovariantDerivativeKineticSum source chart point field
            (field.matterCovariantDerivative +
              (parameter : ℂ) • variation) +
        yukawa =
      (Complex.I •
          matterCovariantDerivativeKineticSum source chart point field
            field.matterCovariantDerivative + yukawa) +
        (parameter : ℂ) •
          (Complex.I •
            matterCovariantDerivativeKineticSum source chart point field
              variation)
  rw [matterCovariantDerivativeKineticSum_add,
    matterCovariantDerivativeKineticSum_smul]
  rw [smul_add]
  module

theorem matterDualFrameRelative_real_smul
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (parameter : ℝ) (matter : DiracExteriorMatterCarrier) :
    matterDualFrameRelative source chart point dual (parameter • matter) =
      (parameter : ℂ) *
        matterDualFrameRelative source chart point dual matter := by
  change
    matterDualFrameRelative source chart point dual
        ((parameter : ℂ) • matter) =
      (parameter : ℂ) •
        matterDualFrameRelative source chart point dual matter
  exact (matterDualFrameRelative source chart point dual).map_smul
    (parameter : ℂ) matter

/-- Exact affine law.  The coefficient is computed from the existing
coframe, matter, conjugate matter, source frame, and the supplied derivative
increment; it carries no independent physical parameter. -/
theorem generatedContinuumMatterDensity_withMatterCovariantDerivative_affine
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (variation : LorentzianIndex -> DiracExteriorMatterCarrier)
    (parameter : ℝ) :
    generatedContinuumMatterDensity source chart point
        (withMatterCovariantDerivative field
          (field.matterCovariantDerivative + parameter • variation)) =
      generatedContinuumMatterDensity source chart point field +
        parameter * matterCovariantDerivativeFirstVariationDensity
          source chart point field variation := by
  unfold generatedContinuumMatterDensity
    matterCovariantDerivativeFirstVariationDensity
  rw [generatedContinuumMatterVector_withMatterCovariantDerivative_affine]
  simp only [withMatterCovariantDerivative, map_add, Complex.add_re,
    matterDualFrameRelative_real_smul]
  simp [Complex.mul_re]

theorem matterCovariantDerivativeFirstVariationDensity_real_smul
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (parameter : ℝ)
    (variation : LorentzianIndex -> DiracExteriorMatterCarrier) :
    matterCovariantDerivativeFirstVariationDensity source chart point field
        (parameter • variation) =
      parameter * matterCovariantDerivativeFirstVariationDensity source chart
        point field variation := by
  unfold matterCovariantDerivativeFirstVariationDensity
    matterCovariantDerivativeVariationVector
  rw [matterCovariantDerivativeKineticSum_real_smul]
  have vectorEquality :
      Complex.I •
          (parameter • matterCovariantDerivativeKineticSum source chart point
            field variation) =
        parameter •
          (Complex.I • matterCovariantDerivativeKineticSum source chart point
            field variation) := by
    change Complex.I •
        ((parameter : ℂ) •
          matterCovariantDerivativeKineticSum source chart point field
            variation) =
      (parameter : ℂ) •
        (Complex.I • matterCovariantDerivativeKineticSum source chart point
          field variation)
    module
  rw [vectorEquality, matterDualFrameRelative_real_smul]
  simp [Complex.mul_re]

end

end SaturationMonoid.PhysicsCore.StageNineMatterCovariantDerivativeAffine
