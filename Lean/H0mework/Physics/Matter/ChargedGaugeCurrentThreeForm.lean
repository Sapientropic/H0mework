import H0mework.Physics.GaugeAction.P286GaugeConnectionLocalVariation
import H0mework.Physics.GaugeAction.TopologicalP286GaugeThreeFormDuality

/-!
# Form-native charged P286 gauge three-form

The scalar and Dirac legs of the authoritative form-native connection
variation generate one pointwise linear functional on the complete P286
connection one-form carrier.  This module retains the live matter volume and
uses the canonical W13 linear equivalence to obtain the unique action-signed
three-form representative.

The represented coefficient enters the action with a plus sign.  A physical
current convention `J := -S_charged` is therefore deferred until the complete
geometric first variation fixes the equation.  No source slot, normalization,
branch selector, current receipt, old momentum, weak equation, stationarity,
or target solution is consumed here.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineFormNativeChargedGaugeCurrentThreeForm

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeP286GaugeConnectionLocalVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineTopologicalFourFormPairing
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

/-! ## Pointwise action-generated charged dual -/

def pointwiseP286GaugeConnectionMotherVariation
    (direction : P286GaugeOneForm) (formDirection : LorentzianIndex) :
    SU7MotherLieMatrix :=
  p286LieBlockEmbed (p286CoordinateEquiv.symm (direction formDirection))

def pointwiseScalarP286GaugeConnectionVariation
    (field : StageNineContinuumPointField)
    (direction : P286GaugeOneForm) :
    LorentzianIndex → ScalarCoordinateCarrier :=
  fun formDirection =>
    scalarMotherLieAction
      (pointwiseP286GaugeConnectionMotherVariation direction formDirection)
      field.scalar

def pointwiseMatterP286GaugeConnectionVariation
    (field : StageNineContinuumPointField)
    (direction : P286GaugeOneForm) :
    LorentzianIndex → DiracExteriorMatterCarrier :=
  fun formDirection =>
    diracExteriorMotherLieAction
      (pointwiseP286GaugeConnectionMotherVariation direction formDirection)
      field.matter

theorem pointwiseP286GaugeConnectionMotherVariation_add
    (first second : P286GaugeOneForm) (formDirection : LorentzianIndex) :
    pointwiseP286GaugeConnectionMotherVariation (first + second)
        formDirection =
      pointwiseP286GaugeConnectionMotherVariation first formDirection +
        pointwiseP286GaugeConnectionMotherVariation second formDirection := by
  unfold pointwiseP286GaugeConnectionMotherVariation
  rw [Pi.add_apply, p286CoordinateEquiv.symm.map_add,
    p286LieBlockEmbed_add]

theorem pointwiseP286GaugeConnectionMotherVariation_smul
    (parameter : ℝ) (direction : P286GaugeOneForm)
    (formDirection : LorentzianIndex) :
    pointwiseP286GaugeConnectionMotherVariation (parameter • direction)
        formDirection =
      parameter •
        pointwiseP286GaugeConnectionMotherVariation direction formDirection := by
  unfold pointwiseP286GaugeConnectionMotherVariation
  rw [Pi.smul_apply, p286CoordinateEquiv.symm.map_smul,
    p286LieBlockEmbed_real_smul]

theorem pointwiseScalarP286GaugeConnectionVariation_add
    (field : StageNineContinuumPointField)
    (first second : P286GaugeOneForm) :
    pointwiseScalarP286GaugeConnectionVariation field (first + second) =
      pointwiseScalarP286GaugeConnectionVariation field first +
        pointwiseScalarP286GaugeConnectionVariation field second := by
  funext formDirection
  unfold pointwiseScalarP286GaugeConnectionVariation
  rw [pointwiseP286GaugeConnectionMotherVariation_add,
    scalarMotherLieAction_add]
  rfl

theorem pointwiseScalarP286GaugeConnectionVariation_smul
    (field : StageNineContinuumPointField) (parameter : ℝ)
    (direction : P286GaugeOneForm) :
    pointwiseScalarP286GaugeConnectionVariation field
        (parameter • direction) =
      parameter •
        pointwiseScalarP286GaugeConnectionVariation field direction := by
  funext formDirection
  unfold pointwiseScalarP286GaugeConnectionVariation
  rw [pointwiseP286GaugeConnectionMotherVariation_smul,
    scalarMotherLieAction_real_smul]
  rfl

theorem pointwiseMatterP286GaugeConnectionVariation_add
    (field : StageNineContinuumPointField)
    (first second : P286GaugeOneForm) :
    pointwiseMatterP286GaugeConnectionVariation field (first + second) =
      pointwiseMatterP286GaugeConnectionVariation field first +
        pointwiseMatterP286GaugeConnectionVariation field second := by
  funext formDirection
  unfold pointwiseMatterP286GaugeConnectionVariation
  rw [pointwiseP286GaugeConnectionMotherVariation_add,
    diracExteriorMotherLieAction_add]
  rfl

theorem pointwiseMatterP286GaugeConnectionVariation_smul
    (field : StageNineContinuumPointField) (parameter : ℝ)
    (direction : P286GaugeOneForm) :
    pointwiseMatterP286GaugeConnectionVariation field
        (parameter • direction) =
      parameter •
        pointwiseMatterP286GaugeConnectionVariation field direction := by
  funext formDirection
  unfold pointwiseMatterP286GaugeConnectionVariation
  rw [pointwiseP286GaugeConnectionMotherVariation_smul,
    diracExteriorMotherLieAction_real_smul]
  rfl

private theorem scalarGaugeConnectionKineticFirstVariationDensity_add_local
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (first second : LorentzianIndex → ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity source chart point field
        (first + second) =
      scalarGaugeConnectionKineticFirstVariationDensity source chart point
          field first +
        scalarGaugeConnectionKineticFirstVariationDensity source chart point
          field second := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  rw [scalarFrameRelativeCovariantDerivative_add]
  simp only [Pi.add_apply, scalarCoordinatePairingRe_add_left,
    scalarCoordinatePairingRe_add_right]
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro firstDirection _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro secondDirection _
  ring

private theorem weightedDoubleSum_real_linear_local
    {First Second : Type*} [Fintype First] [Fintype Second]
    (weight left right : First → Second → ℝ) (parameter : ℝ) :
    (∑ first : First, ∑ second : Second,
      weight first second *
        (parameter * left first second + parameter * right first second)) =
      parameter *
        (∑ first : First, ∑ second : Second,
          weight first second *
            (left first second + right first second)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro second _
  ring

private theorem scalarGaugeConnectionKineticFirstVariationDensity_smul_local
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (parameter : ℝ)
    (variation : LorentzianIndex → ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity source chart point field
        (parameter • variation) =
      parameter *
        scalarGaugeConnectionKineticFirstVariationDensity source chart point
          field variation := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  rw [scalarFrameRelativeCovariantDerivative_real_smul]
  simp only [Pi.smul_apply,
    scalarCoordinatePairingRe_real_smul_left,
    scalarCoordinatePairingRe_real_smul_right]
  simp_rw [← Matrix.of_symm_apply]
  rw [weightedDoubleSum_real_linear_local]
  ring

private theorem matterGaugeConnectionFirstVariationDensity_add_local
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (first second : LorentzianIndex → DiracExteriorMatterCarrier) :
    matterGaugeConnectionFirstVariationDensity source chart point field
        (first + second) =
      matterGaugeConnectionFirstVariationDensity source chart point field
          first +
        matterGaugeConnectionFirstVariationDensity source chart point field
          second := by
  unfold matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector
  rw [matterGaugeKineticSum_add, smul_add, map_add]
  exact Complex.add_re _ _

private theorem matterGaugeConnectionFirstVariationDensity_smul_local
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (parameter : ℝ)
    (variation : LorentzianIndex → DiracExteriorMatterCarrier) :
    matterGaugeConnectionFirstVariationDensity source chart point field
        (parameter • variation) =
      parameter * matterGaugeConnectionFirstVariationDensity source chart
        point field variation := by
  unfold matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector
  rw [matterGaugeKineticSum_real_smul]
  have vectorEquality :
      Complex.I •
          (parameter • matterGaugeKineticSum source chart point field variation) =
        parameter •
          (Complex.I •
            matterGaugeKineticSum source chart point field variation) := by
    change Complex.I •
        ((parameter : ℂ) •
          matterGaugeKineticSum source chart point field variation) =
      (parameter : ℂ) •
        (Complex.I •
          matterGaugeKineticSum source chart point field variation)
    module
  rw [vectorEquality, matterDualFrameRelative_real_smul]
  simp [Complex.mul_re]

/-- Exact scalar-plus-Dirac coefficient as it occurs in the form-native
mother action. -/
def formNativeChargedGaugeFirstCoefficient
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (direction : P286GaugeOneForm) : ℝ :=
  generatedVolumeDensity field *
    (scalarGaugeConnectionKineticFirstVariationDensity source chart point
        field (pointwiseScalarP286GaugeConnectionVariation field direction) +
      matterGaugeConnectionFirstVariationDensity source chart point field
        (pointwiseMatterP286GaugeConnectionVariation field direction))

theorem formNativeChargedGaugeFirstCoefficient_add
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (first second : P286GaugeOneForm) :
    formNativeChargedGaugeFirstCoefficient source chart point field
        (first + second) =
      formNativeChargedGaugeFirstCoefficient source chart point field first +
        formNativeChargedGaugeFirstCoefficient source chart point field
          second := by
  unfold formNativeChargedGaugeFirstCoefficient
  rw [pointwiseScalarP286GaugeConnectionVariation_add,
    pointwiseMatterP286GaugeConnectionVariation_add,
    scalarGaugeConnectionKineticFirstVariationDensity_add_local,
    matterGaugeConnectionFirstVariationDensity_add_local]
  ring

theorem formNativeChargedGaugeFirstCoefficient_smul
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (parameter : ℝ) (direction : P286GaugeOneForm) :
    formNativeChargedGaugeFirstCoefficient source chart point field
        (parameter • direction) =
      parameter *
        formNativeChargedGaugeFirstCoefficient source chart point field
          direction := by
  unfold formNativeChargedGaugeFirstCoefficient
  rw [pointwiseScalarP286GaugeConnectionVariation_smul,
    pointwiseMatterP286GaugeConnectionVariation_smul,
    scalarGaugeConnectionKineticFirstVariationDensity_smul_local,
    matterGaugeConnectionFirstVariationDensity_smul_local]
  ring

def formNativeChargedGaugeFirstLinearMap
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) :
    Module.Dual ℝ P286GaugeOneForm where
  toFun := formNativeChargedGaugeFirstCoefficient source chart point field
  map_add' :=
    formNativeChargedGaugeFirstCoefficient_add source chart point field
  map_smul' := by
    intro parameter direction
    simpa only [RingHom.id_apply, smul_eq_mul] using
      formNativeChargedGaugeFirstCoefficient_smul source chart point field
        parameter direction

@[simp] theorem formNativeChargedGaugeFirstLinearMap_apply
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (direction : P286GaugeOneForm) :
    formNativeChargedGaugeFirstLinearMap source chart point field direction =
      formNativeChargedGaugeFirstCoefficient source chart point field
        direction :=
  rfl

/-! ## Same-occurrence provenance seams -/

theorem pointwiseScalarP286GaugeConnectionVariation_actual
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm) (point : BasePoint) :
    pointwiseScalarP286GaugeConnectionVariation
        (toContinuumPointField configuration point) (variation point) =
      holonomicScalarGaugeConnectionVariation configuration variation point := by
  funext formDirection
  rfl

theorem pointwiseMatterP286GaugeConnectionVariation_actual
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm) (point : BasePoint) :
    pointwiseMatterP286GaugeConnectionVariation
        (toContinuumPointField configuration point) (variation point) =
      holonomicMatterGaugeConnectionVariation configuration variation point := by
  funext formDirection
  rfl

/-- The active local first coefficient reads exactly this charged covector
from the same primitive connection occurrence. -/
theorem holonomicFormNativeP286GaugeConnectionFirstVariationDensity_eq_charged
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → P286GaugeOneForm) (point : BasePoint) :
    holonomicFormNativeP286GaugeConnectionFirstVariationDensity source chart
        configuration variation point =
      generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
          (holonomicP286GaugeAuxiliaryCoordinate configuration point)
          (p286GaugeConnectionLinearCurvatureVariation configuration variation
            point) +
        formNativeChargedGaugeFirstCoefficient source chart point
          (toContinuumPointField configuration point) (variation point) := by
  unfold holonomicFormNativeP286GaugeConnectionFirstVariationDensity
    formNativeP286GaugeConnectionFirstVariationDensity
    formNativeChargedGaugeFirstCoefficient
  rw [formNativeP286GaugeConnectionBFFirstVariationDensity_eq_coordinate,
    pointwiseScalarP286GaugeConnectionVariation_actual,
    pointwiseMatterP286GaugeConnectionVariation_actual]
  rfl

/-! ## Unique W13 representative -/

/-- Action-signed charged contribution generated by the complete pointwise
scalar-plus-Dirac covector. -/
def formNativeChargedGaugeThreeForm
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) :
    P286GaugeThreeForm :=
  p286GaugeThreeFormOfDual
    (formNativeChargedGaugeFirstLinearMap source chart point field)

/-- W13 evaluates the generated three-form to the exact charged action
coefficient on every complete P286 one-form direction. -/
theorem formNativeChargedGaugeThreeForm_evaluation
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (direction : P286GaugeOneForm) :
    p286GaugeOneFormThreeFormWedgeCoefficient direction
        (formNativeChargedGaugeThreeForm source chart point field) =
      formNativeChargedGaugeFirstCoefficient source chart point field
        direction := by
  unfold formNativeChargedGaugeThreeForm
  exact p286GaugeThreeFormOfDual_evaluation _ _

theorem formNativeChargedGaugeThreeForm_unique
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (candidate : P286GaugeThreeForm)
    (represents : ∀ direction : P286GaugeOneForm,
      p286GaugeOneFormThreeFormWedgeCoefficient direction candidate =
        formNativeChargedGaugeFirstCoefficient source chart point field
          direction) :
    candidate = formNativeChargedGaugeThreeForm source chart point field := by
  unfold formNativeChargedGaugeThreeForm
  exact p286GaugeThreeFormOfDual_unique _ candidate represents

theorem formNativeChargedGaugeThreeForm_eq_zero_iff
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) :
    formNativeChargedGaugeThreeForm source chart point field = 0 ↔
      formNativeChargedGaugeFirstLinearMap source chart point field = 0 := by
  unfold formNativeChargedGaugeThreeForm p286GaugeThreeFormOfDual
  constructor
  · intro formZero
    apply p286GaugeThreeFormWedgeEquiv.symm.injective
    simpa using formZero
  · intro dualZero
    rw [dualZero]
    exact map_zero p286GaugeThreeFormWedgeEquiv.symm

/-- Faithful zero fiber: no charged action response can disappear in the W13
carrier, and no witness or coordinate support is chosen. -/
theorem formNativeChargedGaugeThreeForm_eq_zero_iff_all
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) :
    formNativeChargedGaugeThreeForm source chart point field = 0 ↔
      ∀ direction : P286GaugeOneForm,
        formNativeChargedGaugeFirstCoefficient source chart point field
          direction = 0 := by
  rw [formNativeChargedGaugeThreeForm_eq_zero_iff]
  constructor
  · intro dualZero direction
    have evaluated := DFunLike.congr_fun dualZero direction
    simpa using evaluated
  · intro allZero
    apply LinearMap.ext
    intro direction
    simp [allZero direction]

end

end
  SaturationMonoid.PhysicsCore.StageNineFormNativeChargedGaugeCurrentThreeForm
