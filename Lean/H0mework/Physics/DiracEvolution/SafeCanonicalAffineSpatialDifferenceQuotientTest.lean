import H0mework.Physics.DiracEvolution.SafeCanonicalAffineInteriorFirstJetActionLaw
import H0mework.Physics.DiracEvolution.SafeCanonicalAffineVolterraRieszActualization
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Group.Measure

/-!
# Fixed canonical affine spatial difference-quotient tests

The canonical Volterra output is already a source-generated spatial L²
field at every source time.  This module zero-extends one such value, takes
its exact whole-space translation difference quotient, and regularizes that
quotient into an admissible interior first-jet action test.

The constructor does not create a new solution or actual.  The cutoff and
bump are test data; the tested field is the existing canonical physical
output.  No residual, desired derivative, closedness, or regularity
certificate enters the output producer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineSpatialDifferenceQuotientTest

open Filter MeasureTheory Set
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineInteriorFirstJetActionLaw
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineVolterraRieszActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyEstimate
open StageNineDiracMatterSpatialEnergyBalance
open StageNineHolonomicField
open scoped ComplexOrder Convolution ENNReal Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

local instance canonicalDifferenceQuotientTwoNeTop :
    Fact ((2 : ℝ≥0∞) ≠ ⊤) :=
  ⟨by norm_num⟩

private def wholeSpatialTranslateL2
    (shift : DiracMatterSpatialCoordinates)
    (field : Lp MatterCoordinateCarrier 2
      (volume : Measure DiracMatterSpatialCoordinates)) :
    Lp MatterCoordinateCarrier 2
      (volume : Measure DiracMatterSpatialCoordinates) :=
  DomAddAct.mk shift +ᵥ field

private theorem wholeSpatialTranslateL2_norm
    (shift : DiracMatterSpatialCoordinates)
    (field : Lp MatterCoordinateCarrier 2
      (volume : Measure DiracMatterSpatialCoordinates)) :
    ‖wholeSpatialTranslateL2 shift field‖ = ‖field‖ :=
  DomAddAct.norm_vadd_Lp (DomAddAct.mk shift) field

/-- Zero extension of one physical box value to the whole spatial carrier. -/
def canonicalAffineSpatialZeroExtension
    {a b : DiracMatterSpatialCoordinates}
    (field : CauchySafeMatterSpatialL2 a b) :
    DiracMatterSpatialCoordinates → MatterCoordinateCarrier :=
  (Icc a b).indicator fun space ↦ field space

theorem canonicalAffineSpatialZeroExtension_memLp
    {a b : DiracMatterSpatialCoordinates}
    (field : CauchySafeMatterSpatialL2 a b) :
    MemLp (canonicalAffineSpatialZeroExtension field) 2
      (volume : Measure DiracMatterSpatialCoordinates) := by
  rw [canonicalAffineSpatialZeroExtension,
    memLp_indicator_iff_restrict measurableSet_Icc]
  exact Lp.memLp field

/-- Whole-space L² realization of the canonical zero extension. -/
def canonicalAffineSpatialZeroExtensionL2
    {a b : DiracMatterSpatialCoordinates}
    (field : CauchySafeMatterSpatialL2 a b) :
    Lp MatterCoordinateCarrier 2
      (volume : Measure DiracMatterSpatialCoordinates) :=
  (canonicalAffineSpatialZeroExtension_memLp field).toLp
    (canonicalAffineSpatialZeroExtension field)

theorem canonicalAffineSpatialZeroExtensionL2_coe_ae
    {a b : DiracMatterSpatialCoordinates}
    (field : CauchySafeMatterSpatialL2 a b) :
    canonicalAffineSpatialZeroExtensionL2 field =ᵐ[volume]
      canonicalAffineSpatialZeroExtension field :=
  (canonicalAffineSpatialZeroExtension_memLp field).coeFn_toLp

theorem canonicalAffineSpatialZeroExtensionL2_norm
    {a b : DiracMatterSpatialCoordinates}
    (field : CauchySafeMatterSpatialL2 a b) :
    ‖canonicalAffineSpatialZeroExtensionL2 field‖ = ‖field‖ := by
  rw [canonicalAffineSpatialZeroExtensionL2, Lp.norm_toLp,
    canonicalAffineSpatialZeroExtension,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc]
  exact (Lp.norm_def field).symm

/-- Exact whole-space translation difference quotient of one canonical box
value.  The scale is explicit so both finite differences and 1/h quotients
use the same carrier. -/
def canonicalAffineSpatialDifferenceQuotientL2
    {a b : DiracMatterSpatialCoordinates}
    (shift : DiracMatterSpatialCoordinates)
    (scale : ℝ)
    (field : CauchySafeMatterSpatialL2 a b) :
    Lp MatterCoordinateCarrier 2
      (volume : Measure DiracMatterSpatialCoordinates) :=
  scale •
    (wholeSpatialTranslateL2 shift
        (canonicalAffineSpatialZeroExtensionL2 field) -
      canonicalAffineSpatialZeroExtensionL2 field)

theorem canonicalAffineSpatialDifferenceQuotientL2_coe_ae
    {a b : DiracMatterSpatialCoordinates}
    (shift : DiracMatterSpatialCoordinates)
    (scale : ℝ)
    (field : CauchySafeMatterSpatialL2 a b) :
    canonicalAffineSpatialDifferenceQuotientL2 shift scale field =ᵐ[volume]
      fun space ↦ scale •
        (canonicalAffineSpatialZeroExtension field (shift + space) -
          canonicalAffineSpatialZeroExtension field space) := by
  let extension := canonicalAffineSpatialZeroExtensionL2 field
  have scaledRead := Lp.coeFn_smul scale
    (wholeSpatialTranslateL2 shift extension - extension)
  have differenceRead := Lp.coeFn_sub
    (wholeSpatialTranslateL2 shift extension) extension
  have translationRead :=
    DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk shift) extension
  have extensionRead : extension =ᵐ[volume]
      canonicalAffineSpatialZeroExtension field :=
    canonicalAffineSpatialZeroExtensionL2_coe_ae field
  have shiftedExtensionRead :
      (fun space ↦ extension (shift + space)) =ᵐ[volume]
        fun space ↦ canonicalAffineSpatialZeroExtension field
          (shift + space) := by
    exact extensionRead.comp_tendsto
      (measurePreserving_add_left volume shift
        ).quasiMeasurePreserving.tendsto_ae
  filter_upwards [scaledRead, differenceRead, translationRead,
    extensionRead, shiftedExtensionRead] with space scaledEq differenceEq
      translationEq extensionEq shiftedExtensionEq
  rw [canonicalAffineSpatialDifferenceQuotientL2, scaledEq]
  change scale •
      ((wholeSpatialTranslateL2 shift extension - extension) space) = _
  rw [differenceEq]
  change scale •
      ((DomAddAct.mk shift +ᵥ extension) space - extension space) = _
  rw [translationEq]
  change scale • (extension (shift + space) - extension space) = _
  rw [shiftedExtensionEq, extensionEq]

theorem canonicalAffineSpatialDifferenceQuotientL2_norm_le
    {a b : DiracMatterSpatialCoordinates}
    (shift : DiracMatterSpatialCoordinates)
    (scale : ℝ)
    (field : CauchySafeMatterSpatialL2 a b) :
    ‖canonicalAffineSpatialDifferenceQuotientL2 shift scale field‖ ≤
      |scale| * (2 * ‖field‖) := by
  rw [canonicalAffineSpatialDifferenceQuotientL2, norm_smul,
    Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg scale)
  calc
    ‖wholeSpatialTranslateL2 shift
          (canonicalAffineSpatialZeroExtensionL2 field) -
        canonicalAffineSpatialZeroExtensionL2 field‖ ≤
        ‖wholeSpatialTranslateL2 shift
          (canonicalAffineSpatialZeroExtensionL2 field)‖ +
          ‖canonicalAffineSpatialZeroExtensionL2 field‖ :=
      norm_sub_le _ _
    _ = 2 * ‖field‖ := by
      rw [wholeSpatialTranslateL2_norm,
        canonicalAffineSpatialZeroExtensionL2_norm]
      ring

def wholeSpatialMollification
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (field : Lp MatterCoordinateCarrier 2
      (volume : Measure DiracMatterSpatialCoordinates)) :
    DiracMatterSpatialCoordinates → MatterCoordinateCarrier :=
  (bump.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
    fun space ↦ field space

theorem wholeSpatialMollification_contDiff
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (field : Lp MatterCoordinateCarrier 2
      (volume : Measure DiracMatterSpatialCoordinates)) :
    ContDiff ℝ (⊤ : ℕ∞) (wholeSpatialMollification bump field) := by
  exact bump.hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) bump.contDiff_normed
      ((Lp.memLp field).locallyIntegrable (by norm_num))

/-- A cutoff turns the smooth whole-space quotient into an exact interior
first-jet test on the original canonical box. -/
def canonicalAffineCutoffMollifiedDifferenceQuotientTest
    {a b : DiracMatterSpatialCoordinates}
    (cutoff : DiracMatterSpatialCoordinates → ℝ)
    (cutoffCompact : HasCompactSupport cutoff)
    (cutoffSmooth : ContDiff ℝ (⊤ : ℕ∞) cutoff)
    (cutoffInterior : ∀ space,
      ¬ DiracMatterSpatialBoxInterior a b space → cutoff space = 0)
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (shift : DiracMatterSpatialCoordinates)
    (scale : ℝ)
    (field : CauchySafeMatterSpatialL2 a b) :
    CauchySafeMatterCanonicalInteriorSmoothTest a b := by
  let testFunction := fun space ↦ cutoff space •
    wholeSpatialMollification bump
      (canonicalAffineSpatialDifferenceQuotientL2 shift scale field) space
  refine ⟨⟨testFunction, ?_⟩, ?_⟩
  · change HasCompactSupport testFunction ∧
      ContDiff ℝ (⊤ : ℕ∞) testFunction
    exact ⟨cutoffCompact.smul_right,
      cutoffSmooth.smul
        (wholeSpatialMollification_contDiff bump
          (canonicalAffineSpatialDifferenceQuotientL2 shift scale field))⟩
  · intro space outside
    change cutoff space •
      wholeSpatialMollification bump
        (canonicalAffineSpatialDifferenceQuotientL2 shift scale field)
          space = 0
    rw [cutoffInterior space outside, zero_smul]

/-- The exact canonical Volterra output may be used as its own spatial
difference-quotient action test after canonical L² zero extension,
regularization, and an interior cutoff. -/
theorem
    canonicalAffineVolterraPhysicalRepresentative_weightedActionLaw_of_differenceQuotientTest
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (sourceTime : Icc 0 timeEnd)
    (shift : DiracMatterSpatialCoordinates)
    (scale : ℝ)
    (cutoff : DiracMatterSpatialCoordinates → ℝ)
    (cutoffCompact : HasCompactSupport cutoff)
    (cutoffSmooth : ContDiff ℝ (⊤ : ℕ∞) cutoff)
    (cutoffInterior : ∀ space,
      ¬ DiracMatterSpatialBoxInterior a b space → cutoff space = 0)
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (weightZero : weight 0 = 0)
    (weightEndZero : weight timeEnd = 0) :
    canonicalInteriorFirstJetWeightedActionValue
        timeEnd timePositive.le a b boxOrder weight
        (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b
          (canonicalAffineCutoffMollifiedDifferenceQuotientTest
            cutoff cutoffCompact cutoffSmooth cutoffInterior bump shift scale
              (canonicalAffineVolterraPhysicalRepresentative
                timeEnd timePositive a b boxOrder sourceTime))) = 0 := by
  exact
    canonicalAffinePhysicalTimeL2Output_weightedActionLaw_of_interiorSmoothTest
      timeEnd timePositive.le a b boxOrder
      (canonicalAffineCutoffMollifiedDifferenceQuotientTest
        cutoff cutoffCompact cutoffSmooth cutoffInterior bump shift scale
          (canonicalAffineVolterraPhysicalRepresentative
            timeEnd timePositive a b boxOrder sourceTime))
      weight weightRegular weightZero weightEndZero

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineSpatialDifferenceQuotientTest
