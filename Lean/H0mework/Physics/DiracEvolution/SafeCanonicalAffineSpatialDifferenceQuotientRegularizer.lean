import H0mework.Physics.DiracEvolution.SafeCanonicalAffineSpatialDifferenceQuotientActionRead
import Mathlib.MeasureTheory.Function.Holder

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineSpatialDifferenceQuotientRegularizer

open MeasureTheory Set
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineSpatialDifferenceQuotientTest
open StageNineDiracMatterSpatialEnergyBalance
open StageNineHolonomicField
open scoped Convolution

noncomputable section

set_option autoImplicit false

private theorem canonicalAffineSpatialZeroExtension_add_ae
    {a b : DiracMatterSpatialCoordinates}
    (first second : CauchySafeMatterSpatialL2 a b) :
    canonicalAffineSpatialZeroExtension (first + second) =ᵐ[volume]
      canonicalAffineSpatialZeroExtension first +
        canonicalAffineSpatialZeroExtension second := by
  have indicatorRead :
      (Icc a b).indicator (fun space ↦ (first + second) space) =ᵐ[volume]
        (Icc a b).indicator (fun space ↦ first space + second space) :=
    (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Icc).mp
      (Lp.coeFn_add first second)
  filter_upwards [indicatorRead] with space read
  change (Icc a b).indicator (fun point ↦ (first + second) point) space =
    (Icc a b).indicator (fun point ↦ first point) space +
      (Icc a b).indicator (fun point ↦ second point) space
  rw [read]
  by_cases spaceMem : space ∈ Icc a b <;> simp [spaceMem]

private theorem canonicalAffineSpatialZeroExtension_smul_ae
    {a b : DiracMatterSpatialCoordinates}
    (parameter : ℝ)
    (field : CauchySafeMatterSpatialL2 a b) :
    canonicalAffineSpatialZeroExtension (parameter • field) =ᵐ[volume]
      parameter • canonicalAffineSpatialZeroExtension field := by
  have indicatorRead :
      (Icc a b).indicator (fun space ↦ (parameter • field) space) =ᵐ[volume]
        (Icc a b).indicator (fun space ↦ parameter • field space) :=
    (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Icc).mp
      (Lp.coeFn_smul parameter field)
  filter_upwards [indicatorRead] with space read
  change (Icc a b).indicator (fun point ↦ (parameter • field) point) space =
    parameter • (Icc a b).indicator (fun point ↦ field point) space
  rw [read]
  by_cases spaceMem : space ∈ Icc a b <;> simp [spaceMem]

/-- Linear zero extension from the canonical box into whole-space L². -/
def canonicalAffineSpatialZeroExtensionLinear
    (a b : DiracMatterSpatialCoordinates) :
    CauchySafeMatterSpatialL2 a b →ₗ[ℝ]
      Lp MatterCoordinateCarrier 2
        (volume : Measure DiracMatterSpatialCoordinates) where
  toFun := canonicalAffineSpatialZeroExtensionL2
  map_add' first second := by
    let firstMem := canonicalAffineSpatialZeroExtension_memLp first
    let secondMem := canonicalAffineSpatialZeroExtension_memLp second
    let totalMem := canonicalAffineSpatialZeroExtension_memLp (first + second)
    calc
      canonicalAffineSpatialZeroExtensionL2 (first + second) =
          (firstMem.add secondMem).toLp
            (canonicalAffineSpatialZeroExtension first +
              canonicalAffineSpatialZeroExtension second) := by
        exact MemLp.toLp_congr totalMem (firstMem.add secondMem)
          (canonicalAffineSpatialZeroExtension_add_ae first second)
      _ = canonicalAffineSpatialZeroExtensionL2 first +
          canonicalAffineSpatialZeroExtensionL2 second := by
        exact MemLp.toLp_add firstMem secondMem
  map_smul' parameter field := by
    let fieldMem := canonicalAffineSpatialZeroExtension_memLp field
    let totalMem := canonicalAffineSpatialZeroExtension_memLp
      (parameter • field)
    calc
      canonicalAffineSpatialZeroExtensionL2 (parameter • field) =
          (fieldMem.const_smul parameter).toLp
            (parameter • canonicalAffineSpatialZeroExtension field) := by
        exact MemLp.toLp_congr totalMem (fieldMem.const_smul parameter)
          (canonicalAffineSpatialZeroExtension_smul_ae parameter field)
      _ = parameter • canonicalAffineSpatialZeroExtensionL2 field := by
        exact MemLp.toLp_const_smul parameter fieldMem

/-- Zero extension is an isometric continuous linear map. -/
private theorem canonicalAffineSpatialZeroExtensionLinear_norm
    (a b : DiracMatterSpatialCoordinates)
    (field : CauchySafeMatterSpatialL2 a b) :
    ‖canonicalAffineSpatialZeroExtensionLinear a b field‖ = ‖field‖ :=
  canonicalAffineSpatialZeroExtensionL2_norm field

def canonicalAffineSpatialZeroExtensionCLM
    (a b : DiracMatterSpatialCoordinates) :
    CauchySafeMatterSpatialL2 a b →L[ℝ]
      Lp MatterCoordinateCarrier 2
        (volume : Measure DiracMatterSpatialCoordinates) :=
  LinearMap.mkContinuous
    (canonicalAffineSpatialZeroExtensionLinear a b) 1 fun field ↦ by
      exact (canonicalAffineSpatialZeroExtensionLinear_norm a b field).le.trans_eq
        (one_mul ‖field‖).symm

private def wholeSpatialTranslateLinear
    (shift : DiracMatterSpatialCoordinates) :
    Lp MatterCoordinateCarrier 2
        (volume : Measure DiracMatterSpatialCoordinates) →ₗ[ℝ]
      Lp MatterCoordinateCarrier 2
        (volume : Measure DiracMatterSpatialCoordinates) where
  toFun field := DomAddAct.mk shift +ᵥ field
  map_add' first second := DomAddAct.vadd_Lp_add _ _ _
  map_smul' parameter field := by
    rcases field with ⟨⟨field⟩, fieldMem⟩
    rfl

private def canonicalAffineSpatialDifferenceQuotientLinear
    (a b : DiracMatterSpatialCoordinates)
    (shift : DiracMatterSpatialCoordinates)
    (scale : ℝ) :
    CauchySafeMatterSpatialL2 a b →ₗ[ℝ]
      Lp MatterCoordinateCarrier 2
        (volume : Measure DiracMatterSpatialCoordinates) :=
  scale •
    ((wholeSpatialTranslateLinear shift - 1).comp
      (canonicalAffineSpatialZeroExtensionLinear a b))

private theorem canonicalAffineSpatialDifferenceQuotientLinear_apply
    {a b : DiracMatterSpatialCoordinates}
    (shift : DiracMatterSpatialCoordinates)
    (scale : ℝ)
    (field : CauchySafeMatterSpatialL2 a b) :
    canonicalAffineSpatialDifferenceQuotientLinear a b shift scale field =
      canonicalAffineSpatialDifferenceQuotientL2 shift scale field := by
  change scale •
      ((DomAddAct.mk shift +ᵥ canonicalAffineSpatialZeroExtensionL2 field) -
        canonicalAffineSpatialZeroExtensionL2 field) = _
  change _ = scale •
      ((DomAddAct.mk shift +ᵥ canonicalAffineSpatialZeroExtensionL2 field) -
        canonicalAffineSpatialZeroExtensionL2 field)
  rfl

private theorem canonicalAffineSpatialDifferenceQuotientLinear_norm_le
    {a b : DiracMatterSpatialCoordinates}
    (shift : DiracMatterSpatialCoordinates)
    (scale : ℝ)
    (field : CauchySafeMatterSpatialL2 a b) :
    ‖canonicalAffineSpatialDifferenceQuotientLinear a b shift scale field‖ ≤
      (2 * |scale|) * ‖field‖ := by
  rw [canonicalAffineSpatialDifferenceQuotientLinear_apply]
  exact (canonicalAffineSpatialDifferenceQuotientL2_norm_le
    shift scale field).trans_eq (by ring)

/-- The exact whole-space spatial difference quotient as a bounded linear
operator on the canonical box field. -/
def canonicalAffineSpatialDifferenceQuotientCLM
    (a b : DiracMatterSpatialCoordinates)
    (shift : DiracMatterSpatialCoordinates)
    (scale : ℝ) :
    CauchySafeMatterSpatialL2 a b →L[ℝ]
      Lp MatterCoordinateCarrier 2
        (volume : Measure DiracMatterSpatialCoordinates) :=
  LinearMap.mkContinuous
    (canonicalAffineSpatialDifferenceQuotientLinear a b shift scale)
    (2 * |scale|)
    (canonicalAffineSpatialDifferenceQuotientLinear_norm_le shift scale)

theorem canonicalAffineSpatialDifferenceQuotientCLM_apply
    {a b : DiracMatterSpatialCoordinates}
    (shift : DiracMatterSpatialCoordinates)
    (scale : ℝ)
    (field : CauchySafeMatterSpatialL2 a b) :
    canonicalAffineSpatialDifferenceQuotientCLM a b shift scale field =
      canonicalAffineSpatialDifferenceQuotientL2 shift scale field := by
  exact canonicalAffineSpatialDifferenceQuotientLinear_apply
    shift scale field

theorem canonicalAffineSpatialDifferenceQuotientCLM_norm_le
    (a b : DiracMatterSpatialCoordinates)
    (shift : DiracMatterSpatialCoordinates)
    (scale : ℝ) :
    ‖canonicalAffineSpatialDifferenceQuotientCLM a b shift scale‖ ≤
      2 * |scale| := by
  exact LinearMap.mkContinuous_norm_le
    (canonicalAffineSpatialDifferenceQuotientLinear a b shift scale)
    (mul_nonneg (by norm_num) (abs_nonneg scale))
    (canonicalAffineSpatialDifferenceQuotientLinear_norm_le shift scale)

private def wholeSpatialReflectedTranslateL2
    (point : DiracMatterSpatialCoordinates)
    (field : Lp MatterCoordinateCarrier 2
      (volume : Measure DiracMatterSpatialCoordinates)) :
    Lp MatterCoordinateCarrier 2
      (volume : Measure DiracMatterSpatialCoordinates) :=
  Lp.compMeasurePreserving (fun space ↦ point - space)
    (Measure.measurePreserving_sub_left volume point) field

private theorem wholeSpatialReflectedTranslateL2_norm
    (point : DiracMatterSpatialCoordinates)
    (field : Lp MatterCoordinateCarrier 2
      (volume : Measure DiracMatterSpatialCoordinates)) :
    ‖wholeSpatialReflectedTranslateL2 point field‖ = ‖field‖ := by
  exact Lp.norm_compMeasurePreserving field
    (Measure.measurePreserving_sub_left volume point)

abbrev wholeSpatialScalarMatterAction :
    ℝ →L[ℝ] MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier :=
  ContinuousLinearMap.lsmul ℝ ℝ

private theorem wholeSpatialScalarConvolution_norm_le
    (kernel : DiracMatterSpatialCoordinates → ℝ)
    (kernelMem : MemLp kernel 2
      (volume : Measure DiracMatterSpatialCoordinates))
    (field : Lp MatterCoordinateCarrier 2
      (volume : Measure DiracMatterSpatialCoordinates))
    (point : DiracMatterSpatialCoordinates) :
    ‖(kernel ⋆[wholeSpatialScalarMatterAction, volume]
        fun space ↦ field space) point‖ ≤
      ‖wholeSpatialScalarMatterAction‖ *
        ‖kernelMem.toLp kernel‖ * ‖field‖ := by
  let reflected := wholeSpatialReflectedTranslateL2 point field
  have kernelRead : kernelMem.toLp kernel =ᵐ[volume] kernel :=
    kernelMem.coeFn_toLp
  have reflectedRead : reflected =ᵐ[volume] fun space ↦ field (point - space) :=
    Lp.coeFn_compMeasurePreserving field
      (Measure.measurePreserving_sub_left volume point)
  let product : Lp MatterCoordinateCarrier 1
      (volume : Measure DiracMatterSpatialCoordinates) :=
    wholeSpatialScalarMatterAction.holder 1 (kernelMem.toLp kernel) reflected
  have productRead : product =ᵐ[volume] fun space ↦
      kernel space • field (point - space) := by
    have holderRead := wholeSpatialScalarMatterAction.coeFn_holder
      (r := (1 : ENNReal)) (kernelMem.toLp kernel) reflected
    filter_upwards [holderRead, kernelRead, reflectedRead] with space holderEq
      kernelEq fieldEq
    rw [holderEq]
    exact congrArg₂ (fun scalar value ↦ scalar • value) kernelEq fieldEq
  calc
    ‖(kernel ⋆[wholeSpatialScalarMatterAction, volume]
        fun space ↦ field space) point‖ =
        ‖∫ space, product space ∂volume‖ := by
      apply congrArg norm
      rw [convolution_def]
      exact integral_congr_ae productRead.symm
    _ ≤ ∫ space, ‖product space‖ ∂volume :=
      norm_integral_le_integral_norm product
    _ = ‖product‖ := (L1.norm_eq_integral_norm product).symm
    _ ≤ ‖wholeSpatialScalarMatterAction‖ *
          ‖kernelMem.toLp kernel‖ * ‖reflected‖ :=
      wholeSpatialScalarMatterAction.norm_holder_apply_apply_le
        (kernelMem.toLp kernel) reflected
    _ = _ := by
      rw [wholeSpatialReflectedTranslateL2_norm]

private theorem normalizedBump_memLp_two
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates)) :
    MemLp (bump.normed volume) 2
      (volume : Measure DiracMatterSpatialCoordinates) :=
  (bump.contDiff_normed (n := (0 : ℕ∞))).continuous.memLp_of_hasCompactSupport
    bump.hasCompactSupport_normed

private def normalizedBumpL2
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates)) :
    Lp ℝ 2 (volume : Measure DiracMatterSpatialCoordinates) :=
  (normalizedBump_memLp_two bump).toLp (bump.normed volume)

def wholeSpatialMollificationBound
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates)) : ℝ :=
  ‖wholeSpatialScalarMatterAction‖ * ‖normalizedBumpL2 bump‖

theorem wholeSpatialMollification_norm_le
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (field : Lp MatterCoordinateCarrier 2
      (volume : Measure DiracMatterSpatialCoordinates))
    (point : DiracMatterSpatialCoordinates) :
    ‖wholeSpatialMollification bump field point‖ ≤
      wholeSpatialMollificationBound bump * ‖field‖ := by
  simpa only [wholeSpatialMollification, wholeSpatialScalarMatterAction,
    normalizedBumpL2, wholeSpatialMollificationBound] using
      wholeSpatialScalarConvolution_norm_le
        (bump.normed volume) (normalizedBump_memLp_two bump) field point

def normalizedBumpDirectionalDerivative
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (direction : Fin 3)
    (point : DiracMatterSpatialCoordinates) : ℝ :=
  fderiv ℝ (bump.normed volume) point (Pi.single direction 1)

private theorem normalizedBumpDirectionalDerivative_contDiff
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (direction : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞)
      (normalizedBumpDirectionalDerivative bump direction) := by
  have bumpRegular : ContDiff ℝ (⊤ : ℕ∞) (bump.normed volume) :=
    bump.contDiff_normed
  exact (bumpRegular.fderiv_right
    (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

private theorem normalizedBumpDirectionalDerivative_compact
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (direction : Fin 3) :
    HasCompactSupport (normalizedBumpDirectionalDerivative bump direction) := by
  exact bump.hasCompactSupport_normed.fderiv_apply ℝ
    (Pi.single direction 1)

private theorem normalizedBumpDirectionalDerivative_memLp_two
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (direction : Fin 3) :
    MemLp (normalizedBumpDirectionalDerivative bump direction) 2
      (volume : Measure DiracMatterSpatialCoordinates) :=
  (normalizedBumpDirectionalDerivative_contDiff bump direction).continuous
    |>.memLp_of_hasCompactSupport
      (normalizedBumpDirectionalDerivative_compact bump direction)

theorem wholeSpatialMollification_fderiv_coordinate
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (field : Lp MatterCoordinateCarrier 2
      (volume : Measure DiracMatterSpatialCoordinates))
    (point : DiracMatterSpatialCoordinates)
    (direction : Fin 3) :
    fderiv ℝ (wholeSpatialMollification bump field) point
        (Pi.single direction 1) =
      (normalizedBumpDirectionalDerivative bump direction
        ⋆[wholeSpatialScalarMatterAction, volume]
          fun space ↦ field space) point := by
  have bumpRegular : ContDiff ℝ 1 (bump.normed volume) :=
    bump.contDiff_normed
  have derivative :=
    bump.hasCompactSupport_normed.hasFDerivAt_convolution_left
      wholeSpatialScalarMatterAction
      bumpRegular
      ((Lp.memLp field).locallyIntegrable (by norm_num)) point
  have derivativeConvolutionExists : ConvolutionExistsAt
      (fderiv ℝ (bump.normed volume)) (fun space ↦ field space) point
      (wholeSpatialScalarMatterAction.precompL
        DiracMatterSpatialCoordinates) volume :=
    (bump.hasCompactSupport_normed.fderiv ℝ).convolutionExists_left
      (wholeSpatialScalarMatterAction.precompL
        DiracMatterSpatialCoordinates)
      (bumpRegular.continuous_fderiv one_ne_zero)
      ((Lp.memLp field).locallyIntegrable (by norm_num)) point
  have derivativeEq := derivative.fderiv
  change fderiv ℝ
      ((bump.normed volume) ⋆[wholeSpatialScalarMatterAction, volume]
        fun space ↦ field space) point
      (Pi.single direction 1) = _
  rw [derivativeEq, convolution_def,
    ContinuousLinearMap.integral_apply derivativeConvolutionExists]
  rfl

private def normalizedBumpDirectionalDerivativeL2
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (direction : Fin 3) :
    Lp ℝ 2 (volume : Measure DiracMatterSpatialCoordinates) :=
  (normalizedBumpDirectionalDerivative_memLp_two bump direction).toLp
    (normalizedBumpDirectionalDerivative bump direction)

def wholeSpatialMollificationDerivativeBound
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (direction : Fin 3) : ℝ :=
  ‖wholeSpatialScalarMatterAction‖ *
    ‖normalizedBumpDirectionalDerivativeL2 bump direction‖

theorem wholeSpatialMollification_fderiv_coordinate_norm_le
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (field : Lp MatterCoordinateCarrier 2
      (volume : Measure DiracMatterSpatialCoordinates))
    (point : DiracMatterSpatialCoordinates)
    (direction : Fin 3) :
    ‖fderiv ℝ (wholeSpatialMollification bump field) point
        (Pi.single direction 1)‖ ≤
      wholeSpatialMollificationDerivativeBound bump direction * ‖field‖ := by
  rw [wholeSpatialMollification_fderiv_coordinate]
  simpa only [normalizedBumpDirectionalDerivativeL2,
    wholeSpatialMollificationDerivativeBound] using
    wholeSpatialScalarConvolution_norm_le
      (normalizedBumpDirectionalDerivative bump direction)
      (normalizedBumpDirectionalDerivative_memLp_two bump direction)
      field point

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineSpatialDifferenceQuotientRegularizer
