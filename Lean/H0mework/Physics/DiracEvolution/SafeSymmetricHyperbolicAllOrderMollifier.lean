import H0mework.Physics.DiracEvolution.SafeSymmetricHyperbolicAllOrderCommutator
import H0mework.Physics.DiracEvolution.SafeCanonicalAffineSpatialDifferenceQuotientRegularizer

/-!
# Fixed P506/L0 all-order spatial mollifier

One finite spatial word indexes every derivative of the source-owned smooth
mollification.  The same recursion gives both its exact differentiated kernel
and one L²-to-pointwise bound.  This is the common regularized carrier for the
single symmetric-hyperbolic high-order induction; it introduces no new
difference-quotient level or target regularity premise.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderMollifier

open MeasureTheory
open StageNineDiracMatterSpatialEnergyBalance
open StageNineHolonomicField
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineSpatialDifferenceQuotientRegularizer
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineSpatialDifferenceQuotientTest

open scoped Convolution

noncomputable section

set_option autoImplicit false

local instance two_ne_top : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

def spatialWordDerivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (word : List (Fin 3))
    (field : DiracMatterSpatialCoordinates → E) :
    DiracMatterSpatialCoordinates → E :=
  match word with
  | [] => field
  | direction :: tail => fun point =>
      fderiv ℝ (spatialWordDerivative tail field) point
        (Pi.single direction 1)

theorem spatialWordDerivative_contDiff_infty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (word : List (Fin 3))
    (field : DiracMatterSpatialCoordinates → E)
    (fieldSmooth : ContDiff ℝ (⊤ : ℕ∞) field) :
    ContDiff ℝ (⊤ : ℕ∞) (spatialWordDerivative word field) := by
  induction word with
  | nil => simpa [spatialWordDerivative] using fieldSmooth
  | cons direction tail inductionHypothesis =>
      simp only [spatialWordDerivative]
      exact (inductionHypothesis.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply
        contDiff_const

theorem spatialWordDerivative_compact
    (word : List (Fin 3))
    (field : DiracMatterSpatialCoordinates → ℝ)
    (fieldCompact : HasCompactSupport field) :
    HasCompactSupport (spatialWordDerivative word field) := by
  induction word with
  | nil => simpa [spatialWordDerivative] using fieldCompact
  | cons direction tail inductionHypothesis =>
      simpa only [spatialWordDerivative] using
        inductionHypothesis.fderiv_apply ℝ (Pi.single direction 1)

def normalizedBumpSpatialWordDerivative
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3)) : DiracMatterSpatialCoordinates → ℝ :=
  spatialWordDerivative word (bump.normed volume)

theorem normalizedBumpSpatialWordDerivative_contDiff_infty
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (normalizedBumpSpatialWordDerivative bump word) := by
  exact spatialWordDerivative_contDiff_infty word _ bump.contDiff_normed

theorem normalizedBumpSpatialWordDerivative_compact
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3)) :
    HasCompactSupport (normalizedBumpSpatialWordDerivative bump word) := by
  exact spatialWordDerivative_compact word _ bump.hasCompactSupport_normed

theorem normalizedBumpSpatialWordDerivative_memLp_two
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3)) :
    MemLp (normalizedBumpSpatialWordDerivative bump word) 2
      (volume : Measure DiracMatterSpatialCoordinates) :=
  (normalizedBumpSpatialWordDerivative_contDiff_infty bump word).continuous
    |>.memLp_of_hasCompactSupport
      (normalizedBumpSpatialWordDerivative_compact bump word)

private theorem convolution_coordinateDerivative
    (kernel : DiracMatterSpatialCoordinates → ℝ)
    (kernelCompact : HasCompactSupport kernel)
    (kernelSmooth : ContDiff ℝ (⊤ : ℕ∞) kernel)
    (field : Lp MatterCoordinateCarrier 2
      (volume : Measure DiracMatterSpatialCoordinates))
    (point : DiracMatterSpatialCoordinates)
    (direction : Fin 3) :
    fderiv ℝ
        (kernel ⋆[wholeSpatialScalarMatterAction, volume]
          fun space => field space)
        point (Pi.single direction 1) =
      ((fun candidate =>
          fderiv ℝ kernel candidate (Pi.single direction 1))
        ⋆[wholeSpatialScalarMatterAction, volume]
          fun space => field space) point := by
  have kernelOne : ContDiff ℝ 1 kernel := kernelSmooth.of_le (by simp)
  have derivative := kernelCompact.hasFDerivAt_convolution_left
    wholeSpatialScalarMatterAction kernelOne
    ((Lp.memLp field).locallyIntegrable (by norm_num)) point
  have derivativeConvolutionExists : ConvolutionExistsAt
      (fderiv ℝ kernel) (fun space => field space) point
      (wholeSpatialScalarMatterAction.precompL
        DiracMatterSpatialCoordinates) volume :=
    (kernelCompact.fderiv ℝ).convolutionExists_left
      (wholeSpatialScalarMatterAction.precompL
        DiracMatterSpatialCoordinates)
      (kernelOne.continuous_fderiv one_ne_zero)
      ((Lp.memLp field).locallyIntegrable (by norm_num)) point
  rw [derivative.fderiv, convolution_def,
    ContinuousLinearMap.integral_apply derivativeConvolutionExists]
  rfl

theorem wholeSpatialMollification_spatialWordDerivative
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (field : Lp MatterCoordinateCarrier 2
      (volume : Measure DiracMatterSpatialCoordinates))
    (word : List (Fin 3)) :
    spatialWordDerivative word (wholeSpatialMollification bump field) =
      normalizedBumpSpatialWordDerivative bump word
        ⋆[wholeSpatialScalarMatterAction, volume]
          fun space => field space := by
  induction word with
  | nil => rfl
  | cons direction tail inductionHypothesis =>
      funext point
      simp only [spatialWordDerivative,
        normalizedBumpSpatialWordDerivative]
      rw [show spatialWordDerivative tail
          (wholeSpatialMollification bump field) =
          normalizedBumpSpatialWordDerivative bump tail
            ⋆[wholeSpatialScalarMatterAction, volume]
              fun space => field space from inductionHypothesis]
      exact convolution_coordinateDerivative
        (normalizedBumpSpatialWordDerivative bump tail)
        (normalizedBumpSpatialWordDerivative_compact bump tail)
        (normalizedBumpSpatialWordDerivative_contDiff_infty bump tail)
        field point direction

private def reflectedTranslateL2
    (point : DiracMatterSpatialCoordinates)
    (field : Lp MatterCoordinateCarrier 2
      (volume : Measure DiracMatterSpatialCoordinates)) :
    Lp MatterCoordinateCarrier 2
      (volume : Measure DiracMatterSpatialCoordinates) :=
  Lp.compMeasurePreserving (fun space => point - space)
    (Measure.measurePreserving_sub_left volume point) field

private theorem reflectedTranslateL2_norm
    (point : DiracMatterSpatialCoordinates)
    (field : Lp MatterCoordinateCarrier 2
      (volume : Measure DiracMatterSpatialCoordinates)) :
    ‖reflectedTranslateL2 point field‖ = ‖field‖ := by
  exact Lp.norm_compMeasurePreserving field
    (Measure.measurePreserving_sub_left volume point)

private theorem scalarConvolution_norm_le
    (kernel : DiracMatterSpatialCoordinates → ℝ)
    (kernelMem : MemLp kernel 2
      (volume : Measure DiracMatterSpatialCoordinates))
    (field : Lp MatterCoordinateCarrier 2
      (volume : Measure DiracMatterSpatialCoordinates))
    (point : DiracMatterSpatialCoordinates) :
    ‖(kernel ⋆[wholeSpatialScalarMatterAction, volume]
        fun space => field space) point‖ ≤
      ‖wholeSpatialScalarMatterAction‖ *
        ‖kernelMem.toLp kernel‖ * ‖field‖ := by
  let reflected := reflectedTranslateL2 point field
  have kernelRead : kernelMem.toLp kernel =ᵐ[volume] kernel :=
    kernelMem.coeFn_toLp
  have reflectedRead : reflected =ᵐ[volume]
      fun space => field (point - space) :=
    Lp.coeFn_compMeasurePreserving field
      (Measure.measurePreserving_sub_left volume point)
  let product : Lp MatterCoordinateCarrier 1
      (volume : Measure DiracMatterSpatialCoordinates) :=
    wholeSpatialScalarMatterAction.holder 1 (kernelMem.toLp kernel) reflected
  have productRead : product =ᵐ[volume] fun space =>
      kernel space • field (point - space) := by
    have holderRead := wholeSpatialScalarMatterAction.coeFn_holder
      (r := (1 : ENNReal)) (kernelMem.toLp kernel) reflected
    filter_upwards [holderRead, kernelRead, reflectedRead] with space holderEq
      kernelEq fieldEq
    rw [holderEq]
    exact congrArg₂ (fun scalar value => scalar • value) kernelEq fieldEq
  calc
    ‖(kernel ⋆[wholeSpatialScalarMatterAction, volume]
        fun space => field space) point‖ =
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
    _ = _ := by rw [reflectedTranslateL2_norm]

private def normalizedBumpSpatialWordDerivativeL2
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3)) :
    Lp ℝ 2 (volume : Measure DiracMatterSpatialCoordinates) :=
  (normalizedBumpSpatialWordDerivative_memLp_two bump word).toLp
    (normalizedBumpSpatialWordDerivative bump word)

def wholeSpatialMollificationSpatialWordBound
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3)) : ℝ :=
  ‖wholeSpatialScalarMatterAction‖ *
    ‖normalizedBumpSpatialWordDerivativeL2 bump word‖

theorem wholeSpatialMollification_spatialWordDerivative_norm_le
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (field : Lp MatterCoordinateCarrier 2
      (volume : Measure DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (point : DiracMatterSpatialCoordinates) :
    ‖spatialWordDerivative word (wholeSpatialMollification bump field) point‖ ≤
      wholeSpatialMollificationSpatialWordBound bump word * ‖field‖ := by
  rw [wholeSpatialMollification_spatialWordDerivative bump field word]
  simpa only [normalizedBumpSpatialWordDerivativeL2,
    wholeSpatialMollificationSpatialWordBound] using
    scalarConvolution_norm_le
      (normalizedBumpSpatialWordDerivative bump word)
      (normalizedBumpSpatialWordDerivative_memLp_two bump word)
      field point

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderMollifier
