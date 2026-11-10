import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyClosure
import H0mework.Physics.DiracEvolution.SafeCanonicalAffineSpatialDifferenceQuotientRegularizer
import H0mework.Physics.DiracEvolution.SafeCanonicalFiniteStep
import H0mework.Physics.DiracEvolution.GalerkinEvolution
import Mathlib.Order.Filter.Finite

/-!
# Fixed P506/L0 Friedrichs evolution

The fixed source generates a canonical shrinking spatial mollifier, its
bounded first-jet realization on each Cauchy box, and the corresponding exact
Banach-space evolution.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterFriedrichsEvolution

open MeasureTheory Set
open ProofFreeRicherAnholonomicSource
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineCanonicalCauchyState
open StageNineDiracMatterGalerkinEvolution
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineSpatialDifferenceQuotientRegularizer
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineSpatialDifferenceQuotientTest
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderJetProlongation
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderMollifier
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterTemporalJetReduction
open StageNineHolonomicField
open scoped Convolution ENNReal Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

local instance friedrichsMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

/-- The canonical radius-`1/(n+1)` Friedrichs kernel of the fixed matter
evolution. -/
def fixedMatterFriedrichsBump
    (index : ℕ) : ContDiffBump (0 : DiracMatterSpatialCoordinates) where
  rIn := ((index + 1 : ℕ) : ℝ)⁻¹
  rOut := 2 * ((index + 1 : ℕ) : ℝ)⁻¹
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have positive : 0 < ((index + 1 : ℕ) : ℝ)⁻¹ := by positivity
    linarith

private def fixedMatterSpatialWordKernelL2
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3)) :
    Lp ℝ 2 (volume : Measure DiracMatterSpatialCoordinates) :=
  (normalizedBumpSpatialWordDerivative_memLp_two bump word).toLp
    (normalizedBumpSpatialWordDerivative bump word)

private def fixedMatterSpatialReflectionCLM
    (space : DiracMatterSpatialCoordinates) :
    Lp MatterCoordinateCarrier 2
        (volume : Measure DiracMatterSpatialCoordinates) →L[ℝ]
      Lp MatterCoordinateCarrier 2
        (volume : Measure DiracMatterSpatialCoordinates) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun point => space - point)
    (Measure.measurePreserving_sub_left volume space)).toContinuousLinearMap

/-- Evaluation of one spatial word of the canonical mollifier as a bounded
linear read of the whole-space physical field. -/
def fixedMatterSpatialWordMollificationEvaluationCLM
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (space : DiracMatterSpatialCoordinates) :
    Lp MatterCoordinateCarrier 2
        (volume : Measure DiracMatterSpatialCoordinates) →L[ℝ]
      MatterCoordinateCarrier :=
  ((wholeSpatialScalarMatterAction.lpPairing volume 2 2)
      (fixedMatterSpatialWordKernelL2 bump word)).comp
    (fixedMatterSpatialReflectionCLM space)

theorem fixedMatterSpatialWordMollificationEvaluationCLM_apply
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (space : DiracMatterSpatialCoordinates)
    (field : Lp MatterCoordinateCarrier 2
      (volume : Measure DiracMatterSpatialCoordinates)) :
    fixedMatterSpatialWordMollificationEvaluationCLM bump word space field =
      (normalizedBumpSpatialWordDerivative bump word
        ⋆[wholeSpatialScalarMatterAction, volume]
          fun point => field point) space := by
  let kernel := fixedMatterSpatialWordKernelL2 bump word
  let reflected := fixedMatterSpatialReflectionCLM space field
  have kernelRead : kernel =ᵐ[volume]
      normalizedBumpSpatialWordDerivative bump word :=
    (normalizedBumpSpatialWordDerivative_memLp_two bump word).coeFn_toLp
  have reflectedRead : reflected =ᵐ[volume]
      fun point => field (space - point) :=
    Lp.coeFn_compMeasurePreserving field
      (Measure.measurePreserving_sub_left volume space)
  rw [fixedMatterSpatialWordMollificationEvaluationCLM,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.lpPairing_eq_integral, convolution_def]
  exact integral_congr_ae <| by
    filter_upwards [kernelRead, reflectedRead] with point kernelEq fieldEq
    rw [kernelEq, fieldEq]

private def fixedMatterSpatialWordMollificationBoxPointCLM
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates)
    (space : DiracMatterSpatialCoordinates) :
    CauchySafeMatterSpatialL2 a b →L[ℝ] MatterCoordinateCarrier :=
  (fixedMatterSpatialWordMollificationEvaluationCLM bump word space).comp
    (canonicalAffineSpatialZeroExtensionCLM a b)

def fixedMatterSpatialWordMollificationBoxField
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates)
    (field : CauchySafeMatterSpatialL2 a b)
    (space : DiracMatterSpatialCoordinates) : MatterCoordinateCarrier :=
  fixedMatterSpatialWordMollificationBoxPointCLM bump word a b space field

theorem fixedMatterSpatialWordMollificationBoxField_contDiff_infty
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates)
    (field : CauchySafeMatterSpatialL2 a b) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fixedMatterSpatialWordMollificationBoxField bump word a b field) := by
  have pointwise : fixedMatterSpatialWordMollificationBoxField
      bump word a b field =
      normalizedBumpSpatialWordDerivative bump word
        ⋆[wholeSpatialScalarMatterAction, volume]
          fun point => canonicalAffineSpatialZeroExtensionCLM a b field point := by
    funext space
    exact fixedMatterSpatialWordMollificationEvaluationCLM_apply
      bump word space (canonicalAffineSpatialZeroExtensionCLM a b field)
  rw [pointwise]
  exact (normalizedBumpSpatialWordDerivative_compact bump word
    ).contDiff_convolution_left wholeSpatialScalarMatterAction
      (normalizedBumpSpatialWordDerivative_contDiff_infty bump word)
      ((Lp.memLp (canonicalAffineSpatialZeroExtensionCLM a b field)
        ).locallyIntegrable (by norm_num))

/-- The source mollifier is jointly continuous in its physical `L²` input
and spatial read point. -/
theorem fixedMatterSpatialWordMollificationBoxField_joint_continuous
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates) :
    Continuous (fun input :
        CauchySafeMatterSpatialL2 a b × DiracMatterSpatialCoordinates =>
      fixedMatterSpatialWordMollificationBoxField
        bump word a b input.1 input.2) := by
  let reflectionJoint : C(DiracMatterSpatialCoordinates ×
      DiracMatterSpatialCoordinates, DiracMatterSpatialCoordinates) :=
    ⟨fun input => input.1 - input.2, by fun_prop⟩
  let reflection := reflectionJoint.curry
  have zeroExtensionContinuous : Continuous (fun input :
      CauchySafeMatterSpatialL2 a b × DiracMatterSpatialCoordinates =>
        canonicalAffineSpatialZeroExtensionCLM a b input.1) :=
    (canonicalAffineSpatialZeroExtensionCLM a b).continuous.comp continuous_fst
  have reflectionContinuous : Continuous (fun input :
      CauchySafeMatterSpatialL2 a b × DiracMatterSpatialCoordinates =>
        reflection input.2) :=
    reflection.continuous.comp continuous_snd
  have reflectedContinuous : Continuous (fun input :
      CauchySafeMatterSpatialL2 a b × DiracMatterSpatialCoordinates =>
        Lp.compMeasurePreserving (reflection input.2)
          (Measure.measurePreserving_sub_left volume input.2)
          (canonicalAffineSpatialZeroExtensionCLM a b input.1)) :=
    zeroExtensionContinuous.compMeasurePreservingLp reflectionContinuous
      (fun input => Measure.measurePreserving_sub_left volume input.2)
      (by norm_num)
  unfold fixedMatterSpatialWordMollificationBoxField
    fixedMatterSpatialWordMollificationBoxPointCLM
    fixedMatterSpatialWordMollificationEvaluationCLM
    fixedMatterSpatialReflectionCLM
  exact ((wholeSpatialScalarMatterAction.lpPairing volume 2 2)
    (fixedMatterSpatialWordKernelL2 bump word)).continuous.comp
      reflectedContinuous

/-- Differentiating one generated box mollification coordinate emits the
next spatial word of the same source mollifier. -/
theorem fixedMatterSpatialWordMollificationBoxField_fderiv_apply
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates)
    (field : CauchySafeMatterSpatialL2 a b)
    (space : DiracMatterSpatialCoordinates)
    (direction : Fin 3) :
    fderiv ℝ
        (fixedMatterSpatialWordMollificationBoxField bump word a b field)
        space (Pi.single direction 1) =
      fixedMatterSpatialWordMollificationBoxField
        bump (direction :: word) a b field space := by
  let wholeField := canonicalAffineSpatialZeroExtensionCLM a b field
  have wordField :
      fixedMatterSpatialWordMollificationBoxField bump word a b field =
        spatialWordDerivative word
          (wholeSpatialMollification bump wholeField) := by
    rw [wholeSpatialMollification_spatialWordDerivative]
    funext point
    exact fixedMatterSpatialWordMollificationEvaluationCLM_apply
      bump word point wholeField
  have childField :
      fixedMatterSpatialWordMollificationBoxField
          bump (direction :: word) a b field =
        spatialWordDerivative (direction :: word)
          (wholeSpatialMollification bump wholeField) := by
    rw [wholeSpatialMollification_spatialWordDerivative]
    funext point
    exact fixedMatterSpatialWordMollificationEvaluationCLM_apply
      bump (direction :: word) point wholeField
  rw [wordField, childField]
  rfl

/-- The full spatial derivative of one generated mollifier word, assembled
from the three child words of the same source-owned hierarchy. -/
def fixedMatterSpatialWordMollificationBoxFieldSpatialDerivativeCLM
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates)
    (field : CauchySafeMatterSpatialL2 a b)
    (space : DiracMatterSpatialCoordinates) :
    DiracMatterSpatialCoordinates →L[ℝ] MatterCoordinateCarrier :=
  ∑ direction : Fin 3,
    (ContinuousLinearMap.proj direction).smulRight
      (fixedMatterSpatialWordMollificationBoxField
        bump (direction :: word) a b field space)

/-- The assembled child-word map is exactly the Fréchet derivative of the
parent mollifier word. -/
theorem fixedMatterSpatialWordMollificationBoxField_fderiv
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates)
    (field : CauchySafeMatterSpatialL2 a b)
    (space : DiracMatterSpatialCoordinates) :
    fderiv ℝ
        (fixedMatterSpatialWordMollificationBoxField bump word a b field)
        space =
      fixedMatterSpatialWordMollificationBoxFieldSpatialDerivativeCLM
        bump word a b field space := by
  apply ContinuousLinearMap.ext
  intro directionVector
  rw [show directionVector = ∑ direction : Fin 3,
      directionVector direction • Pi.single direction (1 : ℝ) by
    exact pi_eq_sum_univ' directionVector]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro direction _
  rw [fixedMatterSpatialWordMollificationBoxField_fderiv_apply]
  simp [fixedMatterSpatialWordMollificationBoxFieldSpatialDerivativeCLM]

/-- The complete spatial derivative varies jointly continuously with the
physical `L²` input and the spatial read point. -/
theorem fixedMatterSpatialWordMollificationBoxFieldSpatialDerivativeCLM_joint_continuous
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates) :
    Continuous (fun input :
        CauchySafeMatterSpatialL2 a b × DiracMatterSpatialCoordinates =>
      fixedMatterSpatialWordMollificationBoxFieldSpatialDerivativeCLM
        bump word a b input.1 input.2) := by
  unfold fixedMatterSpatialWordMollificationBoxFieldSpatialDerivativeCLM
  apply continuous_finsetSum
  intro direction _
  exact ((ContinuousLinearMap.smulRightL ℝ
    DiracMatterSpatialCoordinates MatterCoordinateCarrier)
      (ContinuousLinearMap.proj direction)).continuous.comp
        (fixedMatterSpatialWordMollificationBoxField_joint_continuous
          bump (direction :: word) a b)

/-- The same identity simultaneously covers every finite spatial derivative
word; no regularity order or coordinate is selected by the producer. -/
theorem fixedMatterSpatialWordMollificationBoxField_spatialWordDerivative
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (derivativeWord word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates)
    (field : CauchySafeMatterSpatialL2 a b) :
    spatialWordDerivative derivativeWord
        (fixedMatterSpatialWordMollificationBoxField bump word a b field) =
      fixedMatterSpatialWordMollificationBoxField
        bump (derivativeWord ++ word) a b field := by
  induction derivativeWord with
  | nil => rfl
  | cons direction tail inductionHypothesis =>
      simp only [spatialWordDerivative, List.cons_append]
      rw [inductionHypothesis]
      funext space
      exact fixedMatterSpatialWordMollificationBoxField_fderiv_apply
        bump (tail ++ word) a b field space direction

/-- Every generated derivative word varies jointly continuously with the
physical `L²` input and the spatial read point. -/
theorem fixedMatterSpatialWordMollificationBoxField_spatialWordDerivative_joint_continuous
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (derivativeWord word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates) :
    Continuous (fun input :
        CauchySafeMatterSpatialL2 a b × DiracMatterSpatialCoordinates =>
      spatialWordDerivative derivativeWord
        (fixedMatterSpatialWordMollificationBoxField
          bump word a b input.1) input.2) := by
  refine (fixedMatterSpatialWordMollificationBoxField_joint_continuous
    bump (derivativeWord ++ word) a b).congr ?_
  intro input
  exact (congrFun
    (fixedMatterSpatialWordMollificationBoxField_spatialWordDerivative
      bump derivativeWord word a b input.1) input.2).symm

/-- Time integration of one continuously evolving physical `L²` field after
the source-owned spatial mollifier. -/
def fixedMatterSpatialWordMollificationPathIntegral
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates)
    (path : C(ℝ, CauchySafeMatterSpatialL2 a b))
    (timeStart timeEnd : ℝ)
    (space : DiracMatterSpatialCoordinates) : MatterCoordinateCarrier :=
  ∫ candidateTime in timeStart..timeEnd,
    fixedMatterSpatialWordMollificationBoxField
      bump word a b (path candidateTime) space

theorem fixedMatterIntervalIntegral_hasFDerivAt_of_joint_continuous
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (integrand : E → ℝ → F)
    (integrandDerivative : E → ℝ → E →L[ℝ] F)
    (integrandJointContinuous : Continuous (Function.uncurry integrand))
    (derivativeJointContinuous :
      Continuous (Function.uncurry integrandDerivative))
    (differentiated : ∀ candidate candidateTime,
      HasFDerivAt (fun point => integrand point candidateTime)
        (integrandDerivative candidate candidateTime) candidate)
    (timeStart timeEnd : ℝ)
    (point : E) :
    HasFDerivAt
      (fun candidate => ∫ candidateTime in timeStart..timeEnd,
        integrand candidate candidateTime)
      (∫ candidateTime in timeStart..timeEnd,
        integrandDerivative point candidateTime)
      point := by
  obtain ⟨bound, derivativeBound⟩ :=
    ((isCompact_closedBall point 1).prod
      (isCompact_uIcc : IsCompact (uIcc timeStart timeEnd))
      ).exists_bound_of_continuousOn derivativeJointContinuous.continuousOn
  have integrandContinuous (candidate : E) :
      Continuous (integrand candidate) :=
    integrandJointContinuous.comp (continuous_const.prodMk continuous_id)
  have derivativeContinuous (candidate : E) :
      Continuous (integrandDerivative candidate) :=
    derivativeJointContinuous.comp (continuous_const.prodMk continuous_id)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.closedBall point 1) (bound := fun _ => bound)
  · exact Metric.closedBall_mem_nhds point zero_lt_one
  · filter_upwards [] with candidate
    exact (integrandContinuous candidate).aestronglyMeasurable
  · exact (integrandContinuous point).intervalIntegrable timeStart timeEnd
  · exact (derivativeContinuous point).aestronglyMeasurable
  · filter_upwards [] with candidateTime candidateTimeMem candidate candidateMem
    exact derivativeBound (candidate, candidateTime)
      ⟨candidateMem, uIoc_subset_uIcc candidateTimeMem⟩
  · exact continuous_const.intervalIntegrable timeStart timeEnd
  · filter_upwards [] with candidateTime _ candidate _
    exact differentiated candidate candidateTime

/-- A continuous `L²` path can be differentiated under the generated
mollifier integral without selecting a coordinate or a regularity order. -/
theorem fixedMatterSpatialWordMollificationPathIntegral_hasFDerivAt
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates)
    (path : C(ℝ, CauchySafeMatterSpatialL2 a b))
    (timeStart timeEnd : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    HasFDerivAt
      (fixedMatterSpatialWordMollificationPathIntegral
        bump word a b path timeStart timeEnd)
      (∫ candidateTime in timeStart..timeEnd,
        fixedMatterSpatialWordMollificationBoxFieldSpatialDerivativeCLM
          bump word a b (path candidateTime) space)
      space := by
  let integrand : DiracMatterSpatialCoordinates → ℝ →
      MatterCoordinateCarrier := fun candidate candidateTime =>
    fixedMatterSpatialWordMollificationBoxField
      bump word a b (path candidateTime) candidate
  let integrandDerivative : DiracMatterSpatialCoordinates → ℝ →
      DiracMatterSpatialCoordinates →L[ℝ] MatterCoordinateCarrier :=
    fun candidate candidateTime =>
      fixedMatterSpatialWordMollificationBoxFieldSpatialDerivativeCLM
        bump word a b (path candidateTime) candidate
  let inputMap : C(DiracMatterSpatialCoordinates × ℝ,
      CauchySafeMatterSpatialL2 a b × DiracMatterSpatialCoordinates) :=
    ⟨fun pair => (path pair.2, pair.1),
      (path.continuous.comp continuous_snd).prodMk continuous_fst⟩
  let mollifier : C(CauchySafeMatterSpatialL2 a b ×
      DiracMatterSpatialCoordinates, MatterCoordinateCarrier) :=
    ⟨fun input => fixedMatterSpatialWordMollificationBoxField
        bump word a b input.1 input.2,
      fixedMatterSpatialWordMollificationBoxField_joint_continuous
        bump word a b⟩
  let mollifierDerivative : C(CauchySafeMatterSpatialL2 a b ×
      DiracMatterSpatialCoordinates,
      DiracMatterSpatialCoordinates →L[ℝ] MatterCoordinateCarrier) :=
    ⟨fun input =>
        fixedMatterSpatialWordMollificationBoxFieldSpatialDerivativeCLM
          bump word a b input.1 input.2,
      fixedMatterSpatialWordMollificationBoxFieldSpatialDerivativeCLM_joint_continuous
        bump word a b⟩
  have integrandJointContinuous : Continuous
      (fun pair : DiracMatterSpatialCoordinates × ℝ =>
        integrand pair.1 pair.2) := by
    exact (mollifier.comp inputMap).continuous
  have derivativeJointContinuous : Continuous
      (fun pair : DiracMatterSpatialCoordinates × ℝ =>
        integrandDerivative pair.1 pair.2) := by
    exact (mollifierDerivative.comp inputMap).continuous
  apply fixedMatterIntervalIntegral_hasFDerivAt_of_joint_continuous
    integrand integrandDerivative integrandJointContinuous
      derivativeJointContinuous
  intro candidate candidateTime
  have smooth := fixedMatterSpatialWordMollificationBoxField_contDiff_infty
    bump word a b (path candidateTime)
  have actual := (smooth.differentiable (by simp) candidate).hasFDerivAt
  rw [fixedMatterSpatialWordMollificationBoxField_fderiv] at actual
  exact actual

/-- One coordinate readback of differentiation under the generated time
integral. -/
theorem fixedMatterSpatialWordMollificationPathIntegral_fderiv_apply
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates)
    (path : C(ℝ, CauchySafeMatterSpatialL2 a b))
    (timeStart timeEnd : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (direction : Fin 3) :
    fderiv ℝ
        (fixedMatterSpatialWordMollificationPathIntegral
          bump word a b path timeStart timeEnd)
        space (Pi.single direction 1) =
      fixedMatterSpatialWordMollificationPathIntegral
        bump (direction :: word) a b path timeStart timeEnd space := by
  let fixedSpaceInput : C(ℝ, CauchySafeMatterSpatialL2 a b ×
      DiracMatterSpatialCoordinates) :=
    ⟨fun candidateTime => (path candidateTime, space),
      path.continuous.prodMk continuous_const⟩
  let mollifierDerivative : C(CauchySafeMatterSpatialL2 a b ×
      DiracMatterSpatialCoordinates,
      DiracMatterSpatialCoordinates →L[ℝ] MatterCoordinateCarrier) :=
    ⟨fun input =>
        fixedMatterSpatialWordMollificationBoxFieldSpatialDerivativeCLM
          bump word a b input.1 input.2,
      fixedMatterSpatialWordMollificationBoxFieldSpatialDerivativeCLM_joint_continuous
        bump word a b⟩
  have derivativeContinuous : Continuous (fun candidateTime =>
      fixedMatterSpatialWordMollificationBoxFieldSpatialDerivativeCLM
        bump word a b (path candidateTime) space) :=
    (mollifierDerivative.comp fixedSpaceInput).continuous
  let evaluate :
      (DiracMatterSpatialCoordinates →L[ℝ] MatterCoordinateCarrier) →L[ℝ]
        MatterCoordinateCarrier :=
    ContinuousLinearMap.apply ℝ MatterCoordinateCarrier
      (Pi.single direction 1)
  have derivativeIntegrable : IntervalIntegrable (fun candidateTime =>
      fixedMatterSpatialWordMollificationBoxFieldSpatialDerivativeCLM
        bump word a b (path candidateTime) space) volume timeStart timeEnd :=
    derivativeContinuous.intervalIntegrable timeStart timeEnd
  rw [(fixedMatterSpatialWordMollificationPathIntegral_hasFDerivAt
    bump word a b path timeStart timeEnd space).fderiv]
  rw [show
      (∫ candidateTime in timeStart..timeEnd,
        fixedMatterSpatialWordMollificationBoxFieldSpatialDerivativeCLM
          bump word a b (path candidateTime) space) (Pi.single direction 1) =
      ∫ candidateTime in timeStart..timeEnd,
        evaluate
          (fixedMatterSpatialWordMollificationBoxFieldSpatialDerivativeCLM
            bump word a b (path candidateTime) space) by
    exact (evaluate.intervalIntegral_comp_comm derivativeIntegrable).symm]
  apply intervalIntegral.integral_congr
  intro candidateTime _
  simp [evaluate,
    fixedMatterSpatialWordMollificationBoxFieldSpatialDerivativeCLM]

/-- Time integration commutes with every finite spatial word at once. -/
theorem fixedMatterSpatialWordMollificationPathIntegral_spatialWordDerivative
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (derivativeWord word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates)
    (path : C(ℝ, CauchySafeMatterSpatialL2 a b))
    (timeStart timeEnd : ℝ) :
    spatialWordDerivative derivativeWord
        (fixedMatterSpatialWordMollificationPathIntegral
          bump word a b path timeStart timeEnd) =
      fixedMatterSpatialWordMollificationPathIntegral
        bump (derivativeWord ++ word) a b path timeStart timeEnd := by
  induction derivativeWord with
  | nil => rfl
  | cons direction tail inductionHypothesis =>
      simp only [spatialWordDerivative, List.cons_append]
      rw [inductionHypothesis]
      funext space
      exact fixedMatterSpatialWordMollificationPathIntegral_fderiv_apply
        bump (tail ++ word) a b path timeStart timeEnd space direction

private theorem fixedMatterSpatialWordMollificationPathIntegral_contDiff_nat
    (order : ℕ)
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates)
    (path : C(ℝ, CauchySafeMatterSpatialL2 a b))
    (timeStart timeEnd : ℝ) :
    ContDiff ℝ order
      (fixedMatterSpatialWordMollificationPathIntegral
        bump word a b path timeStart timeEnd) := by
  induction order generalizing word with
  | zero =>
      have actual :=
        (contDiff_zero (𝕜 := ℝ)
          (f := fixedMatterSpatialWordMollificationPathIntegral
            bump word a b path timeStart timeEnd)).mpr
          (continuous_iff_continuousAt.mpr fun space =>
            (fixedMatterSpatialWordMollificationPathIntegral_hasFDerivAt
              bump word a b path timeStart timeEnd space).continuousAt)
      simpa using actual
  | succ order inductionHypothesis =>
      rw [Nat.cast_succ]
      rw [contDiff_succ_iff_fderiv_apply]
      refine ⟨?_, by simp, ?_⟩
      · intro space
        exact (fixedMatterSpatialWordMollificationPathIntegral_hasFDerivAt
          bump word a b path timeStart timeEnd space).differentiableAt
      · intro directionVector
        have derivativeEq :
            (fun space => fderiv ℝ
              (fixedMatterSpatialWordMollificationPathIntegral
                bump word a b path timeStart timeEnd)
              space directionVector) =
            fun space => ∑ direction : Fin 3,
              directionVector direction •
                fixedMatterSpatialWordMollificationPathIntegral
                  bump (direction :: word) a b path timeStart timeEnd space := by
          funext space
          conv_lhs =>
            rw [show directionVector = ∑ direction : Fin 3,
                directionVector direction • Pi.single direction (1 : ℝ) by
              exact pi_eq_sum_univ' directionVector]
          simp only [map_sum, map_smul]
          apply Finset.sum_congr rfl
          intro direction _
          rw [fixedMatterSpatialWordMollificationPathIntegral_fderiv_apply]
        rw [derivativeEq]
        apply ContDiff.sum
        intro direction _
        exact ContDiff.const_smul (R := ℝ) (directionVector direction)
          (inductionHypothesis (direction :: word))

/-- A continuous physical `L²` path generates a spatially smooth time
integral, with all spatial orders supplied by the same word hierarchy. -/
theorem fixedMatterSpatialWordMollificationPathIntegral_contDiff_infty
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates)
    (path : C(ℝ, CauchySafeMatterSpatialL2 a b))
    (timeStart timeEnd : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fixedMatterSpatialWordMollificationPathIntegral
        bump word a b path timeStart timeEnd) := by
  rw [contDiff_infty]
  intro order
  exact fixedMatterSpatialWordMollificationPathIntegral_contDiff_nat
    order bump word a b path timeStart timeEnd

private def fixedMatterSpatialWordMollificationBoxBound
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates) : ℝ :=
  ‖(wholeSpatialScalarMatterAction.lpPairing volume 2 2)
      (fixedMatterSpatialWordKernelL2 bump word)‖ *
    ‖canonicalAffineSpatialZeroExtensionCLM a b‖

theorem fixedMatterSpatialWordMollificationBoxField_norm_le
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates)
    (field : CauchySafeMatterSpatialL2 a b)
    (space : DiracMatterSpatialCoordinates) :
    ‖fixedMatterSpatialWordMollificationBoxField bump word a b field space‖ ≤
      fixedMatterSpatialWordMollificationBoxBound bump word a b * ‖field‖ := by
  let whole := canonicalAffineSpatialZeroExtensionCLM a b field
  let pairing := (wholeSpatialScalarMatterAction.lpPairing volume 2 2)
    (fixedMatterSpatialWordKernelL2 bump word)
  calc
    ‖fixedMatterSpatialWordMollificationBoxField bump word a b field space‖ =
        ‖pairing (fixedMatterSpatialReflectionCLM space whole)‖ := rfl
    _ ≤ ‖pairing‖ * ‖fixedMatterSpatialReflectionCLM space whole‖ :=
      pairing.le_opNorm _
    _ = ‖pairing‖ * ‖whole‖ := by
      congr 1
      exact (Lp.compMeasurePreservingₗᵢ ℝ (fun point => space - point)
        (Measure.measurePreserving_sub_left volume space)).norm_map whole
    _ ≤ ‖pairing‖ *
        (‖canonicalAffineSpatialZeroExtensionCLM a b‖ * ‖field‖) := by
      exact mul_le_mul_of_nonneg_left
        ((canonicalAffineSpatialZeroExtensionCLM a b).le_opNorm field)
        (norm_nonneg _)
    _ = fixedMatterSpatialWordMollificationBoxBound bump word a b * ‖field‖ := by
      simp only [fixedMatterSpatialWordMollificationBoxBound]
      ring

/-- One estimate controls every selected derivative word by reading the
matching child word of the same generated mollifier hierarchy. -/
theorem fixedMatterSpatialWordMollificationBoxField_spatialWordDerivative_norm_le
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (derivativeWord word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates)
    (field : CauchySafeMatterSpatialL2 a b)
    (space : DiracMatterSpatialCoordinates) :
    ‖spatialWordDerivative derivativeWord
        (fixedMatterSpatialWordMollificationBoxField
          bump word a b field) space‖ ≤
      fixedMatterSpatialWordMollificationBoxBound
        bump (derivativeWord ++ word) a b * ‖field‖ := by
  rw [congrFun
    (fixedMatterSpatialWordMollificationBoxField_spatialWordDerivative
      bump derivativeWord word a b field) space]
  exact fixedMatterSpatialWordMollificationBoxField_norm_le
    bump (derivativeWord ++ word) a b field space

private theorem fixedMatterSpatialWordMollificationBoxField_memLp
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates)
    (field : CauchySafeMatterSpatialL2 a b) :
    MemLp (fixedMatterSpatialWordMollificationBoxField bump word a b field)
      2 (volume.restrict (Icc a b)) := by
  letI : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    { measure_univ_lt_top := by simp [isCompact_Icc.measure_lt_top] }
  apply MemLp.of_bound
    (fixedMatterSpatialWordMollificationBoxField_contDiff_infty
      bump word a b field).continuous.aestronglyMeasurable.restrict
    (fixedMatterSpatialWordMollificationBoxBound bump word a b * ‖field‖)
  exact ae_of_all _ fun space =>
    fixedMatterSpatialWordMollificationBoxField_norm_le
      bump word a b field space

def fixedMatterSpatialWordMollificationBoxL2
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates)
    (field : CauchySafeMatterSpatialL2 a b) :
    CauchySafeMatterSpatialL2 a b :=
  (fixedMatterSpatialWordMollificationBoxField_memLp
    bump word a b field).toLp
      (fixedMatterSpatialWordMollificationBoxField bump word a b field)

private def fixedMatterSpatialWordMollificationBoxLinear
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates) :
    CauchySafeMatterSpatialL2 a b →ₗ[ℝ]
      CauchySafeMatterSpatialL2 a b where
  toFun := fixedMatterSpatialWordMollificationBoxL2 bump word a b
  map_add' first second := by
    let firstMem := fixedMatterSpatialWordMollificationBoxField_memLp
      bump word a b first
    let secondMem := fixedMatterSpatialWordMollificationBoxField_memLp
      bump word a b second
    let totalMem := fixedMatterSpatialWordMollificationBoxField_memLp
      bump word a b (first + second)
    have pointwise : fixedMatterSpatialWordMollificationBoxField
        bump word a b (first + second) =
        fixedMatterSpatialWordMollificationBoxField bump word a b first +
          fixedMatterSpatialWordMollificationBoxField bump word a b second := by
      funext space
      exact map_add
        (fixedMatterSpatialWordMollificationBoxPointCLM
          bump word a b space) first second
    calc
      fixedMatterSpatialWordMollificationBoxL2 bump word a b
          (first + second) =
          (firstMem.add secondMem).toLp
            (fixedMatterSpatialWordMollificationBoxField bump word a b first +
              fixedMatterSpatialWordMollificationBoxField
                bump word a b second) := by
        exact MemLp.toLp_congr totalMem (firstMem.add secondMem)
          (ae_of_all _ fun space => congrFun pointwise space)
      _ = fixedMatterSpatialWordMollificationBoxL2 bump word a b first +
          fixedMatterSpatialWordMollificationBoxL2 bump word a b second :=
        MemLp.toLp_add firstMem secondMem
  map_smul' parameter field := by
    let fieldMem := fixedMatterSpatialWordMollificationBoxField_memLp
      bump word a b field
    let totalMem := fixedMatterSpatialWordMollificationBoxField_memLp
      bump word a b (parameter • field)
    have pointwise : fixedMatterSpatialWordMollificationBoxField
        bump word a b (parameter • field) =
        parameter • fixedMatterSpatialWordMollificationBoxField
          bump word a b field := by
      funext space
      exact map_smul
        (fixedMatterSpatialWordMollificationBoxPointCLM
          bump word a b space) parameter field
    calc
      fixedMatterSpatialWordMollificationBoxL2 bump word a b
          (parameter • field) =
          (fieldMem.const_smul parameter).toLp
            (parameter • fixedMatterSpatialWordMollificationBoxField
              bump word a b field) := by
        exact MemLp.toLp_congr totalMem (fieldMem.const_smul parameter)
          (ae_of_all _ fun space => congrFun pointwise space)
      _ = parameter •
          fixedMatterSpatialWordMollificationBoxL2 bump word a b field :=
        MemLp.toLp_const_smul parameter fieldMem

private def fixedMatterSpatialWordMollificationBoxOperatorBound
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates) : ℝ :=
  measureUnivNNReal (volume.restrict (Icc a b)) ^
      (2 : ENNReal).toReal⁻¹ *
    fixedMatterSpatialWordMollificationBoxBound bump word a b

private theorem fixedMatterSpatialWordMollificationBoxLinear_norm_le
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates)
    (field : CauchySafeMatterSpatialL2 a b) :
    ‖fixedMatterSpatialWordMollificationBoxLinear bump word a b field‖ ≤
      fixedMatterSpatialWordMollificationBoxOperatorBound bump word a b *
        ‖field‖ := by
  let fieldMem := fixedMatterSpatialWordMollificationBoxField_memLp
    bump word a b field
  letI : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    { measure_univ_lt_top := by simp [isCompact_Icc.measure_lt_top] }
  change ‖fieldMem.toLp
      (fixedMatterSpatialWordMollificationBoxField bump word a b field)‖ ≤ _
  calc
    ‖fieldMem.toLp
        (fixedMatterSpatialWordMollificationBoxField bump word a b field)‖ ≤
        measureUnivNNReal (volume.restrict (Icc a b)) ^
            (2 : ENNReal).toReal⁻¹ *
          (fixedMatterSpatialWordMollificationBoxBound bump word a b *
            ‖field‖) := by
      apply Lp.norm_le_of_ae_bound
      · unfold fixedMatterSpatialWordMollificationBoxBound
        positivity
      filter_upwards [fieldMem.coeFn_toLp] with space read
      rw [read]
      exact fixedMatterSpatialWordMollificationBoxField_norm_le
        bump word a b field space
    _ = fixedMatterSpatialWordMollificationBoxOperatorBound bump word a b *
        ‖field‖ := by
      simp only [fixedMatterSpatialWordMollificationBoxOperatorBound]
      ring

/-- The canonical spatial-word Friedrichs regularizer on one physical box. -/
def fixedMatterSpatialWordMollificationBoxCLM
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates) :
    CauchySafeMatterSpatialL2 a b →L[ℝ]
      CauchySafeMatterSpatialL2 a b :=
  LinearMap.mkContinuous
    (fixedMatterSpatialWordMollificationBoxLinear bump word a b)
    (fixedMatterSpatialWordMollificationBoxOperatorBound bump word a b)
    (fixedMatterSpatialWordMollificationBoxLinear_norm_le bump word a b)

theorem fixedMatterSpatialWordMollificationBoxCLM_coe_ae
    (bump : ContDiffBump (0 : DiracMatterSpatialCoordinates))
    (word : List (Fin 3))
    (a b : DiracMatterSpatialCoordinates)
    (field : CauchySafeMatterSpatialL2 a b) :
    fixedMatterSpatialWordMollificationBoxCLM bump word a b field =ᵐ[
        volume.restrict (Icc a b)]
      fixedMatterSpatialWordMollificationBoxField bump word a b field := by
  let fieldMem := fixedMatterSpatialWordMollificationBoxField_memLp
    bump word a b field
  change fieldMem.toLp
      (fixedMatterSpatialWordMollificationBoxField bump word a b field) =ᵐ[
        volume.restrict (Icc a b)] _
  exact fieldMem.coeFn_toLp

private def fixedMatterSpatialJetValueInjection :
    MatterCoordinateCarrier →L[ℝ] MatterCoordinateSpatialJetCarrier :=
  ContinuousLinearMap.inl ℝ MatterCoordinateCarrier
    (WithLp 2 (Fin 3 → MatterCoordinateCarrier))

/-- Inject one spatial derivative coordinate into the complete spatial
first-jet carrier. -/
def fixedMatterSpatialJetDerivativeInjection
    (direction : Fin 3) :
    MatterCoordinateCarrier →L[ℝ] MatterCoordinateSpatialJetCarrier := by
  let linear : MatterCoordinateCarrier →ₗ[ℝ]
      MatterCoordinateSpatialJetCarrier :=
    { toFun := fun value =>
        (0, WithLp.toLp 2 (Pi.single direction value))
      map_add' := by
        intro first second
        apply Prod.ext
        · simp
        · exact PiLp.single_add 2 direction
      map_smul' := by
        intro parameter value
        apply Prod.ext
        · simp
        · apply PiLp.ext
          intro index
          simp [PiLp.single_apply, Pi.single_apply, smul_ite] }
  exact ⟨linear, linear.continuous_of_finiteDimensional⟩

def fixedMatterFriedrichsValueVelocityCLM
    (point : BasePoint) :
    MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier :=
  (fixedOnShellTemporalVelocityCLM point).comp
    fixedMatterSpatialJetValueInjection

def fixedMatterFriedrichsDerivativeVelocityCLM
    (direction : Fin 3)
    (point : BasePoint) :
    MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier :=
  (fixedOnShellTemporalVelocityCLM point).comp
    (fixedMatterSpatialJetDerivativeInjection direction)

theorem fixedMatterFriedrichsValueVelocityCLM_continuous :
    Continuous fixedMatterFriedrichsValueVelocityCLM := by
  exact Continuous.clm_comp fixedOnShellTemporalVelocityCLM_continuous
    continuous_const

theorem fixedMatterFriedrichsDerivativeVelocityCLM_continuous
    (direction : Fin 3) :
    Continuous (fixedMatterFriedrichsDerivativeVelocityCLM direction) := by
  exact Continuous.clm_comp fixedOnShellTemporalVelocityCLM_continuous
    continuous_const

theorem fixedMatterFriedrichsValueVelocityCLM_contDiff_infty :
    ContDiff ℝ (⊤ : ℕ∞) fixedMatterFriedrichsValueVelocityCLM := by
  exact fixedOnShellTemporalVelocityCLM_contDiff_infty.clm_comp contDiff_const

theorem fixedMatterFriedrichsDerivativeVelocityCLM_contDiff_infty
    (direction : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fixedMatterFriedrichsDerivativeVelocityCLM direction) := by
  exact fixedOnShellTemporalVelocityCLM_contDiff_infty.clm_comp contDiff_const

private abbrev FixedMatterFriedrichsJetSlot := Option (Fin 3)

private def fixedMatterFriedrichsJetVelocityCLM
    (slot : FixedMatterFriedrichsJetSlot)
    (point : BasePoint) :
    MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier :=
  match slot with
  | none => fixedMatterFriedrichsValueVelocityCLM point
  | some direction =>
      fixedMatterFriedrichsDerivativeVelocityCLM direction point

private theorem fixedMatterFriedrichsJetVelocityCLM_continuous
    (slot : FixedMatterFriedrichsJetSlot) :
    Continuous (fixedMatterFriedrichsJetVelocityCLM slot) := by
  cases slot with
  | none => exact fixedMatterFriedrichsValueVelocityCLM_continuous
  | some direction =>
      exact fixedMatterFriedrichsDerivativeVelocityCLM_continuous direction

private def fixedMatterFriedrichsJetWord
    (slot : FixedMatterFriedrichsJetSlot) : List (Fin 3) :=
  match slot with
  | none => []
  | some direction => [direction]

private def fixedMatterFriedrichsCoefficientCompactPath
    (slot : FixedMatterFriedrichsJetSlot)
    (a b : DiracMatterSpatialCoordinates) :
    C(ℝ, BoundedContinuousFunction (Icc a b)
      (MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier)) := by
  let joint : C(ℝ × Icc a b,
      MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier) :=
    ⟨fun point => fixedMatterFriedrichsJetVelocityCLM slot
        (diracMatterSpacetimeCoordinatePoint point.1 point.2.1),
      (fixedMatterFriedrichsJetVelocityCLM_continuous slot).comp
        (diracMatterSpacetimeCoordinatePoint_joint_contDiff.continuous.comp
          (continuous_fst.prodMk
            (continuous_subtype_val.comp continuous_snd)))⟩
  exact ⟨fun time =>
      ContinuousMap.linearIsometryBoundedOfCompact
        (Icc a b)
        (MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier) ℝ
        (joint.curry time),
    (ContinuousMap.linearIsometryBoundedOfCompact
      (Icc a b)
      (MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier) ℝ).continuous.comp
      joint.curry.continuous⟩

private def fixedMatterSpatialClamp
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    C(DiracMatterSpatialCoordinates, Icc a b) :=
  ⟨fun space =>
      ⟨fun direction =>
          (projIcc (a direction) (b direction)
            (boxOrder direction) (space direction)).1,
        ⟨fun direction =>
            (projIcc (a direction) (b direction)
              (boxOrder direction) (space direction)).2.1,
          fun direction =>
            (projIcc (a direction) (b direction)
              (boxOrder direction) (space direction)).2.2⟩⟩,
    by
      apply Continuous.subtype_mk
      fun_prop⟩

private def fixedMatterFriedrichsCoefficientBoundedPath
    (slot : FixedMatterFriedrichsJetSlot)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    C(ℝ, BoundedContinuousFunction DiracMatterSpatialCoordinates
      (MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier)) := by
  let clamp := fixedMatterSpatialClamp a b boxOrder
  exact ⟨fun time =>
      (fixedMatterFriedrichsCoefficientCompactPath slot a b time
        ).compContinuous clamp,
    (BoundedContinuousFunction.continuous_compContinuous clamp).comp
      (fixedMatterFriedrichsCoefficientCompactPath slot a b).continuous⟩

private noncomputable def fixedMatterFriedrichsCoefficientLp
    (slot : FixedMatterFriedrichsJetSlot)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (time : ℝ) :
    Lp (MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier) ∞
      (volume.restrict (Icc a b)) := by
  letI : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    { measure_univ_lt_top := by simp [isCompact_Icc.measure_lt_top] }
  exact BoundedContinuousFunction.toLp ∞
    (volume.restrict (Icc a b)) ℝ
    (fixedMatterFriedrichsCoefficientBoundedPath slot a b boxOrder time)

private theorem fixedMatterFriedrichsCoefficientLp_continuous
    (slot : FixedMatterFriedrichsJetSlot)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    Continuous (fixedMatterFriedrichsCoefficientLp slot a b boxOrder) := by
  letI : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    { measure_univ_lt_top := by simp [isCompact_Icc.measure_lt_top] }
  exact (BoundedContinuousFunction.toLp ∞
    (volume.restrict (Icc a b)) ℝ).continuous.comp
      (fixedMatterFriedrichsCoefficientBoundedPath
        slot a b boxOrder).continuous

private theorem fixedMatterFriedrichsCoefficientLp_coe_ae
    (slot : FixedMatterFriedrichsJetSlot)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (time : ℝ) :
    fixedMatterFriedrichsCoefficientLp slot a b boxOrder time =ᵐ[
        volume.restrict (Icc a b)]
      fun space => fixedMatterFriedrichsJetVelocityCLM slot
        (diracMatterSpacetimeCoordinatePoint time space) := by
  letI : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    { measure_univ_lt_top := by simp [isCompact_Icc.measure_lt_top] }
  have read := BoundedContinuousFunction.coeFn_toLp
    (p := (∞ : ENNReal)) (volume.restrict (Icc a b)) ℝ
    (fixedMatterFriedrichsCoefficientBoundedPath slot a b boxOrder time)
  filter_upwards [read, ae_restrict_mem measurableSet_Icc]
    with space readAt spaceMem
  have readAt' :
      (fixedMatterFriedrichsCoefficientLp slot a b boxOrder time) space =
        fixedMatterFriedrichsCoefficientBoundedPath
          slot a b boxOrder time space := by
    simpa only [fixedMatterFriedrichsCoefficientLp] using readAt
  rw [readAt']
  change fixedMatterFriedrichsJetVelocityCLM slot
      (diracMatterSpacetimeCoordinatePoint time
        (fixedMatterSpatialClamp a b boxOrder space).1) = _
  congr 2
  funext direction
  exact congrArg Subtype.val
    (projIcc_of_mem (boxOrder direction)
      ⟨spaceMem.1 direction, spaceMem.2 direction⟩)

private def fixedMatterFriedrichsFiberEvaluation :
    (MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier) →L[ℝ]
      MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier :=
  isBoundedBilinearMap_apply.toContinuousLinearMap

private def fixedMatterFriedrichsJetOperator
    (index : ℕ)
    (slot : FixedMatterFriedrichsJetSlot)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (time : ℝ) :
    CauchySafeMatterSpatialL2 a b →L[ℝ]
      CauchySafeMatterSpatialL2 a b :=
  ((fixedMatterFriedrichsFiberEvaluation.holderL
      (volume.restrict (Icc a b)) ∞ 2 2)
    (fixedMatterFriedrichsCoefficientLp slot a b boxOrder time)).comp
      (fixedMatterSpatialWordMollificationBoxCLM
        (fixedMatterFriedrichsBump index)
        (fixedMatterFriedrichsJetWord slot) a b)

private theorem fixedMatterFriedrichsJetOperator_continuous
    (index : ℕ)
    (slot : FixedMatterFriedrichsJetSlot)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    Continuous (fixedMatterFriedrichsJetOperator
      index slot a b boxOrder) := by
  apply Continuous.clm_comp
  · exact (fixedMatterFriedrichsFiberEvaluation.holderL
      (volume.restrict (Icc a b)) ∞ 2 2).continuous.comp
        (fixedMatterFriedrichsCoefficientLp_continuous
          slot a b boxOrder)
  · exact continuous_const

/-- The fixed source's all-spatial-word Friedrichs generator at resolution
`index`.  The four action slots are assembled once, rather than through
successive first- and second-derivative epochs. -/
def fixedMatterFriedrichsOperator
    (index : ℕ)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (time : ℝ) :
    CauchySafeMatterSpatialL2 a b →L[ℝ]
      CauchySafeMatterSpatialL2 a b :=
  ∑ slot : FixedMatterFriedrichsJetSlot,
    fixedMatterFriedrichsJetOperator index slot a b boxOrder time

/-- Pointwise source velocity read by the box Friedrichs generator. -/
def fixedMatterFriedrichsVelocityField
    (index : ℕ)
    (a b : DiracMatterSpatialCoordinates)
    (time : ℝ)
    (field : CauchySafeMatterSpatialL2 a b)
    (space : DiracMatterSpatialCoordinates) : MatterCoordinateCarrier :=
  fixedOnShellTemporalVelocityCLM
    (diracMatterSpacetimeCoordinatePoint time space)
    (fixedMatterSpatialWordMollificationBoxField
        (fixedMatterFriedrichsBump index) [] a b field space,
      WithLp.toLp 2 fun direction =>
        fixedMatterSpatialWordMollificationBoxField
          (fixedMatterFriedrichsBump index) [direction] a b field space)

private def fixedMatterFriedrichsJetVelocityField
    (index : ℕ)
    (slot : FixedMatterFriedrichsJetSlot)
    (a b : DiracMatterSpatialCoordinates)
    (time : ℝ)
    (field : CauchySafeMatterSpatialL2 a b)
    (space : DiracMatterSpatialCoordinates) : MatterCoordinateCarrier :=
  fixedMatterFriedrichsJetVelocityCLM slot
    (diracMatterSpacetimeCoordinatePoint time space)
    (fixedMatterSpatialWordMollificationBoxField
      (fixedMatterFriedrichsBump index)
      (fixedMatterFriedrichsJetWord slot) a b field space)

private theorem fixedMatterFriedrichsJetOperator_coe_ae
    (index : ℕ)
    (slot : FixedMatterFriedrichsJetSlot)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (time : ℝ)
    (field : CauchySafeMatterSpatialL2 a b) :
    fixedMatterFriedrichsJetOperator
        index slot a b boxOrder time field =ᵐ[
          volume.restrict (Icc a b)]
      fixedMatterFriedrichsJetVelocityField index slot a b time field := by
  have holderRead := ContinuousLinearMap.coeFn_holder (r := (2 : ENNReal))
    fixedMatterFriedrichsFiberEvaluation
    (fixedMatterFriedrichsCoefficientLp slot a b boxOrder time)
    (fixedMatterSpatialWordMollificationBoxCLM
      (fixedMatterFriedrichsBump index)
      (fixedMatterFriedrichsJetWord slot) a b field)
  have coefficientRead := fixedMatterFriedrichsCoefficientLp_coe_ae
    slot a b boxOrder time
  have fieldRead := fixedMatterSpatialWordMollificationBoxCLM_coe_ae
    (fixedMatterFriedrichsBump index)
    (fixedMatterFriedrichsJetWord slot) a b field
  filter_upwards [holderRead, coefficientRead, fieldRead]
    with space holderAt coefficientAt fieldAt
  change
    ((fixedMatterFriedrichsFiberEvaluation.holderL
        (volume.restrict (Icc a b)) ∞ 2 2
        (fixedMatterFriedrichsCoefficientLp slot a b boxOrder time))
      (fixedMatterSpatialWordMollificationBoxCLM
        (fixedMatterFriedrichsBump index)
        (fixedMatterFriedrichsJetWord slot) a b field)) space =
      fixedMatterFriedrichsFiberEvaluation
        ((fixedMatterFriedrichsCoefficientLp
          slot a b boxOrder time) space)
        ((fixedMatterSpatialWordMollificationBoxCLM
          (fixedMatterFriedrichsBump index)
          (fixedMatterFriedrichsJetWord slot) a b field) space) at holderAt
  change
    ((fixedMatterFriedrichsFiberEvaluation.holderL
        (volume.restrict (Icc a b)) ∞ 2 2
        (fixedMatterFriedrichsCoefficientLp slot a b boxOrder time))
      (fixedMatterSpatialWordMollificationBoxCLM
        (fixedMatterFriedrichsBump index)
        (fixedMatterFriedrichsJetWord slot) a b field)) space = _
  calc
    _ = fixedMatterFriedrichsFiberEvaluation
        ((fixedMatterFriedrichsCoefficientLp
          slot a b boxOrder time) space)
        ((fixedMatterSpatialWordMollificationBoxCLM
          (fixedMatterFriedrichsBump index)
          (fixedMatterFriedrichsJetWord slot) a b field) space) := holderAt
    _ = fixedMatterFriedrichsFiberEvaluation
        (fixedMatterFriedrichsJetVelocityCLM slot
          (diracMatterSpacetimeCoordinatePoint time space))
        ((fixedMatterSpatialWordMollificationBoxCLM
          (fixedMatterFriedrichsBump index)
          (fixedMatterFriedrichsJetWord slot) a b field) space) :=
      congrArg (fun coefficient =>
        fixedMatterFriedrichsFiberEvaluation coefficient
          ((fixedMatterSpatialWordMollificationBoxCLM
            (fixedMatterFriedrichsBump index)
            (fixedMatterFriedrichsJetWord slot) a b field) space))
        coefficientAt
    _ = fixedMatterFriedrichsFiberEvaluation
        (fixedMatterFriedrichsJetVelocityCLM slot
          (diracMatterSpacetimeCoordinatePoint time space))
        (fixedMatterSpatialWordMollificationBoxField
          (fixedMatterFriedrichsBump index)
          (fixedMatterFriedrichsJetWord slot) a b field space) :=
      congrArg
        (fixedMatterFriedrichsFiberEvaluation
          (fixedMatterFriedrichsJetVelocityCLM slot
            (diracMatterSpacetimeCoordinatePoint time space))) fieldAt
    _ = _ := rfl

private theorem fixedMatterFriedrichsJetVelocityField_sum
    (index : ℕ)
    (a b : DiracMatterSpatialCoordinates)
    (time : ℝ)
    (field : CauchySafeMatterSpatialL2 a b)
    (space : DiracMatterSpatialCoordinates) :
    (∑ slot : FixedMatterFriedrichsJetSlot,
      fixedMatterFriedrichsJetVelocityField
        index slot a b time field space) =
      fixedMatterFriedrichsVelocityField index a b time field space := by
  unfold fixedMatterFriedrichsJetVelocityField
    fixedMatterFriedrichsVelocityField
  rw [Fintype.sum_option]
  simp only [fixedMatterFriedrichsJetVelocityCLM,
    fixedMatterFriedrichsJetWord,
    fixedMatterFriedrichsValueVelocityCLM,
    fixedMatterFriedrichsDerivativeVelocityCLM,
    ContinuousLinearMap.comp_apply]
  rw [← map_sum, ← map_add]
  apply congrArg
  apply Prod.ext
  · rw [Prod.fst_add]
    simp [fixedMatterSpatialJetValueInjection,
      fixedMatterSpatialJetDerivativeInjection]
    change (∑ _ : Fin 3, (0 : MatterCoordinateCarrier)) = 0
    simp
  · apply PiLp.ext
    intro direction
    fin_cases direction <;>
      simp [fixedMatterSpatialJetValueInjection,
        fixedMatterSpatialJetDerivativeInjection,
        Fin.sum_univ_three]

/-- The four native action slots are the exact pointwise decomposition of the
Friedrichs matter velocity. -/
theorem fixedMatterFriedrichsVelocityField_eq_value_add_derivatives
    (index : ℕ)
    (a b : DiracMatterSpatialCoordinates)
    (time : ℝ)
    (field : CauchySafeMatterSpatialL2 a b)
    (space : DiracMatterSpatialCoordinates) :
    fixedMatterFriedrichsVelocityField index a b time field space =
      fixedMatterFriedrichsValueVelocityCLM
          (diracMatterSpacetimeCoordinatePoint time space)
          (fixedMatterSpatialWordMollificationBoxField
            (fixedMatterFriedrichsBump index) [] a b field space) +
        ∑ direction : Fin 3,
          fixedMatterFriedrichsDerivativeVelocityCLM direction
            (diracMatterSpacetimeCoordinatePoint time space)
            (fixedMatterSpatialWordMollificationBoxField
              (fixedMatterFriedrichsBump index) [direction] a b field space) := by
  rw [← fixedMatterFriedrichsJetVelocityField_sum]
  rw [Fintype.sum_option]
  rfl

theorem fixedMatterFriedrichsOperator_coe_ae
    (index : ℕ)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (time : ℝ)
    (field : CauchySafeMatterSpatialL2 a b) :
    fixedMatterFriedrichsOperator index a b boxOrder time field =ᵐ[
        volume.restrict (Icc a b)]
      fixedMatterFriedrichsVelocityField index a b time field := by
  have allTermReads : ∀ᵐ space ∂volume.restrict (Icc a b),
      ∀ slot : FixedMatterFriedrichsJetSlot,
        fixedMatterFriedrichsJetOperator
            index slot a b boxOrder time field space =
          fixedMatterFriedrichsJetVelocityField
            index slot a b time field space :=
    Filter.eventually_all.2 fun slot =>
      fixedMatterFriedrichsJetOperator_coe_ae
        index slot a b boxOrder time field
  have sumRead := Lp.coeFn_fun_finsetSum Finset.univ
    (fun slot : FixedMatterFriedrichsJetSlot =>
      fixedMatterFriedrichsJetOperator
        index slot a b boxOrder time field)
  filter_upwards [sumRead, allTermReads]
    with space sumAt readsAt
  have sumAt' :
      fixedMatterFriedrichsOperator index a b boxOrder time field space =
        ∑ slot : FixedMatterFriedrichsJetSlot,
          fixedMatterFriedrichsJetOperator
            index slot a b boxOrder time field space := by
    change ((∑ slot : FixedMatterFriedrichsJetSlot,
      fixedMatterFriedrichsJetOperator
        index slot a b boxOrder time) field) space = _
    exact sumAt
  calc
    _ = ∑ slot : FixedMatterFriedrichsJetSlot,
        fixedMatterFriedrichsJetOperator
          index slot a b boxOrder time field space := sumAt'
    _ = ∑ slot : FixedMatterFriedrichsJetSlot,
        fixedMatterFriedrichsJetVelocityField
          index slot a b time field space :=
      Finset.sum_congr rfl fun slot _ => readsAt slot
    _ = _ := fixedMatterFriedrichsJetVelocityField_sum
      index a b time field space

theorem fixedMatterFriedrichsOperator_continuous
    (index : ℕ)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    Continuous (fixedMatterFriedrichsOperator index a b boxOrder) := by
  apply continuous_finsetSum
  intro slot _
  exact fixedMatterFriedrichsJetOperator_continuous
    index slot a b boxOrder

/-- One exact source-generated Friedrichs evolution on a compact Cauchy box. -/
structure FixedP506L0CauchySafeMatterFriedrichsEvolution
    (index : ℕ)
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b) where
  coefficient : ℝ → CauchySafeMatterSpatialL2 a b
  initial : coefficient timeStart =
    fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 timeStart a b
  actionEvolution : ∀ time ∈ Icc timeStart timeEnd,
    HasDerivWithinAt coefficient
      (fixedMatterFriedrichsOperator index a b boxOrder time
        (coefficient time))
      (Icc timeStart timeEnd) time

/-- At every canonical mollifier scale, the fixed P506/L0 source generates an
exact Banach-space Friedrichs evolution on each compact Cauchy box.  The
constructor consumes only the source coefficients and canonical initial
slice; no residual, target state, or regularity conclusion is supplied to the
writer. -/
theorem nonempty_fixedP506L0CauchySafeMatterFriedrichsEvolution
    (index : ℕ)
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b) :
    Nonempty (FixedP506L0CauchySafeMatterFriedrichsEvolution
      index timeStart timeEnd a b timeOrder boxOrder) := by
  obtain ⟨coefficient, initial, evolution⟩ :=
    exists_galerkinLinearCoefficientCurve_on_Icc
      (fixedMatterFriedrichsOperator index a b boxOrder)
      (fixedMatterFriedrichsOperator_continuous index a b boxOrder)
      (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2
        timeStart a b)
      timeStart timeEnd timeOrder
  exact ⟨⟨coefficient, initial, fun time timeMem => by
    simpa [galerkinLinearVelocity] using evolution time timeMem⟩⟩

/-- The source interval and initial slice determine the Friedrichs
coefficient curve uniquely. -/
theorem FixedP506L0CauchySafeMatterFriedrichsEvolution.eqOn
    {index : ℕ}
    {timeStart timeEnd : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {timeOrder : timeStart ≤ timeEnd}
    {boxOrder : a ≤ b}
    (first second : FixedP506L0CauchySafeMatterFriedrichsEvolution
      index timeStart timeEnd a b timeOrder boxOrder) :
    EqOn first.coefficient second.coefficient (Icc timeStart timeEnd) := by
  apply galerkinLinearCoefficientCurve_eqOn_Icc
    (fixedMatterFriedrichsOperator index a b boxOrder)
    (fixedMatterFriedrichsOperator_continuous index a b boxOrder)
    first.coefficient second.coefficient
    (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 timeStart a b)
    timeStart timeEnd timeOrder first.initial second.initial
  · intro time timeMem
    simpa [galerkinLinearVelocity] using first.actionEvolution time timeMem
  · intro time timeMem
    simpa [galerkinLinearVelocity] using second.actionEvolution time timeMem

/-- The pointwise smooth spatial readout of a generated Friedrichs curve. -/
def FixedP506L0CauchySafeMatterFriedrichsEvolution.spatialField
    {index : ℕ}
    {timeStart timeEnd : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {timeOrder : timeStart ≤ timeEnd}
    {boxOrder : a ≤ b}
    (evolution : FixedP506L0CauchySafeMatterFriedrichsEvolution
      index timeStart timeEnd a b timeOrder boxOrder)
    (time : ℝ) : DiracMatterSpatialCoordinates → MatterCoordinateCarrier :=
  fixedMatterSpatialWordMollificationBoxField
    (fixedMatterFriedrichsBump index) [] a b (evolution.coefficient time)

theorem FixedP506L0CauchySafeMatterFriedrichsEvolution.spatialField_contDiff_infty
    {index : ℕ}
    {timeStart timeEnd : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {timeOrder : timeStart ≤ timeEnd}
    {boxOrder : a ≤ b}
    (evolution : FixedP506L0CauchySafeMatterFriedrichsEvolution
      index timeStart timeEnd a b timeOrder boxOrder)
    (time : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (evolution.spatialField time) := by
  exact fixedMatterSpatialWordMollificationBoxField_contDiff_infty
    (fixedMatterFriedrichsBump index) [] a b (evolution.coefficient time)

/-- The outer mollification of the coefficient curve obeys the exact
Friedrichs evolution law. -/
theorem FixedP506L0CauchySafeMatterFriedrichsEvolution.mollifiedL2_hasDerivWithinAt
    {index : ℕ}
    {timeStart timeEnd : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {timeOrder : timeStart ≤ timeEnd}
    {boxOrder : a ≤ b}
    (evolution : FixedP506L0CauchySafeMatterFriedrichsEvolution
      index timeStart timeEnd a b timeOrder boxOrder)
    (time : ℝ)
    (timeMem : time ∈ Icc timeStart timeEnd) :
    HasDerivWithinAt
      (fun candidateTime =>
        fixedMatterSpatialWordMollificationBoxCLM
          (fixedMatterFriedrichsBump index) [] a b
          (evolution.coefficient candidateTime))
      (fixedMatterSpatialWordMollificationBoxCLM
        (fixedMatterFriedrichsBump index) [] a b
        (fixedMatterFriedrichsOperator index a b boxOrder time
          (evolution.coefficient time)))
      (Icc timeStart timeEnd) time := by
  exact (fixedMatterSpatialWordMollificationBoxCLM
      (fixedMatterFriedrichsBump index) [] a b).hasFDerivAt
    |>.comp_hasDerivWithinAt time (evolution.actionEvolution time timeMem)

/-- Every spatial word of the generated smooth readout obeys the same exact
Friedrichs time law.  The word selects a derivative read; it does not select
a new evolution or a new regularity mechanism. -/
theorem FixedP506L0CauchySafeMatterFriedrichsEvolution.spatialWord_hasDerivWithinAt
    {index : ℕ}
    {timeStart timeEnd : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {timeOrder : timeStart ≤ timeEnd}
    {boxOrder : a ≤ b}
    (evolution : FixedP506L0CauchySafeMatterFriedrichsEvolution
      index timeStart timeEnd a b timeOrder boxOrder)
    (word : List (Fin 3))
    (time : ℝ)
    (timeMem : time ∈ Icc timeStart timeEnd)
    (space : DiracMatterSpatialCoordinates) :
    HasDerivWithinAt
      (fun candidateTime =>
        fixedMatterSpatialWordMollificationBoxField
          (fixedMatterFriedrichsBump index) word a b
          (evolution.coefficient candidateTime) space)
      (fixedMatterSpatialWordMollificationBoxField
        (fixedMatterFriedrichsBump index) word a b
        (fixedMatterFriedrichsOperator index a b boxOrder time
          (evolution.coefficient time)) space)
      (Icc timeStart timeEnd) time := by
  exact (fixedMatterSpatialWordMollificationBoxPointCLM
      (fixedMatterFriedrichsBump index) word a b space).hasFDerivAt
    |>.comp_hasDerivWithinAt time (evolution.actionEvolution time timeMem)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterFriedrichsEvolution
