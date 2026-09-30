import H0mework.Physics.DiracEvolution.SafeCanonicalMassProjectionConvergence
import H0mework.Physics.DiracEvolution.SafeCanonicalSameSourceGalerkinFamily
import H0mework.Physics.DiracEvolution.SafeCanonicalUniformTimeMassGeometry
import Mathlib.Analysis.ODE.Gronwall

namespace SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalForcedCrossLevelEnergy

open MeasureTheory Metric Set
open DiracExteriorMatterAction
open StageEightSourceGeneratedMatter
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalCrossLevelStability
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalSameSourceGalerkinFamily
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalUniformTimeMassGeometry
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterFiniteL2MassRead
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyEstimate
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterWeakGalerkinEnergy
open StageNineDiracMatterWeakGalerkinEvolution
open StageNineDiracMatterWeakSpatialGalerkinStiffness
open StageNineDiracMatterSpatialEnergyBalance
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false

attribute [local instance 10000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

private theorem fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateLp_norm_le
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C) :
    ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateLp
      time a b C operatorBound‖ ≤ C := by
  rw [fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateLp,
    Lp.norm_toLp, eLpNorm_exponent_top]
  calc
    ENNReal.toReal
        (eLpNormEssSup
          (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField time)
          (volume.restrict (Icc a b))) ≤
        ENNReal.toReal (ENNReal.ofReal C) := by
      apply ENNReal.toReal_mono ENNReal.ofReal_ne_top
      apply eLpNormEssSup_le_of_ae_bound
      filter_upwards [ae_restrict_mem measurableSet_Icc] with space spaceMem
      exact operatorBound space spaceMem
    _ = C := ENNReal.toReal_ofReal CNonnegative

private theorem fixedP506L0CauchySafeMatterL2MassAction_norm_apply_le
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (field : CauchySafeMatterSpatialL2 a b) :
    ‖fixedP506L0CauchySafeMatterL2MassAction
      time a b C operatorBound field‖ ≤
        ‖matterFiberMassRieszCoordinateBilinear‖ * C * ‖field‖ := by
  change
    ‖matterFiberMassRieszCoordinateBilinear.holder 2
      (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateLp
        time a b C operatorBound) field‖ ≤ _
  calc
    _ ≤ ‖matterFiberMassRieszCoordinateBilinear‖ *
          ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateLp
            time a b C operatorBound‖ * ‖field‖ :=
      matterFiberMassRieszCoordinateBilinear.norm_holder_apply_apply_le _ _
    _ ≤ ‖matterFiberMassRieszCoordinateBilinear‖ * C * ‖field‖ := by
      gcongr
      exact fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateLp_norm_le
        time a b C CNonnegative operatorBound

private theorem fixedP506L0CauchySafeMatterL2MassForm_abs_le
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (first second : CauchySafeMatterSpatialL2 a b) :
    |fixedP506L0CauchySafeMatterL2MassForm
        time a b C operatorBound first second| ≤
      ‖matterFiberMassRieszCoordinateBilinear‖ * C *
        ‖first‖ * ‖second‖ := by
  change |inner ℝ
    (fixedP506L0CauchySafeMatterL2MassAction
      time a b C operatorBound first) second| ≤ _
  calc
    _ ≤ ‖fixedP506L0CauchySafeMatterL2MassAction
          time a b C operatorBound first‖ * ‖second‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (‖matterFiberMassRieszCoordinateBilinear‖ * C *
          ‖first‖) * ‖second‖ := by
      gcongr
      exact fixedP506L0CauchySafeMatterL2MassAction_norm_apply_le
        time a b C CNonnegative operatorBound first
    _ = _ := by ring

/-- The exact energy derivative when the finite weak equation carries one
explicit action-owned forcing leg. -/
private theorem galerkinWeakEnergy_hasDerivWithinAt_of_forcing
    (massForm massDerivative : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (stiffnessForm : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (coefficient : ℝ → H)
    (velocity forcing : H)
    (set : Set ℝ)
    (time : ℝ)
    (massHasDeriv : HasDerivWithinAt massForm (massDerivative time) set time)
    (coefficientHasDeriv : HasDerivWithinAt coefficient velocity set time)
    (massSymmetric : ∀ first second,
      massForm time first second = massForm time second first)
    (weakEquation :
      massForm time velocity (coefficient time) +
        stiffnessForm time (coefficient time) (coefficient time) =
      massForm time forcing (coefficient time)) :
    HasDerivWithinAt (galerkinWeakEnergy massForm coefficient)
      (galerkinWeakEnergyRate massDerivative stiffnessForm coefficient time +
        2 * massForm time forcing (coefficient time))
      set time := by
  have firstApplication := massHasDeriv.clm_apply coefficientHasDeriv
  have fullDerivative := firstApplication.clm_apply coefficientHasDeriv
  have velocityPairing :
      massForm time velocity (coefficient time) =
        -stiffnessForm time (coefficient time) (coefficient time) +
          massForm time forcing (coefficient time) := by
    linarith [weakEquation]
  have derivativeValue :
      ((massDerivative time (coefficient time) + massForm time velocity)
          (coefficient time) +
        massForm time (coefficient time) velocity) =
        galerkinWeakEnergyRate massDerivative stiffnessForm coefficient time +
          2 * massForm time forcing (coefficient time) := by
    simp only [add_apply]
    rw [massSymmetric (coefficient time) velocity, velocityPairing]
    unfold galerkinWeakEnergyRate
    ring
  change HasDerivWithinAt
    (fun candidateTime ↦
      massForm candidateTime (coefficient candidateTime)
        (coefficient candidateTime))
    _ set time
  exact fullDerivative.congr_deriv derivativeValue

/-- A forced finite energy obeys the same Grönwall law with one explicit
uniform forcing budget. -/
private theorem galerkinWeakEnergy_norm_le_of_modeUniformRate_forced
    (massForm massDerivative : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (stiffnessForm : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (coefficient velocity forcing : ℝ → H)
    (a b K ε : ℝ)
    (massHasDeriv : ∀ time ∈ Set.Ico a b,
      HasDerivWithinAt massForm (massDerivative time) (Set.Ici time) time)
    (coefficientHasDeriv : ∀ time ∈ Set.Ico a b,
      HasDerivWithinAt coefficient (velocity time) (Set.Ici time) time)
    (massSymmetric : ∀ time ∈ Set.Ico a b, ∀ first second,
      massForm time first second = massForm time second first)
    (weakEquation : ∀ time ∈ Set.Ico a b,
      massForm time (velocity time) (coefficient time) +
        stiffnessForm time (coefficient time) (coefficient time) =
      massForm time (forcing time) (coefficient time))
    (energyContinuous :
      ContinuousOn (galerkinWeakEnergy massForm coefficient) (Set.Icc a b))
    (rateBound : ∀ time ∈ Set.Ico a b,
      ‖galerkinWeakEnergyRate massDerivative stiffnessForm coefficient time +
          2 * massForm time (forcing time) (coefficient time)‖ ≤
        K * ‖galerkinWeakEnergy massForm coefficient time‖ + ε) :
    ∀ time ∈ Set.Icc a b,
      ‖galerkinWeakEnergy massForm coefficient time‖ ≤
        gronwallBound
          ‖galerkinWeakEnergy massForm coefficient a‖ K ε (time - a) := by
  intro time timeMem
  exact norm_le_gronwallBound_of_norm_deriv_right_le
    energyContinuous
    (fun candidate candidateMem ↦
      galerkinWeakEnergy_hasDerivWithinAt_of_forcing
        massForm massDerivative stiffnessForm coefficient
        (velocity candidate) (forcing candidate) (Set.Ici candidate) candidate
        (massHasDeriv candidate candidateMem)
        (coefficientHasDeriv candidate candidateMem)
        (massSymmetric candidate candidateMem)
        (weakEquation candidate candidateMem))
    (le_refl _)
    rateBound time timeMem

private def canonicalCrossLevelError
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (time : ℝ) :
    FixedP506L0CauchySafeMatterCanonicalCoefficient a b secondCount :=
  fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
      timeStart timeEnd timeOrder a b secondCount time -
    canonicalCoefficientEmbedding a b countMonotone
      (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
        timeStart timeEnd timeOrder a b firstCount time)

private def canonicalCrossLevelForcing
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (time : ℝ) :
    FixedP506L0CauchySafeMatterCanonicalCoefficient a b secondCount :=
  fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
      a b secondCount time
      (canonicalCoefficientEmbedding a b countMonotone
        (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
          timeStart timeEnd timeOrder a b firstCount time)) -
    canonicalCoefficientEmbedding a b countMonotone
      (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
        a b firstCount time
        (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
          timeStart timeEnd timeOrder a b firstCount time))

private theorem canonicalCrossLevelError_evolution
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (time : ℝ)
    (timeMem : time ∈ Icc timeStart timeEnd) :
    HasDerivWithinAt
      (canonicalCrossLevelError timeStart timeEnd timeOrder a b countMonotone)
      (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
          a b secondCount time
          (canonicalCrossLevelError
            timeStart timeEnd timeOrder a b countMonotone time) +
        canonicalCrossLevelForcing
          timeStart timeEnd timeOrder a b countMonotone time)
      (Icc timeStart timeEnd) time := by
  let embedding :
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b firstCount →L[ℝ]
        FixedP506L0CauchySafeMatterCanonicalCoefficient a b secondCount :=
    (canonicalCoefficientEmbeddingLinearMap a b countMonotone
      ).toContinuousLinearMap
  have largeEvolution :=
    fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_evolution
      timeStart timeEnd timeOrder a b secondCount time timeMem
  have smallEvolution :=
    fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_evolution
      timeStart timeEnd timeOrder a b firstCount time timeMem
  have embeddedEvolution : HasDerivWithinAt
      (fun candidateTime ↦ embedding
        (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
          timeStart timeEnd timeOrder a b firstCount candidateTime))
      (embedding
        (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
          a b firstCount time
          (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
            timeStart timeEnd timeOrder a b firstCount time)))
      (Icc timeStart timeEnd) time :=
    embedding.hasFDerivAt.comp_hasDerivWithinAt time smallEvolution
  apply (largeEvolution.sub embeddedEvolution).congr_deriv
  change
    fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
          a b secondCount time
          (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
            timeStart timeEnd timeOrder a b secondCount time) -
        canonicalCoefficientEmbedding a b countMonotone
          (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
            a b firstCount time
            (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
              timeStart timeEnd timeOrder a b firstCount time)) =
      fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
          a b secondCount time
          (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
              timeStart timeEnd timeOrder a b secondCount time -
            canonicalCoefficientEmbedding a b countMonotone
              (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
                timeStart timeEnd timeOrder a b firstCount time)) +
        (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
            a b secondCount time
            (canonicalCoefficientEmbedding a b countMonotone
              (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
                timeStart timeEnd timeOrder a b firstCount time)) -
          canonicalCoefficientEmbedding a b countMonotone
            (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
              a b firstCount time
              (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
                timeStart timeEnd timeOrder a b firstCount time)))
  rw [(fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
    a b secondCount time).map_sub]
  abel

private theorem canonicalCrossLevelError_forcedWeakEquation
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (time : ℝ)
    (test : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b secondCount) :
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b secondCount time
        (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
            a b secondCount time
            (canonicalCrossLevelError
              timeStart timeEnd timeOrder a b countMonotone time) +
          canonicalCrossLevelForcing
            timeStart timeEnd timeOrder a b countMonotone time)
        test +
      fixedP506L0CauchySafeMatterWeakStiffnessForm
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
          a b secondCount)
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
          a b secondCount)
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
          a b secondCount)
        time
        (canonicalCrossLevelError
          timeStart timeEnd timeOrder a b countMonotone time)
        test =
      fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b secondCount time
        (canonicalCrossLevelForcing
          timeStart timeEnd timeOrder a b countMonotone time)
        test := by
  have actionEquation := galerkinWeakActionOperator_mass_equation
    (galerkinWeakMassOperator
      (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b secondCount))
    (fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator
      a b secondCount)
    time
    (canonicalCrossLevelError
      timeStart timeEnd timeOrder a b countMonotone time)
    (fixedP506L0CauchySafeMatterWeakMassOperator_isInvertible
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b secondCount)
      (fun mode ↦
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
          a b secondCount mode).continuous)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
        a b secondCount)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinSynthesis_faithful
        a b secondCount)
      time)
  have tested := congrArg (fun value ↦ inner ℝ value test) actionEquation
  rw [inner_add_left, inner_zero_left,
    real_inner_galerkinWeakMassOperator] at tested
  have tested' :
      fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b secondCount time
          (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
            a b secondCount time
            (canonicalCrossLevelError
              timeStart timeEnd timeOrder a b countMonotone time)) test +
        fixedP506L0CauchySafeMatterWeakStiffnessForm
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b secondCount)
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
            a b secondCount)
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
            a b secondCount)
          time
          (canonicalCrossLevelError
            timeStart timeEnd timeOrder a b countMonotone time) test = 0 := by
    simpa only [fixedP506L0CauchySafeMatterCanonicalWeakActionOperator,
      fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator,
      fixedP506L0CauchySafeMatterWeakStiffnessOperator_readout,
      fixedP506L0CauchySafeMatterWeakStiffnessForm,
      diracMatterWeakStiffnessForm_apply] using tested
  simp only [map_add, add_apply]
  linarith [tested']

private theorem fixedP506L0CauchySafeMatterWeakMassForm_abs_le
    {modeCount : ℕ}
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (a b : DiracMatterSpatialCoordinates)
    (basisZeroOutside :
      DiracMatterSpatialBasisSupportedInBoxInterior basis a b)
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    (time : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (first second : DiracMatterGalerkinCoefficient modeCount) :
    |fixedP506L0CauchySafeMatterWeakMassForm
        basis basisContinuous basisCompact time first second| ≤
      ‖matterFiberMassRieszCoordinateBilinear‖ * C *
        ‖fixedMatterTrialL2 basis basisContinuous basisCompact first a b‖ *
        ‖fixedMatterTrialL2 basis basisContinuous basisCompact second a b‖ := by
  have finiteRead := fixedP506L0CauchySafeMatterWeakMassForm_eq_l2MassForm_trial
    basis basisContinuous basisCompact time a b basisZeroOutside
      C operatorBound first second
  rw [finiteRead]
  exact fixedP506L0CauchySafeMatterL2MassForm_abs_le
    time a b C CNonnegative operatorBound _ _

private theorem fixedP506L0CauchySafeMatterWeakMassForm_coercive_of_pointwise
    {modeCount : ℕ}
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (a b : DiracMatterSpatialCoordinates)
    (basisZeroOutside :
      DiracMatterSpatialBasisSupportedInBoxInterior basis a b)
    (C : ℝ)
    (time : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (κ : ℝ)
    (pointwiseCoercivity :
      ∀ space ∈ Icc a b, ∀ field : MatterCoordinateCarrier,
        κ * ‖field‖ ^ 2 ≤
          fixedP506L0CauchySafeMatterFiberMassEnergy
            (time, space) field)
    (coefficient : DiracMatterGalerkinCoefficient modeCount) :
    κ * ‖fixedMatterTrialL2 basis basisContinuous basisCompact
        coefficient a b‖ *
        ‖fixedMatterTrialL2 basis basisContinuous basisCompact
          coefficient a b‖ ≤
      fixedP506L0CauchySafeMatterWeakMassForm
        basis basisContinuous basisCompact time coefficient coefficient := by
  rw [fixedP506L0CauchySafeMatterWeakMassForm_eq_l2MassForm_trial
    basis basisContinuous basisCompact time a b basisZeroOutside
      C operatorBound coefficient coefficient]
  exact fixedP506L0CauchySafeMatterL2MassForm_coercive_of_pointwise
    time a b C operatorBound κ pointwiseCoercivity _

private theorem fixedP506L0CauchySafeMatterCanonicalSynthesis_eq_trialL2
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (coefficient : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b testCount) :
    fixedP506L0CauchySafeMatterCanonicalSynthesis a b testCount coefficient =
      fixedMatterTrialL2
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
        (fun mode ↦
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
            a b testCount mode).continuous)
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
          a b testCount)
        coefficient a b := by
  rfl

private theorem forcedEnergyRate_norm_le
    (energy rate forcingPairing fieldNorm B δ κ K : ℝ)
    (energyNonnegative : 0 ≤ energy)
    (κPositive : 0 < κ)
    (rateBound : ‖rate‖ ≤ K * energy)
    (forcingBound : |forcingPairing| ≤ B * δ * fieldNorm)
    (coercivity : κ * fieldNorm * fieldNorm ≤ energy) :
    ‖rate + 2 * forcingPairing‖ ≤
      (K + κ⁻¹) * ‖energy‖ + (B * δ) ^ 2 := by
  have κNonnegative : 0 ≤ κ⁻¹ := inv_nonneg.mpr κPositive.le
  have fieldNormSq : fieldNorm ^ 2 ≤ κ⁻¹ * energy := by
    calc
      fieldNorm ^ 2 = κ⁻¹ * (κ * fieldNorm * fieldNorm) := by
        field_simp [ne_of_gt κPositive]
      _ ≤ κ⁻¹ * energy :=
        mul_le_mul_of_nonneg_left coercivity κNonnegative
  have forcingTwice : 2 * |forcingPairing| ≤
      (B * δ) ^ 2 + fieldNorm ^ 2 := by
    calc
      2 * |forcingPairing| ≤ 2 * (B * δ * fieldNorm) := by
        gcongr
      _ ≤ (B * δ) ^ 2 + fieldNorm ^ 2 := by
        nlinarith [sq_nonneg (B * δ - fieldNorm)]
  rw [Real.norm_of_nonneg energyNonnegative]
  calc
    ‖rate + 2 * forcingPairing‖ ≤ ‖rate‖ + ‖2 * forcingPairing‖ :=
      norm_add_le _ _
    _ = ‖rate‖ + 2 * |forcingPairing| := by
      simp only [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ K * energy + ((B * δ) ^ 2 + fieldNorm ^ 2) :=
      add_le_add rateBound forcingTwice
    _ ≤ K * energy + ((B * δ) ^ 2 + κ⁻¹ * energy) := by
      gcongr
    _ = (K + κ⁻¹) * energy + (B * δ) ^ 2 := by ring

def canonicalCrossLevelPhysicalError
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (time : ℝ) : CauchySafeMatterSpatialL2 a b :=
  fixedP506L0CauchySafeMatterCanonicalSynthesis a b secondCount
    (canonicalCrossLevelError
      timeStart timeEnd timeOrder a b countMonotone time)

def canonicalCrossLevelProjectionTail
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (time : ℝ) : CauchySafeMatterSpatialL2 a b :=
  fixedP506L0CauchySafeMatterCanonicalSynthesis a b secondCount
    (canonicalCrossLevelForcing
      timeStart timeEnd timeOrder a b countMonotone time)

def canonicalCrossLevelPhysicalErrorNorm
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (time : ℝ) : ℝ :=
  ‖canonicalCrossLevelPhysicalError
    timeStart timeEnd timeOrder a b countMonotone time‖

def canonicalCrossLevelProjectionTailNorm
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (time : ℝ) : ℝ :=
  ‖canonicalCrossLevelProjectionTail
    timeStart timeEnd timeOrder a b countMonotone time‖

def canonicalCrossLevelWeakEnergy
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (time : ℝ) : ℝ :=
  galerkinWeakEnergy
    (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b secondCount)
    (canonicalCrossLevelError
      timeStart timeEnd timeOrder a b countMonotone)
    time

private def canonicalCrossLevelWeakEnergyRate
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (time : ℝ) : ℝ :=
  galerkinWeakEnergyRate
    (fixedP506L0CauchySafeMatterWeakMassFormDerivative
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b secondCount)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
        a b secondCount)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
        a b secondCount))
    (fixedP506L0CauchySafeMatterWeakStiffnessForm
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b secondCount)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
        a b secondCount)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
        a b secondCount))
    (canonicalCrossLevelError
      timeStart timeEnd timeOrder a b countMonotone)
    time

private def canonicalCrossLevelForcingPairing
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (time : ℝ) : ℝ :=
  fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b secondCount time
    (canonicalCrossLevelForcing
      timeStart timeEnd timeOrder a b countMonotone time)
    (canonicalCrossLevelError
      timeStart timeEnd timeOrder a b countMonotone time)

private theorem canonicalCrossLevelForcingPairing_abs_le
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (time : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C) :
    |canonicalCrossLevelForcingPairing
        timeStart timeEnd timeOrder a b countMonotone time| ≤
      ‖matterFiberMassRieszCoordinateBilinear‖ * C *
        canonicalCrossLevelProjectionTailNorm
          timeStart timeEnd timeOrder a b countMonotone time *
        canonicalCrossLevelPhysicalErrorNorm
          timeStart timeEnd timeOrder a b countMonotone time := by
  let basis :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b secondCount
  let basisContinuous := fun mode ↦
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
      a b secondCount mode).continuous
  let basisCompact :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
      a b secondCount
  simpa only [canonicalCrossLevelForcingPairing,
    canonicalCrossLevelProjectionTail, canonicalCrossLevelPhysicalError,
    canonicalCrossLevelProjectionTailNorm,
    canonicalCrossLevelPhysicalErrorNorm,
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm,
    fixedP506L0CauchySafeMatterCanonicalSynthesis_eq_trialL2,
    basis, basisContinuous, basisCompact] using
    fixedP506L0CauchySafeMatterWeakMassForm_abs_le
      basis basisContinuous basisCompact a b
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_zeroOutside
          a b secondCount)
      C CNonnegative time operatorBound
      (canonicalCrossLevelForcing
        timeStart timeEnd timeOrder a b countMonotone time)
      (canonicalCrossLevelError
        timeStart timeEnd timeOrder a b countMonotone time)

private theorem canonicalCrossLevelWeakEnergy_coercive_of_pointwise
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (C κ : ℝ)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (time : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (pointwiseCoercivity :
      ∀ space ∈ Icc a b, ∀ field : MatterCoordinateCarrier,
        κ * ‖field‖ ^ 2 ≤
          fixedP506L0CauchySafeMatterFiberMassEnergy
            (time, space) field) :
    κ *
        canonicalCrossLevelPhysicalErrorNorm
          timeStart timeEnd timeOrder a b countMonotone time *
        canonicalCrossLevelPhysicalErrorNorm
          timeStart timeEnd timeOrder a b countMonotone time ≤
      canonicalCrossLevelWeakEnergy
        timeStart timeEnd timeOrder a b countMonotone time := by
  let basis :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b secondCount
  let basisContinuous := fun mode ↦
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
      a b secondCount mode).continuous
  let basisCompact :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
      a b secondCount
  simpa only [canonicalCrossLevelPhysicalError,
    canonicalCrossLevelPhysicalErrorNorm,
    canonicalCrossLevelWeakEnergy,
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm,
    fixedP506L0CauchySafeMatterCanonicalSynthesis_eq_trialL2,
    galerkinWeakEnergy, basis, basisContinuous, basisCompact] using
    fixedP506L0CauchySafeMatterWeakMassForm_coercive_of_pointwise
      basis basisContinuous basisCompact a b
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_zeroOutside
          a b secondCount)
      C time operatorBound κ pointwiseCoercivity
      (canonicalCrossLevelError
        timeStart timeEnd timeOrder a b countMonotone time)

private def canonicalForcedPhysicalNorm
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (error : ℝ →
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount)
    (time : ℝ) : ℝ :=
  ‖fixedP506L0CauchySafeMatterCanonicalSynthesis
    a b testCount (error time)‖

private def canonicalForcedWeakEnergy
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (error : ℝ →
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount)
    (time : ℝ) : ℝ :=
  galerkinWeakEnergy
    (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount)
    error time

private def canonicalForcedWeakEnergyRate
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (error : ℝ →
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount)
    (time : ℝ) : ℝ :=
  galerkinWeakEnergyRate
    (fixedP506L0CauchySafeMatterWeakMassFormDerivative
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
        a b testCount)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
        a b testCount))
    (fixedP506L0CauchySafeMatterWeakStiffnessForm
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
        a b testCount)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
        a b testCount))
    error time

private def canonicalForcedPairing
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (error forcing : ℝ →
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount)
    (time : ℝ) : ℝ :=
  fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount time
    (forcing time) (error time)

private theorem canonicalForcedError_forcedWeakEquation
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (error forcing : ℝ →
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount)
    (time : ℝ)
    (test : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b testCount) :
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount time
        (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
            a b testCount time (error time) + forcing time)
        test +
      fixedP506L0CauchySafeMatterWeakStiffnessForm
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
          a b testCount)
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
          a b testCount)
        time (error time) test =
      fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount time
        (forcing time) test := by
  have actionEquation := galerkinWeakActionOperator_mass_equation
    (galerkinWeakMassOperator
      (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount))
    (fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator
      a b testCount)
    time (error time)
    (fixedP506L0CauchySafeMatterWeakMassOperator_isInvertible
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
      (fun mode ↦
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
          a b testCount mode).continuous)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
        a b testCount)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinSynthesis_faithful
        a b testCount)
      time)
  have tested := congrArg (fun value ↦ inner ℝ value test) actionEquation
  rw [inner_add_left, inner_zero_left,
    real_inner_galerkinWeakMassOperator] at tested
  have tested' :
      fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount time
          (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
            a b testCount time (error time)) test +
        fixedP506L0CauchySafeMatterWeakStiffnessForm
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
            a b testCount)
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
            a b testCount)
          time (error time) test = 0 := by
    simpa only [fixedP506L0CauchySafeMatterCanonicalWeakActionOperator,
      fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator,
      fixedP506L0CauchySafeMatterWeakStiffnessOperator_readout,
      fixedP506L0CauchySafeMatterWeakStiffnessForm,
      diracMatterWeakStiffnessForm_apply] using tested
  simp only [map_add, add_apply]
  linarith [tested']

private theorem canonicalForcedEnergyRate_norm_le
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    (κ : ℝ)
    (κPositive : 0 < κ)
    (K : ℝ)
    (operatorBound : ∀ time ∈ Icc timeStart timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
          time space‖ ≤ C)
    (pointwiseCoercivity :
      ∀ time ∈ Icc timeStart timeEnd,
        ∀ space ∈ Icc a b, ∀ field : MatterCoordinateCarrier,
          κ * ‖field‖ ^ 2 ≤
            fixedP506L0CauchySafeMatterFiberMassEnergy
              (time, space) field)
    (rateBound : ∀ (candidateModeCount : ℕ)
      (basis : Fin candidateModeCount →
        DiracMatterSpatialCoordinates → ℝ)
      (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
      (basisCompact : ∀ mode, HasCompactSupport (basis mode)),
      DiracMatterSpatialBasisSupportedInBoxInterior basis a b →
      ∀ coefficient : ℝ → DiracMatterGalerkinCoefficient candidateModeCount,
        ∀ time ∈ Icc timeStart timeEnd,
          ‖galerkinWeakEnergyRate
              (fixedP506L0CauchySafeMatterWeakMassFormDerivative
                basis basisRegular basisCompact)
              (fixedP506L0CauchySafeMatterWeakStiffnessForm
                basis basisRegular basisCompact)
              coefficient time‖ ≤
            K * galerkinWeakEnergy
              (fixedP506L0CauchySafeMatterWeakMassForm
                basis (fun mode ↦ (basisRegular mode).continuous)
                  basisCompact)
              coefficient time)
    (testCount : ℕ)
    (error forcing : ℝ →
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount)
    (δ : ℝ)
    (forcingBound : ∀ time ∈ Icc timeStart timeEnd,
      ‖fixedP506L0CauchySafeMatterCanonicalSynthesis
        a b testCount (forcing time)‖ ≤ δ)
    (time : ℝ)
    (timeMem : time ∈ Ico timeStart timeEnd) :
    ‖canonicalForcedWeakEnergyRate a b testCount error time +
        2 * canonicalForcedPairing a b testCount error forcing time‖ ≤
      (K + κ⁻¹) *
          ‖canonicalForcedWeakEnergy a b testCount error time‖ +
        ((‖matterFiberMassRieszCoordinateBilinear‖ * C) * δ) ^ 2 := by
  let basis :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount
  let basisRegular :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
      a b testCount
  let basisContinuous := fun mode ↦ (basisRegular mode).continuous
  let basisCompact :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
      a b testCount
  let basisZeroOutside :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_zeroOutside
      a b testCount
  have timeMemIcc : time ∈ Icc timeStart timeEnd :=
    Ico_subset_Icc_self timeMem
  have energyNonnegative :
      0 ≤ canonicalForcedWeakEnergy a b testCount error time := by
    simpa only [canonicalForcedWeakEnergy, galerkinWeakEnergy,
      basis, basisContinuous, basisCompact,
      fixedP506L0CauchySafeMatterCanonicalWeakMassForm] using
      fixedP506L0CauchySafeMatterWeakMassForm_nonnegative
        basis basisContinuous basisCompact time (error time)
  have ordinaryRateBound :
      ‖canonicalForcedWeakEnergyRate a b testCount error time‖ ≤
        K * canonicalForcedWeakEnergy a b testCount error time := by
    simpa only [canonicalForcedWeakEnergyRate, canonicalForcedWeakEnergy,
      basis, basisRegular, basisContinuous, basisCompact,
      fixedP506L0CauchySafeMatterCanonicalWeakMassForm]
      using rateBound _ basis basisRegular basisCompact basisZeroOutside
        error time timeMemIcc
  have forcingPairingBound :
      |canonicalForcedPairing a b testCount error forcing time| ≤
        (‖matterFiberMassRieszCoordinateBilinear‖ * C) * δ *
          canonicalForcedPhysicalNorm a b testCount error time := by
    have massBound := fixedP506L0CauchySafeMatterWeakMassForm_abs_le
      basis basisContinuous basisCompact a b basisZeroOutside
      C CNonnegative time (operatorBound time timeMemIcc)
        (forcing time) (error time)
    calc
      |canonicalForcedPairing a b testCount error forcing time| ≤
          ‖matterFiberMassRieszCoordinateBilinear‖ * C *
            ‖fixedP506L0CauchySafeMatterCanonicalSynthesis
              a b testCount (forcing time)‖ *
            canonicalForcedPhysicalNorm a b testCount error time := by
        simpa only [canonicalForcedPairing, canonicalForcedPhysicalNorm,
          fixedP506L0CauchySafeMatterCanonicalWeakMassForm,
          fixedP506L0CauchySafeMatterCanonicalSynthesis_eq_trialL2,
          basis, basisContinuous, basisCompact] using massBound
      _ ≤ (‖matterFiberMassRieszCoordinateBilinear‖ * C) * δ *
            canonicalForcedPhysicalNorm a b testCount error time := by
        have scaleNonnegative :
            0 ≤ ‖matterFiberMassRieszCoordinateBilinear‖ * C :=
          mul_nonneg
            (norm_nonneg matterFiberMassRieszCoordinateBilinear)
            CNonnegative
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (forcingBound time timeMemIcc)
            scaleNonnegative)
          (by exact norm_nonneg _)
  have energyCoercivity :
      κ * canonicalForcedPhysicalNorm a b testCount error time *
          canonicalForcedPhysicalNorm a b testCount error time ≤
        canonicalForcedWeakEnergy a b testCount error time := by
    simpa only [canonicalForcedPhysicalNorm, canonicalForcedWeakEnergy,
      galerkinWeakEnergy,
      basis, basisContinuous, basisCompact,
      fixedP506L0CauchySafeMatterCanonicalWeakMassForm,
      fixedP506L0CauchySafeMatterCanonicalSynthesis_eq_trialL2] using
      fixedP506L0CauchySafeMatterWeakMassForm_coercive_of_pointwise
        basis basisContinuous basisCompact a b basisZeroOutside
        C time (operatorBound time timeMemIcc)
        κ (pointwiseCoercivity time timeMemIcc) (error time)
  exact forcedEnergyRate_norm_le
    (canonicalForcedWeakEnergy a b testCount error time)
    (canonicalForcedWeakEnergyRate a b testCount error time)
    (canonicalForcedPairing a b testCount error forcing time)
    (canonicalForcedPhysicalNorm a b testCount error time)
    (‖matterFiberMassRieszCoordinateBilinear‖ * C) δ κ K
    energyNonnegative κPositive ordinaryRateBound forcingPairingBound
    energyCoercivity

def CanonicalForcedPhysicalErrorEstimate
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C κ K : ℝ) : Prop :=
  ∀ (testCount : ℕ)
    (error forcing : ℝ →
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount),
    (∀ time ∈ Icc timeStart timeEnd,
      HasDerivWithinAt error
        (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
            a b testCount time (error time) +
          forcing time)
        (Icc timeStart timeEnd) time) →
    ∀ δ : ℝ,
      (∀ time ∈ Icc timeStart timeEnd,
        ‖fixedP506L0CauchySafeMatterCanonicalSynthesis
          a b testCount (forcing time)‖ ≤ δ) →
      ∀ time ∈ Icc timeStart timeEnd,
        κ *
            ‖fixedP506L0CauchySafeMatterCanonicalSynthesis
              a b testCount (error time)‖ ^ 2 ≤
          gronwallBound
            ‖galerkinWeakEnergy
              (fixedP506L0CauchySafeMatterCanonicalWeakMassForm
                a b testCount)
              error timeStart‖
            (K + κ⁻¹)
            ((‖matterFiberMassRieszCoordinateBilinear‖ * C * δ) ^ 2)
            (time - timeStart)

/-- A finite action-owned forced Galerkin curve inherits a physical `L²`
energy estimate from one source-owned forcing bound.  The curve and forcing
remain explicit inputs; no limiting family or target state enters this finite
mechanism. -/
theorem exists_fixedP506L0CauchySafeMatterCanonicalForcedPhysicalError_bound
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    ∃ C κ K : ℝ, 0 ≤ C ∧ 0 < κ ∧ 0 ≤ K ∧
      CanonicalForcedPhysicalErrorEstimate timeStart timeEnd a b C κ K := by
  obtain ⟨C, CNonnegative, operatorBound⟩ :=
    exists_fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateBoundOnBox
      timeStart timeEnd a b
  obtain ⟨κ, κPositive, pointwiseCoercivity⟩ :=
    exists_fixedP506L0CauchySafeMatterFiberMassCoercivityOnTimeSpaceBox
      timeStart timeEnd timeOrder a b boxOrder
  obtain ⟨K, KNonnegative, rateBound⟩ :=
    exists_fixedModeUniformGalerkinWeakEnergyRateBoundOnBox
      timeStart timeEnd a b timeOrder boxOrder
  refine ⟨C, κ, K, CNonnegative, κPositive, KNonnegative, ?_⟩
  unfold CanonicalForcedPhysicalErrorEstimate
  intro testCount error forcing errorEvolution δ forcingBound time timeMem
  let basis :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount
  let basisRegular :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
      a b testCount
  let basisContinuous := fun mode ↦ (basisRegular mode).continuous
  let basisCompact :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
      a b testCount
  let basisZeroOutside :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_zeroOutside
      a b testCount
  let massForm :=
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount
  let massDerivative := fixedP506L0CauchySafeMatterWeakMassFormDerivative
    basis basisRegular basisCompact
  let stiffnessForm := fixedP506L0CauchySafeMatterWeakStiffnessForm
    basis basisRegular basisCompact
  let velocity := fun candidateTime ↦
    fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
        a b testCount candidateTime (error candidateTime) +
      forcing candidateTime
  let forcingScale : ℝ :=
    ‖matterFiberMassRieszCoordinateBilinear‖ * C
  have massHasDeriv : ∀ candidateTime ∈ Ico timeStart timeEnd,
      HasDerivWithinAt massForm (massDerivative candidateTime)
        (Ici candidateTime) candidateTime := by
    intro candidateTime _
    exact (fixedP506L0CauchySafeMatterWeakMassForm_hasDerivAt
      basis basisRegular basisCompact candidateTime).hasDerivWithinAt
  have errorHasDeriv : ∀ candidateTime ∈ Ico timeStart timeEnd,
      HasDerivWithinAt error (velocity candidateTime)
        (Ici candidateTime) candidateTime := by
    intro candidateTime candidateTimeMem
    exact
      (errorEvolution candidateTime
        (Ico_subset_Icc_self candidateTimeMem)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem candidateTimeMem)
  have massSymmetric : ∀ candidateTime ∈ Ico timeStart timeEnd,
      ∀ first second,
        massForm candidateTime first second =
          massForm candidateTime second first := by
    intro candidateTime _ first second
    exact fixedP506L0CauchySafeMatterWeakMassForm_symm
      basis basisContinuous basisCompact candidateTime first second
  have weakEquation : ∀ candidateTime ∈ Ico timeStart timeEnd,
      massForm candidateTime (velocity candidateTime)
          (error candidateTime) +
        stiffnessForm candidateTime (error candidateTime)
          (error candidateTime) =
        massForm candidateTime (forcing candidateTime)
          (error candidateTime) := by
    intro candidateTime _
    simpa only [massForm, stiffnessForm, velocity,
      basis, basisRegular, basisCompact] using
      canonicalForcedError_forcedWeakEquation
        a b testCount error forcing candidateTime (error candidateTime)
  have energyContinuous :
      ContinuousOn (galerkinWeakEnergy massForm error)
        (Icc timeStart timeEnd) := by
    intro candidateTime candidateTimeMem
    exact
      (galerkinWeakEnergy_hasDerivWithinAt_of_forcing
        massForm massDerivative stiffnessForm error
        (velocity candidateTime) (forcing candidateTime)
        (Icc timeStart timeEnd) candidateTime
        (fixedP506L0CauchySafeMatterWeakMassForm_hasDerivAt
          basis basisRegular basisCompact candidateTime).hasDerivWithinAt
        (errorEvolution candidateTime candidateTimeMem)
        (fun first second ↦
          fixedP506L0CauchySafeMatterWeakMassForm_symm
            basis basisContinuous basisCompact candidateTime first second)
        (by
          simpa only [massForm, stiffnessForm, velocity,
            basis, basisRegular, basisCompact] using
            canonicalForcedError_forcedWeakEquation
              a b testCount error forcing candidateTime
                (error candidateTime))).continuousWithinAt
  have derivativeRateBound : ∀ candidateTime ∈ Ico timeStart timeEnd,
      ‖galerkinWeakEnergyRate massDerivative stiffnessForm error candidateTime +
          2 * massForm candidateTime (forcing candidateTime)
            (error candidateTime)‖ ≤
        (K + κ⁻¹) *
            ‖galerkinWeakEnergy massForm error candidateTime‖ +
          (forcingScale * δ) ^ 2 := by
    intro candidateTime candidateTimeMem
    simpa only [canonicalForcedWeakEnergyRate,
      canonicalForcedPairing, canonicalForcedWeakEnergy,
      massDerivative, stiffnessForm, massForm, forcingScale,
      basis, basisRegular, basisCompact] using
      canonicalForcedEnergyRate_norm_le
        timeStart timeEnd a b C CNonnegative κ κPositive K
        operatorBound pointwiseCoercivity rateBound testCount error forcing
        δ forcingBound candidateTime candidateTimeMem
  have energyBound := galerkinWeakEnergy_norm_le_of_modeUniformRate_forced
    massForm massDerivative stiffnessForm error velocity forcing
    timeStart timeEnd (K + κ⁻¹)
      ((forcingScale * δ) ^ 2)
    massHasDeriv errorHasDeriv massSymmetric weakEquation energyContinuous
      derivativeRateBound time timeMem
  have finalCoercivity :
      κ *
          ‖fixedP506L0CauchySafeMatterCanonicalSynthesis
            a b testCount (error time)‖ *
          ‖fixedP506L0CauchySafeMatterCanonicalSynthesis
            a b testCount (error time)‖ ≤
        galerkinWeakEnergy massForm error time := by
    simpa only [massForm, basis, basisContinuous, basisCompact,
      galerkinWeakEnergy,
      fixedP506L0CauchySafeMatterCanonicalWeakMassForm,
      fixedP506L0CauchySafeMatterCanonicalSynthesis_eq_trialL2] using
      fixedP506L0CauchySafeMatterWeakMassForm_coercive_of_pointwise
        basis basisContinuous basisCompact a b basisZeroOutside
        C time (operatorBound time timeMem)
        κ (pointwiseCoercivity time timeMem) (error time)
  have energyNonnegative :
      0 ≤ galerkinWeakEnergy massForm error time := by
    simpa only [massForm, basis, basisContinuous, basisCompact,
      galerkinWeakEnergy,
      fixedP506L0CauchySafeMatterCanonicalWeakMassForm] using
      fixedP506L0CauchySafeMatterWeakMassForm_nonnegative
        basis basisContinuous basisCompact time (error time)
  calc
    κ *
        ‖fixedP506L0CauchySafeMatterCanonicalSynthesis
          a b testCount (error time)‖ ^ 2 =
      κ *
          ‖fixedP506L0CauchySafeMatterCanonicalSynthesis
            a b testCount (error time)‖ *
          ‖fixedP506L0CauchySafeMatterCanonicalSynthesis
            a b testCount (error time)‖ := by ring
    _ ≤ galerkinWeakEnergy massForm error time := finalCoercivity
    _ = ‖galerkinWeakEnergy massForm error time‖ := by
      exact (Real.norm_of_nonneg energyNonnegative).symm
    _ ≤ gronwallBound
        ‖galerkinWeakEnergy massForm error timeStart‖
        (K + κ⁻¹)
        ((‖matterFiberMassRieszCoordinateBilinear‖ * C * δ) ^ 2)
        (time - timeStart) := by
      simpa only [forcingScale] using energyBound

/-- One source-owned set of mass and energy constants converts the exact
cross-level projection forcing into an all-time physical `L²` error bound. -/
theorem exists_fixedP506L0CauchySafeMatterCanonicalCrossLevelPhysicalError_bound_of_projectionTail
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    ∃ C κ K : ℝ, 0 ≤ C ∧ 0 < κ ∧ 0 ≤ K ∧
      ∀ {firstCount secondCount : ℕ}
        (countMonotone : firstCount ≤ secondCount)
        (δ : ℝ),
        (∀ time ∈ Icc timeStart timeEnd,
          canonicalCrossLevelProjectionTailNorm
            timeStart timeEnd timeOrder a b countMonotone time ≤ δ) →
        ∀ time ∈ Icc timeStart timeEnd,
          κ *
              canonicalCrossLevelPhysicalErrorNorm
                timeStart timeEnd timeOrder a b countMonotone time ^ 2 ≤
            gronwallBound
              ‖canonicalCrossLevelWeakEnergy
                timeStart timeEnd timeOrder a b countMonotone timeStart‖
              (K + κ⁻¹)
              ((‖matterFiberMassRieszCoordinateBilinear‖ * C * δ) ^ 2)
              (time - timeStart) := by
  obtain ⟨C, κ, K, CNonnegative, κPositive, KNonnegative, estimate⟩ :=
    exists_fixedP506L0CauchySafeMatterCanonicalForcedPhysicalError_bound
      timeStart timeEnd timeOrder a b boxOrder
  unfold CanonicalForcedPhysicalErrorEstimate at estimate
  refine ⟨C, κ, K, CNonnegative, κPositive, KNonnegative, ?_⟩
  intro firstCount secondCount countMonotone δ tailBound time timeMem
  let error := canonicalCrossLevelError
    timeStart timeEnd timeOrder a b countMonotone
  let forcing := canonicalCrossLevelForcing
    timeStart timeEnd timeOrder a b countMonotone
  have forcingPhysicalBound : ∀ candidateTime ∈ Icc timeStart timeEnd,
      ‖fixedP506L0CauchySafeMatterCanonicalSynthesis
        a b secondCount (forcing candidateTime)‖ ≤ δ := by
    intro candidateTime candidateTimeMem
    simpa only [canonicalCrossLevelProjectionTailNorm,
      canonicalCrossLevelProjectionTail, forcing] using
      tailBound candidateTime candidateTimeMem
  have bound := estimate secondCount error forcing
    (by
      intro candidateTime candidateTimeMem
      exact canonicalCrossLevelError_evolution
        timeStart timeEnd timeOrder a b countMonotone
          candidateTime candidateTimeMem)
    δ forcingPhysicalBound time timeMem
  simpa only [canonicalCrossLevelPhysicalErrorNorm,
    canonicalCrossLevelPhysicalError, canonicalCrossLevelWeakEnergy,
    error, forcing] using bound
end

end SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalForcedCrossLevelEnergy
