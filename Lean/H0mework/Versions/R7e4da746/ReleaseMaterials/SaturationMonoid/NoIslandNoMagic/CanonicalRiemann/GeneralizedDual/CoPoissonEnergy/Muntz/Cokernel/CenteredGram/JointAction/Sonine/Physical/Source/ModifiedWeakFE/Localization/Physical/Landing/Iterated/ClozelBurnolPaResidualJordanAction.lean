import H0mework.Versions.R7e4da746.Arithmetic.RiemannResolvent.PaResidualBoundary

/-! # Iterated right-resolvent Jordan action in `P_a⊥` -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex MeasureTheory Set
open SourceGeneratedComplexFeaturePerfectification
open ClozelGeneralizedDual
open ClozelGeneralizedDual.BurnolPhysicalState
open scoped ENNReal

noncomputable section

local instance burnolJordanPaAmbientComplete :
    CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

local instance (priority := 10000) burnolJordanPaResidualRealModule :
    Module ℝ BurnolPaResidual :=
  Module.restrictScalars ℝ ℂ BurnolPaResidual

local instance (priority := 10000) burnolJordanPaResidualRealNormedSpace :
    NormedSpace ℝ BurnolPaResidual :=
  NormedSpace.restrictScalars ℝ ℂ BurnolPaResidual

local instance burnolJordanPaResidualComplete : CompleteSpace BurnolPaResidual := by
  apply IsComplete.completeSpace_coe
  exact burnolPaOrthogonalClosedFace.isClosed.isComplete

private theorem burnolPaResidual_continuous_primitive
    (f : ℝ → BurnolPaResidual) (hf : Continuous f) :
    Continuous (fun shift : ℝ => ∫ base : ℝ in (0 : ℝ)..shift, f base) := by
  exact @intervalIntegral.continuous_primitive
    BurnolPaResidual inferInstance burnolJordanPaResidualRealNormedSpace
    volume f inferInstance (fun first second => hf.intervalIntegrable first second) 0

/-- Recursive truncated-exponential coordinate of the resolvent tower. -/
def burnolPaResidualJordanCoordinate
    (z : ℂ) (sourceValue : HilbertAmbient (quarterMellinL2Feature z)) :
    Nat → ℝ → BurnolPaResidual
  | 0, _ => 0
  | order + 1, shift =>
      burnolPaResidualRead z
          (quarterFeatureCompletionRightResolventIterate z
            (order + 1) sourceValue) +
        ∫ base : ℝ in (0 : ℝ)..shift,
          burnolPaResidualJordanCoordinate z sourceValue order base

@[simp] theorem burnolPaResidualJordanCoordinate_one
    (z : ℂ) (sourceValue : HilbertAmbient (quarterMellinL2Feature z))
    (shift : ℝ) :
    burnolPaResidualJordanCoordinate z sourceValue 1 shift =
      burnolPaResidualRead z
        (quarterFeatureCompletionRightResolventIterate z 1 sourceValue) := by
  simp [burnolPaResidualJordanCoordinate]

theorem burnolPaResidualJordanCoordinate_two
    (z : ℂ) (sourceValue : HilbertAmbient (quarterMellinL2Feature z))
    (shift : ℝ) :
    burnolPaResidualJordanCoordinate z sourceValue 2 shift =
      burnolPaResidualRead z
          (quarterFeatureCompletionRightResolventIterate z 2 sourceValue) +
        (shift : ℂ) • burnolPaResidualRead z
          (quarterFeatureCompletionRightResolventIterate z 1 sourceValue) := by
  simp only [burnolPaResidualJordanCoordinate,
    intervalIntegral.integral_zero, add_zero,
    intervalIntegral.integral_const, sub_zero]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  norm_num

theorem burnolPaResidualJordanCoordinate_continuous
    (z : ℂ) (sourceValue : HilbertAmbient (quarterMellinL2Feature z))
    (order : Nat) :
    Continuous (burnolPaResidualJordanCoordinate z sourceValue order) := by
  induction order with
  | zero =>
      change Continuous (fun _ : ℝ => (0 : BurnolPaResidual))
      exact continuous_const
  | succ order ih =>
      change Continuous (fun shift : ℝ =>
        burnolPaResidualRead z
            (quarterFeatureCompletionRightResolventIterate z
              (order + 1) sourceValue) +
          ∫ base : ℝ in (0 : ℝ)..shift,
            burnolPaResidualJordanCoordinate z sourceValue order base)
      exact continuous_const.add
        (burnolPaResidual_continuous_primitive _ ih)

/-- Exact finite-shift action of the full resolvent tower.  Order one is the
ordinary character law; each successor integrates the preceding layer. -/
theorem burnolPaResidualRead_resolventIterate_jordanAction
    (source : burnolCompactAnnulusSource)
    (segment : BurnolCompactAnnulusDilationSegment source)
    (z : ℂ) (rightQuarter : 1 / 4 < z.re)
    (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (order : Nat) :
    ∀ (shift : ℝ), 0 ≤ shift → shift ≤ Real.log 16 →
      burnolPaResidualRead z
          (quarterFeatureCompletionTranslation z shift
            (quarterFeatureCompletionRightResolventIterate z order
              (burnolSourceQuarterCompletionValue
                source z positive belowHalf))) =
        positiveMellinQuarterRightResolventCharacter z shift •
          burnolPaResidualJordanCoordinate z
            (burnolSourceQuarterCompletionValue source z positive belowHalf)
            order shift := by
  induction order with
  | zero =>
      intro shift shiftNonnegative shiftBounded
      simpa [quarterFeatureCompletionRightResolventIterate,
        burnolPaResidualJordanCoordinate] using
        burnolPaResidualRead_source_translation_eq_zero
          source segment z positive belowHalf shift
          shiftNonnegative shiftBounded
  | succ order ih =>
      intro shift shiftNonnegative shiftBounded
      let sourceValue := burnolSourceQuarterCompletionValue
        source z positive belowHalf
      let previous := quarterFeatureCompletionRightResolventIterate
        z order sourceValue
      let boundary := quarterCompletionRightResolventBoundary z previous shift
      have recurrence := burnolPaResidualRead_resolvent_recurrence
        z rightQuarter previous shift shiftNonnegative
      have boundaryIntegrable : IntegrableOn
          (quarterFeatureCompletionRightResolventIntegrand z previous)
          (Ioc (0 : ℝ) shift) :=
        ((quarterFeatureCompletionRightResolventIntegrand_continuous
          z previous).continuousOn.integrableOn_compact isCompact_Icc
          ).mono_set Ioc_subset_Icc_self
      have boundaryRead :
          burnolPaResidualRead z boundary =
            ∫ base : ℝ in (0 : ℝ)..shift,
              burnolPaResidualJordanCoordinate z sourceValue order base := by
        calc
          burnolPaResidualRead z boundary =
              ∫ base : ℝ in Ioc (0 : ℝ) shift,
                burnolPaResidualRead z
                  (quarterFeatureCompletionRightResolventIntegrand
                    z previous base) := by
            unfold boundary quarterCompletionRightResolventBoundary
            exact (burnolPaResidualRead_integral_comp_comm
              z boundaryIntegrable).symm
          _ = ∫ base : ℝ in Ioc (0 : ℝ) shift,
                burnolPaResidualJordanCoordinate
                  z sourceValue order base := by
            apply setIntegral_congr_fun measurableSet_Ioc
            intro base baseMem
            have baseNonnegative : 0 ≤ base := baseMem.1.le
            have baseBounded : base ≤ Real.log 16 :=
              baseMem.2.trans shiftBounded
            calc
              burnolPaResidualRead z
                  (quarterFeatureCompletionRightResolventIntegrand
                    z previous base) =
                  positiveMellinQuarterRightResolventWeight z base •
                    burnolPaResidualRead z
                      (quarterFeatureCompletionTranslation z base previous) := by
                simp [quarterFeatureCompletionRightResolventIntegrand]
              _ = positiveMellinQuarterRightResolventWeight z base •
                    (positiveMellinQuarterRightResolventCharacter z base •
                      burnolPaResidualJordanCoordinate
                        z sourceValue order base) := by
                rw [ih base baseNonnegative baseBounded]
              _ = burnolPaResidualJordanCoordinate
                    z sourceValue order base := by
                rw [smul_smul,
                  positiveMellinQuarterRightResolventWeight_mul_character,
                  one_smul]
          _ = ∫ base : ℝ in (0 : ℝ)..shift,
                burnolPaResidualJordanCoordinate
                  z sourceValue order base := by
            rw [intervalIntegral.integral_of_le shiftNonnegative]
      have recurrence' :
          burnolPaResidualRead z
              (quarterFeatureCompletionTranslation z shift
                (quarterFeatureCompletionRightResolvent z previous)) -
            positiveMellinQuarterRightResolventCharacter z shift •
              burnolPaResidualRead z
                (quarterFeatureCompletionRightResolvent z previous) =
            positiveMellinQuarterRightResolventCharacter z shift •
              burnolPaResidualRead z boundary := by
        simpa only [boundary] using recurrence
      calc
        burnolPaResidualRead z
            (quarterFeatureCompletionTranslation z shift
              (quarterFeatureCompletionRightResolventIterate z
                (order + 1) sourceValue)) =
            positiveMellinQuarterRightResolventCharacter z shift •
                burnolPaResidualRead z
                  (quarterFeatureCompletionRightResolventIterate z
                    (order + 1) sourceValue) +
              positiveMellinQuarterRightResolventCharacter z shift •
                burnolPaResidualRead z boundary := by
          change burnolPaResidualRead z
              (quarterFeatureCompletionTranslation z shift
                (quarterFeatureCompletionRightResolvent z previous)) =
            positiveMellinQuarterRightResolventCharacter z shift •
                burnolPaResidualRead z
                  (quarterFeatureCompletionRightResolvent z previous) +
              positiveMellinQuarterRightResolventCharacter z shift •
                burnolPaResidualRead z boundary
          let action := burnolPaResidualRead z
            (quarterFeatureCompletionTranslation z shift
              (quarterFeatureCompletionRightResolvent z previous))
          let diagonal := positiveMellinQuarterRightResolventCharacter z shift •
            burnolPaResidualRead z
              (quarterFeatureCompletionRightResolvent z previous)
          let lower := positiveMellinQuarterRightResolventCharacter z shift •
            burnolPaResidualRead z boundary
          change action = diagonal + lower
          calc
            action = (action - diagonal) + diagonal :=
              (sub_add_cancel action diagonal).symm
            _ = lower + diagonal := by rw [recurrence']
            _ = diagonal + lower := add_comm _ _
        _ = positiveMellinQuarterRightResolventCharacter z shift •
            (burnolPaResidualRead z
                (quarterFeatureCompletionRightResolventIterate z
                  (order + 1) sourceValue) +
              ∫ base : ℝ in (0 : ℝ)..shift,
                burnolPaResidualJordanCoordinate
                  z sourceValue order base) := by
          rw [boundaryRead, smul_add]
        _ = positiveMellinQuarterRightResolventCharacter z shift •
            burnolPaResidualJordanCoordinate z sourceValue
              (order + 1) shift := by
          rfl

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
