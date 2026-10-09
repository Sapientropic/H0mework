import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeOriginalDictionaryIdentity
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeDiracLiteral
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationOriginalPreparedGreen
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationFieldFormConsumer
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNoetherEulerReturn

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourcePropagationNativeActionHessian
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFieldConstraintResponse
open PreparationVacuumPhysicalFeedback PreparationVacuumMixedFieldReturn
open PreparationVacuumGaugeSourceInjection SourcePropagationNoetherTime
open scoped BigOperators Matrix
attribute [local irreducible] nativeHessian nativeBlockHessian originalJacobi PreparationVacuumOriginalGreenFeedback.sourceField
  originalRowLift sourceCompatibility originalReader36 noetherField noetherForcing

def nativeCompleteLiteralTerms := literalGravityTerms ++ literalGaugeTerms ++
  literalScalarTerms ++ literalDiracTerms

theorem nativeLiteralHessian_append (left right : List (NativeJetIndex × NativeJetIndex × ℝ)) :
    nativeLiteralHessian (left++right)=nativeLiteralHessian left+nativeLiteralHessian right := by
  induction left with
  | nil =>
    simp only [List.nil_append,nativeLiteralHessian,List.map_nil,List.sum_nil]
    apply ContinuousLinearMap.ext
    intro x
    apply ContinuousLinearMap.ext
    intro y
    simp only [add_apply,zero_apply,zero_add]
  | cons a rest ih =>
    simp only [List.cons_append,nativeLiteralHessian,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih]
    apply ContinuousLinearMap.ext
    intro x
    apply ContinuousLinearMap.ext
    intro y
    simp only [add_apply,add_assoc]

theorem nativeCompleteLiteralTerms_source : nativeCompleteLiteralTerms =
    nativeSourceRealTerms nativeWholeSourceRecords := by
  simp only [nativeCompleteLiteralTerms,nativeWholeSourceRecords,literalGravityTerms_source,
    literalGaugeTerms_source,literalScalarTerms_source,literalDiracTerms_source,
    nativeSourceRealTerms,List.map_append]

theorem nativeHessian_complete_literal : nativeHessian = nativeLiteralHessian nativeCompleteLiteralTerms := by
  have gravity : literalGravityHessian=nativeLiteralHessian literalGravityTerms := rfl
  have gauge : literalGaugeHessian=nativeLiteralHessian literalGaugeTerms := rfl
  have scalar : literalScalarHessian=nativeLiteralHessian literalScalarTerms := rfl
  have dirac : literalDiracHessian=nativeLiteralHessian literalDiracTerms := rfl
  apply ContinuousLinearMap.ext
  intro a
  apply ContinuousLinearMap.ext
  intro b
  rw [nativeHessian_blocks]
  simp only [Fin.sum_univ_four]
  rw [nativeGravityHessian_literal,nativeGaugeHessian_literal,nativeScalarHessian_literal,
    nativeDiracHessian_literal,gravity,gauge,scalar,dirac]
  simp only [nativeCompleteLiteralTerms,nativeLiteralHessian_append,add_apply]

theorem nativeHessian_complete_source : nativeHessian =
    nativeLiteralHessian (nativeSourceRealTerms nativeWholeSourceRecords) := by
  rw [nativeHessian_complete_literal,nativeCompleteLiteralTerms_source]

/-- The full repaired native action Hessian is the original Fourier Jacobi matrix. -/
theorem nativeActionFourierHessian_original (p : Fin 4 → ℂ) :
    nativeFourierHessian nativeHessian p = originalJacobi p := by
  rw [nativeHessian_complete_source]
  exact nativeWholeLiteralFourier_original p

theorem nativeJacobi_original (p : Fin 4 → ℂ) : nativeJacobi p = originalJacobi p :=
  nativeActionFourierHessian_original p

theorem nativeAction_sourceField (p : regularSource) (forcing : Fin 289 → ℂ) :
    nativeFourierHessian nativeHessian p.val *ᵥ PreparationVacuumOriginalGreenFeedback.sourceField p forcing =
      forcing-originalRowLift p.val *ᵥ sourceCompatibility p.val forcing := by
  rw [nativeActionFourierHessian_original]
  exact original_forced_field p forcing

theorem nativeAction_original_regular_point :
    nativeFourierHessian nativeHessian generatedRegularPoint.val = originalJacobi generatedRegularPoint.val :=
  nativeActionFourierHessian_original generatedRegularPoint.val


theorem nativeAction_sourceField36 (p : regularSource) (forcing : Fin 289 → ℂ) :
    originalReader36 p.val *ᵥ
      (nativeFourierHessian nativeHessian p.val *ᵥ PreparationVacuumOriginalGreenFeedback.sourceField p forcing) =
      originalReader36 p.val *ᵥ forcing -
        originalReader36 p.val *ᵥ (originalRowLift p.val *ᵥ sourceCompatibility p.val forcing) := by
  rw [nativeAction_sourceField,Matrix.mulVec_sub]

theorem nativeAction_noetherField (q : PhysicalResponsePoint) (signal : ℝ → SourceJet Field289)
    (lambda : physicalSpectralDomain q.k) (T : ℝ) :
    nativeFourierHessian nativeHessian (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
      noetherField q signal lambda T =
        noetherForcing q signal lambda.val T -
          originalRowLift (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
            sourceCompatibility (fullMomentum (physicalSpatial q.k) lambda.val)
              (noetherForcing q signal lambda.val T) := by
  rw [nativeActionFourierHessian_original]
  exact noetherField_equation q signal lambda T

theorem nativeAction_noetherField36 (q : PhysicalResponsePoint) (signal : ℝ → SourceJet Field289)
    (lambda : physicalSpectralDomain q.k) (T : ℝ) :
    originalReader36 (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
      (nativeFourierHessian nativeHessian (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
        noetherField q signal lambda T) =
          originalReader36 (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
            noetherForcing q signal lambda.val T -
              originalReader36 (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
                (originalRowLift (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
                  sourceCompatibility (fullMomentum (physicalSpatial q.k) lambda.val)
                    (noetherForcing q signal lambda.val T)) := by
  rw [nativeAction_noetherField,Matrix.mulVec_sub]

end LowEnergy.SourcePropagationNativeActionHessian
