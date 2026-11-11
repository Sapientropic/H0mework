import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.QuarterCurrentSource
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open UnitPowerJordanSource UnitPowerJordanAction QuarterSourceCommutator
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Rq" => burnolQuarterRestriction
local notation "Eq" => burnolQuarterZeroExtension
local notation "D" => burnolTruncatedFourier
local notation "Cq" => intervalConstant q
local notation "mu" => burnolQuarterMeanCoefficient
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

/-- The existing actual ambient gap evaluator, on the literal quarter extension. -/
def quarterMean : Hq →L[ℂ] ℂ := (burnolAmbientGapCoefficient q).comp Eq

theorem quarterMean_read (value : Hq) : quarterMean value=mu value := by
  change ((‖Cq‖:ℂ)^2)⁻¹*inner ℂ Cq (Rq (Eq value))=mu value
  rw [burnolQuarterRestriction_zeroExtension]
  unfold burnolQuarterMeanCoefficient
  rw [Complex.ofReal_pow]
  ring

/-- Each contact coefficient is an actual continuous linear read of the current quarter source. -/
def contactCoefficientMap (c : BurnolCompletedMellinCoordinate) : Fin 6 → Hq →L[ℂ] ℂ :=
  ![(-2:ℂ) • ((innerSL ℂ (SingularCounting.powerL2 (barC c))).comp D),
    (2:ℂ) • ((sourceTail c).comp (fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.comp (burnolQuarterZeroExtension.comp D))),
    -(quarterMean.comp (burnolTruncatedFourier.comp D)),-(quarterMean.comp D),quarterMean.comp (quarterStep c),
    quarterMean.comp (burnolTruncatedFourier.comp (quarterStep c))-(mu (D Cq):ℂ) • (quarterMean.comp (quarterStep c))]

theorem contactCoefficientMap_read (c : BurnolCompletedMellinCoordinate) (value : Hq) (i : Fin 6) :
    contactCoefficientMap c i value=contactCoefficients c value i := by
  fin_cases i <;> simp [contactCoefficientMap,contactCoefficients,quarterMean_read]

/-- The six fixed columns consume only those reads of the actual current quarter source. -/
def currentContactMap (c : BurnolCompletedMellinCoordinate) : Hq →L[ℂ] M :=
  ∑ i : Fin 6,(contactCoefficientMap c i).smulRight (contactColumns c i)

theorem currentContactMap_read (c : BurnolCompletedMellinCoordinate) (value : Hq) :
    currentContactMap c value=contactAction c value := by
  simp [currentContactMap,contactAction,contactCoefficientMap_read]

/-- The finite log history and the current first-B source produce the identical six actual coefficients. -/
theorem finite_contact_coefficients_current (c : BurnolCompletedMellinCoordinate) (j : Nat) (i : Fin 6) :
    finiteContactCoefficients c j i=
      contactCoefficients c (burnolAmbientMeanZeroFirstCorrection (sourceField c j):Hq) i := by
  rw [←contactCoefficientMap_read,source_B_first]
  change (∑ k∈Finset.range j,sourceCoefficient c j k*contactCoefficients c (logBFirst c k:Hq) i)=
    ((contactCoefficientMap c i).comp (Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule))
      (∑ k∈Finset.range j,sourceCoefficient c j k • logBFirst c k)
  simp only [map_sum,map_smul,ContinuousLinearMap.comp_apply,contactCoefficientMap_read,smul_eq_mul]
  rfl

/-- The actual current first-B carrier replaces the complete finite feedback history. -/
theorem finite_contact_current (c : BurnolCompletedMellinCoordinate) (j : Nat) :
    finiteContactAction c j=contactAction c (burnolAmbientMeanZeroFirstCorrection (sourceField c j):Hq) := by
  unfold finiteContactAction contactAction
  apply Finset.sum_congr rfl
  intro i _
  rw [finite_contact_coefficients_current]

open private mean_constant
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKForcingGapAction.Source

/-- The current quarter mean is read from the same full source, including its constant direction. -/
theorem source_quarter_mean (c : BurnolCompletedMellinCoordinate) (j : Nat) :
    mu (Rq (sourceField c j))=sourceConstant c j+
      ∑ k∈Finset.range j,sourceCoefficient c j k*mu (dividedLogColumn c k) := by
  have finite : quarterMean (finiteQuarterSource c j)=
      ∑ k∈Finset.range j,sourceCoefficient c j k*mu (dividedLogColumn c k) := by
    unfold finiteQuarterSource
    simp only [map_sum,map_smul,quarterMean_read,smul_eq_mul]
  have actual := congrArg quarterMean (source_quarter_finite c j)
  rw [map_add,map_smul,finite] at actual
  simpa only [quarterMean_read,mean_constant,smul_eq_mul,mul_one] using actual

/-- The historical mean contact is exactly the current source mean after its original constant split. -/
theorem finite_mean_current (c : BurnolCompletedMellinCoordinate) (j : Nat) :
    finiteMeanContact c j=(mu (Rq (sourceField c j))-sourceConstant c j)*
      (q:ℂ)^(1-star c.value)/(1-star c.value) := by
  rw [source_quarter_mean,add_sub_cancel_left]
  unfold finiteMeanContact meanContact
  rw [Finset.sum_mul,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Whole-tail and quarter mean are read from one current full source. -/
theorem source_amplitude_current (c : BurnolCompletedMellinCoordinate) (j : Nat) :
    sourceAmplitude c j-2*finiteMeanContact c j=
      -2*(sourceTail c (sourceField c j)+
        mu (Rq (sourceField c j))*(q:ℂ)^(1-star c.value)/(1-star c.value)) := by
  rw [finite_mean_current]
  unfold sourceAmplitude
  ring

/-- The original full-adjoint source generates its next B carrier solely from its current full source. -/
theorem actual_B_current_step (c : BurnolCompletedMellinCoordinate) (j : Nat) :
    burnolAmbientMeanZeroFirstCorrection (sourceField c (j+1))=
      centeredQuarterStep c (burnolAmbientMeanZeroFirstCorrection (sourceField c j))+
      (-2*(sourceTail c (sourceField c j)+
        mu (Rq (sourceField c j))*(q:ℂ)^(1-star c.value)/(1-star c.value))) • logBFirst c 0-
      burnolMeanZeroBlockInverse
        (contactAction c (burnolAmbientMeanZeroFirstCorrection (sourceField c j):Hq)) := by
  rw [actual_B_source_contact_step,finite_contact_current,source_amplitude_current]

/-- This update program reads one current full carrier; no history or next state is an input. -/
def currentBNext (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) : M :=
  centeredQuarterStep c (burnolAmbientMeanZeroFirstCorrection value)+
    (-2*(sourceTail c value+mu (Rq value)*(q:ℂ)^(1-star c.value)/(1-star c.value))) • logBFirst c 0-
    burnolMeanZeroBlockInverse (contactAction c (burnolAmbientMeanZeroFirstCorrection value:Hq))

/-- The actual sourceStep action, rather than a selected equal-valued receiver, generates this update. -/
theorem actual_sourceStep_B_current (c : BurnolCompletedMellinCoordinate) (j : Nat) :
    burnolAmbientMeanZeroFirstCorrection (sourceStep c (sourceField c j))=
      currentBNext c (sourceField c j) :=
  actual_B_current_step c j

end OriginalKFiniteOrderRelease.QuarterCurrentSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
