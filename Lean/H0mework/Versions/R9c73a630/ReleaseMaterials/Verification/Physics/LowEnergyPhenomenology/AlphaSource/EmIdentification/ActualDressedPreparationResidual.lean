import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativePreparedWard
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedJointGraph

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedPreparationEnergy
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussDensityCore GaussComposite.SourceGraph
open PreparationVacuumSourcePreparedState PreparationVacuumSourcePreparedResponse
open PreparationVacuumNativeClosure PreparationVacuumLocalizedYukawa PreparationVacuumPreparedCurrent
open CanonicalPreparationCore.Completed CanonicalPreparationCreation CanonicalScalarPreparation PreparationChartGuard
open ActualDressedFullCoulomb ActualDressedSourcePreparation ActualDressedJointGraph ActualDressedNoether
open GaussComposite.PhysicalEMDressedCharacter
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumSourceFieldFamily PreparationVacuumNoetherChart PreparationVacuumPhysicalFeedback
open scoped Topology InnerProductSpace BigOperators Matrix LinearPMap
local instance : NormedAddCommGroup ScalarZero := inferInstance
local instance : InnerProductSpace ℂ ScalarZero := inferInstance
local instance : CompleteSpace ScalarZero := inferInstance
attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourcePreparation sourceProfile
  sourceOperator sourceEnergy sourcePrepared sourceLeg

def preparationPoint (event : DressedEvent) : sourceOperator.domain :=
  (sourcePreparation event.epsilon event.precision).point

def preparationResidual (event : DressedEvent) : sourceLocalSpace :=
  sourceOperator (preparationPoint event)-(sourceEnergy:ℂ) • (preparationPoint event).val

/-- This is the original approximation obligation, on its own actual operator-domain point. -/
theorem preparation_residual_price (event : DressedEvent) : ‖preparationResidual event‖<event.epsilon :=
  (sourcePreparation event.epsilon event.precision).near

/-- The unchanged physical background is the original isometric source transport. -/
theorem preparation_background (event : DressedEvent) :
    sourcePrepared (preparationPoint event).val=prepared (sourceProfile event.epsilon event.precision) := by
  rw [source_profile_original_domain]
  simp only [sourcePrepared,preparationPoint,ContinuousLinearMap.comp_apply]

def preparationCreationMap (event : DressedEvent) : sourceLocalSpace→L[ℂ]H :=
  ((‖sourceDressedExcitation event.epsilon event.precision‖:ℂ)⁻¹*emDressedCharacter true) • sourceLeg true 1 0

theorem preparation_creation_actual (event : DressedEvent) :
    preparationCreationMap event (preparationPoint event).val=sourceDressedUnit event.epsilon event.precision := by
  rw [source_dressed_unit_original,sourceDressedAddition,source_profile_original_domain event]
  simp only [preparationCreationMap,smul_apply,sourceLeg,ContinuousLinearMap.comp_apply,preparationPoint]

private theorem creation_normalizer_bound (a b : ℝ) (na : 0≤a) (nb : 0≤b)
    (lower : 1≤4*b^2) (unit : a*b=1) : a≤2 := by
  have half : (1/2:ℝ)≤b := by nlinarith
  nlinarith

/-- The original creation lower bound generates the normalization price; no spectral gap is used. -/
theorem preparation_creation_normalizer (event : DressedEvent) :
    ‖(‖sourceDressedExcitation event.epsilon event.precision‖:ℂ)⁻¹*emDressedCharacter true‖≤2 := by
  have lower:=localized_creation_lower (preparationPoint event).val
  have unit : ‖sourcePrepared (preparationPoint event).val‖=1 := by
    simpa only [sourcePrepared,preparationPoint,ContinuousLinearMap.comp_apply] using
      (sourcePreparation event.epsilon event.precision).unit
  rw [unit] at lower
  have actual:=congrArg norm (preparation_creation_actual event)
  simp only [preparationCreationMap,smul_apply,norm_smul,source_dressed_unit_norm] at actual
  exact creation_normalizer_bound _ _ (norm_nonneg _) (norm_nonneg _) (by simpa only [one_pow] using lower) actual

theorem preparation_creation_map_price (event : DressedEvent) :
    ‖preparationCreationMap event‖≤2*‖sourceLeg true 1 0‖ := by
  apply (preparationCreationMap event).opNorm_le_bound (by positivity)
  intro x
  simp only [preparationCreationMap,smul_apply,norm_smul]
  calc
    _≤2*‖sourceLeg true 1 0 x‖:=mul_le_mul_of_nonneg_right (preparation_creation_normalizer event) (norm_nonneg _)
    _≤2*(‖sourceLeg true 1 0‖*‖x‖):=mul_le_mul_of_nonneg_left ((sourceLeg true 1 0).le_opNorm x) (by norm_num)
    _=_:=by ring

/-- Both actual state transports retain the same original residual. -/
theorem preparation_background_residual (event : DressedEvent) :
    ‖sourcePrepared (sourceOperator (preparationPoint event))-
      (sourceEnergy:ℂ) • prepared (sourceProfile event.epsilon event.precision)‖<event.epsilon := by
  rw [←preparation_background,←map_smul,←map_sub,sourcePrepared_norm]
  exact preparation_residual_price event

theorem preparation_creation_residual (event : DressedEvent) :
    ‖preparationCreationMap event (sourceOperator (preparationPoint event))-
      (sourceEnergy:ℂ) • sourceDressedUnit event.epsilon event.precision‖≤
        (2*‖sourceLeg true 1 0‖)*event.epsilon := by
  rw [←preparation_creation_actual,←map_smul,←map_sub]
  change ‖preparationCreationMap event (preparationResidual event)‖≤_
  exact ((preparationCreationMap event).le_opNorm _).trans
    (mul_le_mul (preparation_creation_map_price event) (preparation_residual_price event).le
      (norm_nonneg _) (by positivity))

end LowEnergy.GaussComposite.ActualDressedPreparationEnergy
