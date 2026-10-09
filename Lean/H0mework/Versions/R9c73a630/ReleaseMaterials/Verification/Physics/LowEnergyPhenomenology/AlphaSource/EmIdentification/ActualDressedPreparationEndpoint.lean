import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPreparationResidual

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
attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourcePreparation sourceProfile
  sourceOperator sourceEnergy sourcePrepared sourceLeg


private theorem mapped_residual_price (event : DressedEvent) (L : sourceLocalSpace→L[ℂ]H) (A : H→L[ℂ]H) :
    ‖A (L (preparationResidual event))‖≤‖A‖*‖L‖*event.epsilon := by
  calc
    _≤‖A‖*‖L (preparationResidual event)‖:=A.le_opNorm _
    _≤‖A‖*(‖L‖*event.epsilon):=mul_le_mul_of_nonneg_left
      ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (preparation_residual_price event).le (norm_nonneg _))) (norm_nonneg _)
    _=_:=by ring

/-- The true two-time/two-resolvent Noether insertion reads the transported original preparation operator. -/
def preparationNoetherBoundary (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader : Field289) (age : ℝ) (h : Field289) : ℂ :=
  -inner ℂ (sourceDressedUnit event.epsilon event.precision)
    (dressedNoetherKernel event transfer reader age h
      (preparationCreationMap event (sourceOperator (preparationPoint event))))+
  inner ℂ (prepared (sourceProfile event.epsilon event.precision))
    (dressedNoetherKernel event transfer reader age h
      (sourcePrepared (sourceOperator (preparationPoint event))))

/-- This is a genuine original Noether endpoint error, with its unchanged actual background and creation state. -/
theorem preparation_noether_boundary_return (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader : Field289) (age : ℝ) (h : Field289) :
    preparationNoetherBoundary event transfer reader age h-
      (sourceEnergy:ℂ)*dressedEulerObserver event (dressedNoetherKernel event transfer reader age h)=
    -inner ℂ (sourceDressedUnit event.epsilon event.precision)
      (dressedNoetherKernel event transfer reader age h
        (preparationCreationMap event (preparationResidual event)))+
    inner ℂ (prepared (sourceProfile event.epsilon event.precision))
      (dressedNoetherKernel event transfer reader age h (sourcePrepared (preparationResidual event))) := by
  rw [dressed_euler_observer_original]
  simp only [preparationNoetherBoundary,preparationResidual,map_sub,map_smul,
    preparation_creation_actual,preparation_background,inner_sub_right,inner_smul_right]
  ring

/-- The source near-spectrum residual gives an explicit same-event time/reader budget. -/
theorem preparation_noether_boundary_price (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader : Field289) (age : ℝ) (h : Field289) :
    ‖preparationNoetherBoundary event transfer reader age h-
      (sourceEnergy:ℂ)*dressedEulerObserver event (dressedNoetherKernel event transfer reader age h)‖≤
    ‖dressedNoetherKernel event transfer reader age h‖*(2*‖sourceLeg true 1 0‖+1)*event.epsilon := by
  rw [preparation_noether_boundary_return]
  have unit:=source_dressed_unit_norm event.epsilon event.precision
  have background : ‖prepared (sourceProfile event.epsilon event.precision)‖=1 := by
    rw [←preparation_background]
    simpa only [sourcePrepared,preparationPoint,ContinuousLinearMap.comp_apply] using
      (sourcePreparation event.epsilon event.precision).unit
  have creation:=(mapped_residual_price event (preparationCreationMap event) (dressedNoetherKernel event transfer reader age h)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (preparation_creation_map_price event)
      (norm_nonneg _)) event.precision.le)
  have vacuum : ‖dressedNoetherKernel event transfer reader age h (sourcePrepared (preparationResidual event))‖≤
      ‖dressedNoetherKernel event transfer reader age h‖*event.epsilon := by
    exact ((dressedNoetherKernel event transfer reader age h).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (by rw [sourcePrepared_norm];exact (preparation_residual_price event).le) (norm_nonneg _))
  calc
    _≤‖inner ℂ (sourceDressedUnit event.epsilon event.precision)
      (dressedNoetherKernel event transfer reader age h (preparationCreationMap event (preparationResidual event)))‖+
      ‖inner ℂ (prepared (sourceProfile event.epsilon event.precision))
        (dressedNoetherKernel event transfer reader age h (sourcePrepared (preparationResidual event)))‖ := by
        simpa only [norm_neg] using norm_add_le
          (-inner ℂ (sourceDressedUnit event.epsilon event.precision)
            (dressedNoetherKernel event transfer reader age h (preparationCreationMap event (preparationResidual event))))
          (inner ℂ (prepared (sourceProfile event.epsilon event.precision))
            (dressedNoetherKernel event transfer reader age h (sourcePrepared (preparationResidual event))))
    _≤_:=add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _=‖dressedNoetherKernel event transfer reader age h (preparationCreationMap event (preparationResidual event))‖+
      ‖dressedNoetherKernel event transfer reader age h (sourcePrepared (preparationResidual event))‖ := by
        rw [unit,background,one_mul,one_mul]
    _≤‖dressedNoetherKernel event transfer reader age h‖*(2*‖sourceLeg true 1 0‖)*event.epsilon+
      ‖dressedNoetherKernel event transfer reader age h‖*event.epsilon := add_le_add creation vacuum
    _=_:=by ring

end LowEnergy.GaussComposite.ActualDressedPreparationEnergy
