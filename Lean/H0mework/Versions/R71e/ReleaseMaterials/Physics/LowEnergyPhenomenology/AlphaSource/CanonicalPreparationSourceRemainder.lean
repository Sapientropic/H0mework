import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationRawTableUnitConsumer
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationTailActualPreparation
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationYukawaPreparedDomain

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSourcePreparedState
open PreparationVacuumRawTableBounds PreparationVacuumTailOperator PreparationVacuumTailSupport
open PreparationVacuumNativeClosure PreparationVacuumCompositionNative PreparationVacuumLocalizedTail PreparationVacuumOriginalRadii
open PreparationVacuumTailFourier PreparationVacuumRemainder PreparationVacuumWeylDomain
open PreparationChartGuard PreparationScalarCoordinates CanonicalScalarPreparation
open CanonicalPreparationCore.Completed CanonicalPreparationCreation CanonicalGradedSpatialSource
open GaussCoreHilbert GaussDensityCore GaussComposite.SourceGraph
open SaturationMonoid.Quantum.Forms MeasureTheory
open scoped Topology ContDiff LinearPMap ComplexConjugate

-- B, all finite primitive jets and Unit102 are source-generated upstream.
-- Neither this operator nor its energy depends on preparation precision.
def sourceRemainder : sourceLocalSpace →L[ℂ] sourceLocalSpace :=
  completeNativeRemainder originalTableB originalTableB_nonnegative original_table_unit_102

theorem sourceRemainder_decomposition :
    sourceRemainder=nativeEnergyTail originalTableB originalTableB_nonnegative original_table_unit_102-sourceNativeComposition := rfl

theorem sourceRemainder_selfAdjoint : IsSelfAdjoint sourceRemainder :=
  completeNativeRemainder_isSelfAdjoint originalTableB originalTableB_nonnegative original_table_unit_102

theorem sourceRemainder_norm : ‖sourceRemainder‖ ≤ nativeEnergyTailBound originalTableB+sourceNativeCompositionBound :=
  completeNativeRemainder_norm_bound originalTableB originalTableB_nonnegative original_table_unit_102

theorem sourceRemainder_readback (g f : sourceLocalSpace) :
    inner ℂ g (sourceRemainder f)=
      (∫ xy : CanonicalPreparationSquareCutoff.PhysicalMomentum × CanonicalPreparationSquareCutoff.PhysicalMomentum,
        conj (localInput g xy.1)*tailWeylKernel originalTableB xy.1 xy.2*localInput f xy.2 ∂volume.prod volume)-
      (∫ xy : CanonicalPreparationSquareCutoff.PhysicalMomentum × CanonicalPreparationSquareCutoff.PhysicalMomentum,
        conj (localInput g xy.1)*actualFullCompositionKernelDefect xy.1 xy.2*localInput f xy.2 ∂volume.prod volume) :=
  completeNativeRemainder_readback originalTableB originalTableB_nonnegative original_table_unit_102 g f

theorem source_original_radius (k : ℕ) :
    sourceRadiusFor originalTableB (k+1)=(2 : ℝ)^
      max (radiusLog (originalCutoff originalTableB) k+1)
        (k+1+stageLargest (originalCutoff originalTableB) (k+1)) := rfl

def sourceOperator : sourceLocalSpace →ₗ.[ℂ] sourceLocalSpace :=
  BoundedRemainder.operator sourceClosedFactor sourceClosedFactor_closed sourceClosedFactor_dense sourceRemainder

def sourceEnergy : ℝ :=
  BoundedRemainder.energy sourceClosedFactor sourceClosedFactor_closed sourceRemainder

def sourceFactorPoint (x : sourceOperator.domain) : sourceClosedFactor.domain :=
  BoundedRemainder.factorPoint sourceClosedFactor sourceClosedFactor_closed sourceClosedFactor_dense sourceRemainder x

end LowEnergy.PreparationVacuumSourcePreparedState
