import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceGaugeCouplingObservation
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCommonObservableChannels

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalGaugeSpatialChannelExpansion
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open PreparationPhysicalGaugeMomentumCoupling
open PreparationPhysicalCommonObservableUnits
open PreparationPhysicalActualLegNormalization
open PreparationVacuumPhysicalPoleSheet
open PreparationVacuumPhysicalFeedback
open CanonicalGradedSpatialSource
open PreparationVacuumElectromagneticIdentity
open PreparationPhysicalActualGaussChargeCurrent
open PreparationPhysicalCommonCurrentStaticRead
open PreparationVacuumSoftPoleSelection
open PreparationPhysicalActualLegNormalization
open Stage10
open PreparationVacuumPhysicalPoleSheet
open MeasureTheory Filter
open scoped BigOperators Matrix Topology InnerProductSpace Matrix.Norms.L2Operator
local instance : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

/-- The actual source Coulomb field retains every prepared pair weight while exposing
its three signed spatial observable channels.  No angular or material average is taken. -/
theorem sourceGaugeActualCoulombField_channels (q : PhysicalResponsePoint)
    (sL eL sR eR : Fin 2) (n : PhysicalMomentum) :
    sourceGaugeActualCoulombField q sL eL sR eR n =
      ∑a : RestStateIndex, ∑b : RestStateIndex,
        sourceActualPreparedWeight 0 0 sL eL sR eR a b •
          (sourceObservableChannel q n a b 0 • sourceCommonOriginColumn 0 +
            sourceObservableChannel q n a b 1 • nativeBranchVector 0 +
            sourceObservableChannel q n a b 2 • nativeBranchVector 1) := by
  simp only [sourceGaugeActualCoulombField]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [sourceObservableTensor_channels]

/-- The static gauge read is channel expanded after the single source action/clock
normalization.  The complete prepared leg correction remains attached to the full
three-channel field. -/
theorem sourceGaugeStaticCouplingTensor_channels (branch : Fin 2)
    (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (n : PhysicalMomentum)
    (left : qd.z.im ≠ 0) (right : qd.w.im ≠ 0) :
    sourceGaugeStaticCouplingTensor branch qd q dSL dEL dSR dER sL eL sR eR T n =
      sourceActualLegNormalization qd dSL dEL dSR dER *
        ((∑a : RestStateIndex, ∑b : RestStateIndex,
          sourceActualPreparedWeight 0 0 sL eL sR eR a b *
            (sourceObservableChannel q n a b 0 *
                sourceActualPreparedDetector qd 0 0 dSL dEL dSR dER 0 T
                  (sourceCommonOriginColumn 0) +
             sourceObservableChannel q n a b 1 *
                sourceActualPreparedDetector qd 0 0 dSL dEL dSR dER 0 T
                  (nativeBranchVector 0) +
             sourceObservableChannel q n a b 2 *
                sourceActualPreparedDetector qd 0 0 dSL dEL dSR dER 0 T
                  (nativeBranchVector 1))) -
          sourceActualLegCorrection qd dSL dEL dSR dER
            (sourceActualPreparedKernel qd 0 0 0 T
              (sourceGaugeActualCoulombField q sL eL sR eR n))) /
        ((ActionNormalization.phaseMomentum * sourceSpeed branch : ℝ) : ℂ) := by
  rw [sourceGaugeStaticCoupling_return branch qd q dSL dEL dSR dER sL eL sR eR T n left right]
  congr 2
  simp only [sourceObservableTensor_channels, map_add, map_smul, smul_eq_mul]

end LowEnergy.PreparationPhysicalGaugeSpatialChannelExpansion
