import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMGaugeRealization
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualChargeTransition

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalEMChargeReadout
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace YangMills.FullPairing Stage9C.Material.SpinPair
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open DiracExteriorMatterAction DiracCliffordRepresentation SU7MotherLieAlgebra SU7MotherGaugeTheory
open PreparationPhysicalNativeOriginPhaseWard PreparationPhysicalNativePhaseChargeInventory
open PreparationPhysicalActualPhaseChargeReturn PreparationPhysicalChargedPacketQuantumReturn
open PreparationPhysicalChargedPacketVoltage PreparationPhysicalNormalizedFullField
open PreparationVacuumPhysicalQuantumLockedCharge PreparationVacuumActualSpatialPacket
open Stage10.CanonicalMatter MeasureTheory FullQuantum.Triangular
open Stage9DEF.Compatibility Electromagnetic.CanonicalCoframe
open GaussComposite.PhysicalEMGaugeRealization
open scoped Matrix BigOperators InnerProductSpace
local instance : DecidableEq Quantum.Index:=Classical.decEq _

/-- The electromagnetic charge fiber is the density reader of the
    electromagnetic temporal current on the whole Hilbert space. -/
def emChargeFiber : FiberOperators :=
  Electromagnetic.CanonicalPacket.densityReader
    (Stage9DEF.Compatibility.currentAction 0 emDirection)

/-- The remaining `I·(½·(TY − i·id))` defect fiber, kept whole. -/
def emDefectFiber : FiberOperators := operator (Complex.I • emFullDefect)

/-- The spatial lift of the electromagnetic charge fiber. -/
def emChargeSpatial : FullMatterL2→L[ℂ]FullMatterL2 :=
  emChargeFiber.compLpL 2 volume

/-- The spatial lift of the complete defect fiber. -/
def emDefectSpatial : FullMatterL2→L[ℂ]FullMatterL2 :=
  emDefectFiber.compLpL 2 volume

private theorem em_defect_restricted (side edge : Fin 2) :
    emFullDefect (sourceChargedRestriction side edge) = 0 := by
  rw [sourceChargedRestriction_basis, map_smul, em_defect_embedded,
    smul_zero]

/-- The source charge fiber is exactly the electromagnetic fiber plus the
    complete defect fiber, on the entire Hilbert space. -/
theorem origin_charge_decomposition :
    sourceActualChargeFiber = emChargeFiber + emDefectFiber := by
  have decompose : sourcePhaseNoether =
      Stage9DEF.Compatibility.currentAction 0 emDirection+emCurrentDefect 0 := by
    rw [← em_current_full 0]
    exact origin_temporal_current.symm
  have decomp_fiber : phaseInverse.comp sourcePhaseNoether =
      Complex.I • emGaugeAction+Complex.I • emFullDefect := by
    rw [decompose]
    apply LinearMap.ext
    intro v
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add]
    have current :=
      LinearMap.congr_fun (em_phase_current) v
    have defect :=
      LinearMap.congr_fun (em_phase_defect) v
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at current defect
    rw [current, defect]
    rfl
  rw [sourceActualChargeFiber, emChargeFiber, emDefectFiber]
  unfold Electromagnetic.CanonicalPacket.densityReader
  rw [em_phase_current, decomp_fiber, operator_add]

private theorem em_spatial_decomposition :
    sourceActualChargeSpatial = emChargeSpatial + emDefectSpatial := by
  rw [sourceActualChargeSpatial, emChargeSpatial, emDefectSpatial,
    ← ContinuousLinearMap.add_compLpL, origin_charge_decomposition]

private theorem em_defect_fiber_restricted (side edge : Fin 2) :
    emDefectFiber (naturalCoordinates (sourceChargedRestriction side edge)) = 0 := by
  rw [emDefectFiber, operator_smul]
  change (Complex.I • operator emFullDefect) _ = 0
  rw [smul_apply, operator_coordinates,
    em_defect_restricted, map_zero, smul_zero]

/-- On the actual source restriction the electromagnetic fiber returns the
    literal source column charge, through the original phase action — not
    a chosen eigen premise. -/
theorem em_charge_maker (side edge : Fin 2) :
    emChargeFiber (naturalCoordinates (sourceChargedRestriction side edge)) =
      (sourceActualPhaseCharge edge:ℂ) •
        naturalCoordinates (sourceChargedRestriction side edge) := by
  have acted : emGaugeAction (sourceChargedRestriction side edge) =
      (-(sourceActualPhaseCharge edge:ℂ)*Complex.I) •
        sourceChargedRestriction side edge := by
    have sub : emGaugeAction = sourceNativeOriginGenerator-emFullDefect := by
      rw [original_generator_gauge]
      abel
    rw [sub, LinearMap.sub_apply, sourceActualRestriction_generator,
      em_defect_restricted, sub_zero]
  have coeff : Complex.I*(-(sourceActualPhaseCharge edge:ℂ)*Complex.I) =
      sourceActualPhaseCharge edge := by
    calc
      _ = -(sourceActualPhaseCharge edge:ℂ)*(Complex.I*Complex.I) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [emChargeFiber, Electromagnetic.CanonicalPacket.densityReader,
    em_phase_current, operator_coordinates]
  rw [LinearMap.smul_apply, acted, map_smul, map_smul, smul_smul, coeff]

private theorem em_defect_packet (side edge : Fin 2) :
    emDefectSpatial (sourceChargedSpatialPacket side edge) = 0 := by
  apply Lp.ext
  filter_upwards [emDefectFiber.coeFn_compLpL
      (sourceChargedSpatialPacket side edge),
    sourcePacketShape_original
      (naturalCoordinates (sourceChargedRestriction side edge))] with x reader shape
  rw [show emDefectSpatial (sourceChargedSpatialPacket side edge) =
      (emDefectFiber.compLpL 2 volume) (sourceChargedSpatialPacket side edge)
      from rfl, reader]
  rw [show sourceChargedSpatialPacket side edge =
      HistoryPrepared.preparation
        (naturalCoordinates (sourceChargedRestriction side edge)) from rfl]
  rw [shape, map_smul, em_defect_fiber_restricted, smul_zero]
  simp

/-- The bare original unit spatial maker carries its source charge through
    the electromagnetic fiber. -/
theorem em_charge_packet (side edge : Fin 2) :
    emChargeSpatial (sourceChargedSpatialPacket side edge) =
      (sourceActualPhaseCharge edge:ℂ) • sourceChargedSpatialPacket side edge := by
  have dec := congrArg (fun f => f (sourceChargedSpatialPacket side edge))
    em_spatial_decomposition
  rw [add_apply] at dec
  rw [em_defect_packet, add_zero, sourceActualCharge_packet] at dec
  exact dec.symm

/-- The filtered actual source packet returns its charge plus the complete
    filter-transition correction minus the whole defect — both corrections
    retained, nothing extended to the filtered state. -/
theorem em_charge_filtered (side edge : Fin 2) :
    emChargeSpatial (sourceChargedFilteredPacket side edge) =
      (sourceActualPhaseCharge edge:ℂ) • sourceChargedFilteredPacket side edge+
        sourceActualChargeCorrection side edge-
        emDefectSpatial (sourceChargedFilteredPacket side edge) := by
  have dec := congrArg (fun f => f (sourceChargedFilteredPacket side edge))
    em_spatial_decomposition
  rw [add_apply] at dec
  rw [sourceActualCharge_filtered] at dec
  exact eq_sub_iff_add_eq.mpr dec.symm

/-- The bilinear actual filtered current keeps the source-generated unit,
    the charge, the filter correction and the complete defect, on all four
    charged/neutral maker pairs. -/
theorem em_charge_filtered_pair (sideL edgeL sideR edgeR : Fin 2) :
    (Stage10.ActionNormalization.phaseMomentum:ℂ)*
        inner ℂ (sourceChargedFilteredPacket sideL edgeL)
          (emChargeSpatial (sourceChargedFilteredPacket sideR edgeR)) =
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*
          (sourceActualPhaseCharge edgeR:ℂ)*
          inner ℂ (sourceChargedFilteredPacket sideL edgeL)
            (sourceChargedFilteredPacket sideR edgeR)+
        (Stage10.ActionNormalization.phaseMomentum:ℂ)*
          inner ℂ (sourceChargedFilteredPacket sideL edgeL)
            (sourceActualChargeCorrection sideR edgeR)-
        (Stage10.ActionNormalization.phaseMomentum:ℂ)*
          inner ℂ (sourceChargedFilteredPacket sideL edgeL)
            (emDefectSpatial (sourceChargedFilteredPacket sideR edgeR)) := by
  rw [em_charge_filtered, inner_sub_right, inner_add_right, inner_smul_right]
  ring

end LowEnergy.GaussComposite.PhysicalEMChargeReadout
