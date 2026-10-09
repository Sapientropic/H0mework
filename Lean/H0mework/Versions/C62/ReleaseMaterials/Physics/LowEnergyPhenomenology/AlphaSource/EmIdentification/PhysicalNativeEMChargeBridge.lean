import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalNativeCurrentAlignment
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMChargeReadout

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge

open PhysicalNativeCurrentAlignment
open PhysicalFullFieldRestReadout
open PhysicalEMGaugeRealization
open PhysicalEMChargeReadout
open PreparationPhysicalActualPhaseChargeReturn
open PreparationPhysicalChargedPacketQuantumReturn PreparationPhysicalChargedPacketVoltage
open PreparationVacuumPhysicalQuantumLockedCharge
open PreparationVacuumActualSpatialPacket
open PreparationVacuumElectromagneticIdentity
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace YangMills.FullPairing
open Stage9C.Material.SpinPair Stage10 Stage10.CanonicalMatter
open Stage9DEF.Compatibility
open Filter
open scoped InnerProductSpace

/-- The actual source's charged edge `0` is the electron charge unit used by the
    electromagnetic reader.  It is read from `sourceActualPhaseCharge`; no
    hypercharge or mother-trace coefficient is substituted for it. -/
def sourceNativeElectronChargeUnit : ℂ :=
  (sourceActualPhaseCharge (0 : Fin 2) : ℂ)

theorem sourceNativeElectronChargeUnit_generated :
    sourceNativeElectronChargeUnit = 1 := by
  simp [sourceNativeElectronChargeUnit, sourceActualPhaseCharge]

/-- Both readers below act on the actual charged restriction, whose rest index
is `(side,1)`. The canonical `(0,0)` Y-charge state is a different external leg. -/
def sourceNativeElectronState (side : Fin 2) : YangMills.FullPairing.Hilbert :=
  operator (actualRestStatePreparation (sourceChargedRestIndex side 0))
    (YangMills.FullPairing.prepared 0)

theorem sourceNativeElectronState_source (side : Fin 2) :
    sourceNativeElectronState side =
      naturalCoordinates (sourceChargedRestriction side 0) := by
  unfold sourceNativeElectronState YangMills.FullPairing.prepared
  rw [operator_coordinates]
  rfl

/-- Native temporal current on the same charged external state used by the EM
reader. Its normalization follows from the original actionScale*h identity. -/
theorem native_charged_current_unit (side : Fin 2) :
    inner ℂ (sourceNativeElectronState side)
      (nativeCurrentReader 0 (sourceNativeElectronState side)) = -1 := by
  unfold sourceNativeElectronState
  rw [native_current_noether, actualRestState_hypercharge_current]
  simp only [nativeCurrentWeight, if_true, one_mul, mul_neg,
    PreparationPhysicalActionUnits.sourceActionScale_momentum]

/-- The two current conventions are compared only on the actual charged leg. -/
theorem native_rest_current_identifies_electron_unit (side : Fin 2) :
    - inner ℂ (sourceNativeElectronState side)
        (nativeCurrentReader 0 (sourceNativeElectronState side)) =
      sourceNativeElectronChargeUnit := by
  rw [native_charged_current_unit, sourceNativeElectronChargeUnit_generated]
  norm_num

/-- The same unit is consumed by the actual electromagnetic gauge reader on
    the source charged external column. -/
theorem em_reader_electron_unit (side : Fin 2) :
    emChargeFiber (naturalCoordinates (sourceChargedRestriction side 0)) =
      sourceNativeElectronChargeUnit •
        naturalCoordinates (sourceChargedRestriction side 0) := by
  simpa only [sourceNativeElectronChargeUnit] using em_charge_maker side 0

/-- The EM operator and native temporal pairing now consume identical legs. -/
theorem em_reader_same_electron_state (side : Fin 2) :
    emChargeFiber (sourceNativeElectronState side) =
      sourceNativeElectronChargeUnit • sourceNativeElectronState side := by
  rw [sourceNativeElectronState_source]
  exact em_reader_electron_unit side

/-- The electron--electron bilinear charge product is generated from the two
    actual external charges. -/
def sourceNativeElectronChargeProduct : ℂ :=
  sourceNativeElectronChargeUnit * sourceNativeElectronChargeUnit

theorem sourceNativeElectronChargeProduct_generated :
    sourceNativeElectronChargeProduct = 1 := by
  simp [sourceNativeElectronChargeProduct, sourceNativeElectronChargeUnit_generated]

/-- The phase/action unit is retained in the actual filtered bilinear read.
    The commutator correction and the complete EM defect remain explicit. -/
theorem em_filtered_electron_pair (sideL sideR : Fin 2) :
    (Stage10.ActionNormalization.phaseMomentum : ℂ) *
        inner ℂ (sourceChargedFilteredPacket sideL 0)
          (emChargeSpatial (sourceChargedFilteredPacket sideR 0)) =
      (Stage10.ActionNormalization.phaseMomentum : ℂ) *
          sourceNativeElectronChargeUnit *
          inner ℂ (sourceChargedFilteredPacket sideL 0)
            (sourceChargedFilteredPacket sideR 0) +
        (Stage10.ActionNormalization.phaseMomentum : ℂ) *
          inner ℂ (sourceChargedFilteredPacket sideL 0)
            (sourceActualChargeCorrection sideR 0) -
        (Stage10.ActionNormalization.phaseMomentum : ℂ) *
          inner ℂ (sourceChargedFilteredPacket sideL 0)
            (emDefectSpatial (sourceChargedFilteredPacket sideR 0)) := by
  simpa only [sourceNativeElectronChargeUnit] using
    em_charge_filtered_pair sideL 0 sideR 0

/-- Focused negative control: the neutral source edge cannot be promoted to the
    electron unit by this bridge. -/
theorem neutral_edge_not_electron_unit :
    (sourceActualPhaseCharge (1 : Fin 2) : ℂ) ≠ sourceNativeElectronChargeUnit := by
  rw [sourceNativeElectronChargeUnit_generated]
  norm_num [sourceActualPhaseCharge]

/-- Focused negative control: the complete defect remains a nonzero full-carrier
    operator even though it vanishes on the source embedding. -/
theorem full_defect_retained : emFullDefect ≠ 0 :=
  em_defect_nonzero

end LowEnergy.GaussComposite.PhysicalNativeEMChargeBridge
