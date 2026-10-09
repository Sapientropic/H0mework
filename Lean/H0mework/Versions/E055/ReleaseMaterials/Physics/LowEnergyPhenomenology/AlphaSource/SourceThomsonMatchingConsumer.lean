import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceThomsonStaticResponse
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceDressedPhotonCoupling
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceJointPreparedCoupling
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualChargeColumns

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalThomsonMatchingReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open CanonicalGradedSpatialSource
open GaussComposite GaussComposite.SourceGraph
open GaussUnitaryHistory (Index)
open Filter Set
open PreparationPhysicalDressedPhotonCouplingReturn
open PreparationPhysicalNativePhotonFluxReturn
open PreparationPhysicalJointEMCouplingUnitReturn
open PreparationPhysicalActualPhaseChargeReturn
open PreparationVacuumFieldCovector PreparationVacuumSourcePreparedResponse
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open scoped BigOperators Matrix Topology InnerProductSpace

/-- The original source identifies edge zero as the unit charged external column. -/
theorem sourceElectronChargeUnit_edge0 : sourceActualPhaseCharge (0 : Fin 2)=1 := by
  simp [sourceActualPhaseCharge]

/-- The full ordinary DressedPhoton read is retained as the matching input, with independent
source and detector preparations and the original hbar_source*c_source denominator. -/
theorem sourceThomsonOrdinaryInput
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      (∑i,preparedCovector epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i*
        (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
          preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i)/
        ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)=
      sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
        (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS)/
        ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)*
      sourcePhotonWholePair branch e.val (sourceSheet branch n unit e.val) n pD kD FD cutD zD wD
        (completedLeg lD aD sD (sourceProfile epsD precD))
        (completedLeg rD bD tD (sourceProfile epsD precD)) := by
  exact sourceDressedPhotonInteraction_generated epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
    epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS branch n unit

/-- A precise return contract for the missing full-light/Thomson matching input.  The
contract keeps the source-generated static C_EM, the ordinary full read, light response,
and contact separately; it does not identify an arbitrary static tensor with electromagnetism. -/
structure SourceThomsonMatchingContract (sourceCEM : ℂ) where
  ordinaryFull : ℂ
  lightResponse : ℂ
  contactResponse : ℂ
  electronUnit : sourceActualPhaseCharge (0 : Fin 2)=1
  full_light_contact : ordinaryFull-lightResponse=sourceCEM+contactResponse

def sourceThomsonContractReadout {sourceCEM : ℂ}
    (contract : SourceThomsonMatchingContract sourceCEM) (branch : Fin 2) : ℂ :=
  ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)⁻¹ *
    (contract.ordinaryFull-contract.lightResponse-contract.contactResponse)

/-- Once matching supplies its exact full-light/contact equation, the source static residue
is the normalized Thomson read.  The theorem is deliberately conditional on that return
contract; no CODATA value, old 137 anchor, or fitted scale enters. -/
theorem sourceThomsonMatching_return
    (branch : Fin 2)
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2)
    (contract : SourceThomsonMatchingContract
      (sourceThomsonStaticCEM epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
        epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS)) :
    sourceThomsonContractReadout contract branch=
      sourceThomsonAlphaSource branch epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
        epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS := by
  unfold sourceThomsonContractReadout sourceThomsonAlphaSource
  rw [contract.full_light_contact]
  ring

end LowEnergy.PreparationPhysicalThomsonMatchingReturn
