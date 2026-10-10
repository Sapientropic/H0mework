import SourcePreparedThomsonInput
import SourceThomsonMatchingConsumer

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalPreparedThomsonMatchingBridge
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open CanonicalGradedSpatialSource
open GaussComposite GaussComposite.SourceGraph
open GaussUnitaryHistory (Index)
open PreparationPhysicalSourcePreparedThomsonInputReturn
open PreparationPhysicalThomsonMatchingReturn
open PreparationPhysicalActualPhaseChargeReturn
open PreparationPhysicalNativePhotonFluxReturn PreparationVacuumFieldCovector
open PreparationVacuumPhysicalPoleSheet
open scoped BigOperators Matrix Topology InnerProductSpace

variable {branch : Fin 2} {epsilon s : ℝ} {n p k : PhysicalMomentum}
  {F : Index} {cut : ℕ} {z w : ℂ}
  {eps : ℝ} {prec : 0<eps} {left right : Bool} {a b l r : Fin 2}
  {nonzero : epsilon≠0} {hz : z.im≠0} {hw : w.im≠0}

structure SourcePreparedThomsonOwnerContract (sourceCEM : ℂ)
    (input : SourcePreparedThomsonInput branch epsilon s n p k F cut z w eps prec left right a b l r
      nonzero hz hw) where
  ordinaryFull : ℂ
  lightResponse : ℂ
  contactResponse : ℂ
  electronUnit : sourceActualPhaseCharge (0 : Fin 2)=1
  /-- The matching responses use raw action units. The prepared photon amplitude
  is already divided by h*c and needs its source current reader before matching. -/
  ordinaryFull_from_prepared : ordinaryFull=
    ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)*
      (sourcePhotonLeftReader branch epsilon s n
        (preparedCovector eps prec p k F cut z w left right a l b r)*
        sourcePreparedThomsonOrdinaryFull input)
  full_light_contact : ordinaryFull-lightResponse=sourceCEM+contactResponse

def sourcePreparedThomsonOwnerReadout {sourceCEM : ℂ}
    {input : SourcePreparedThomsonInput branch epsilon s n p k F cut z w eps prec left right a b l r
      nonzero hz hw}
    (contract : SourcePreparedThomsonOwnerContract sourceCEM input) : ℂ :=
  ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)⁻¹ *
    (contract.ordinaryFull-contract.lightResponse-contract.contactResponse)

theorem sourcePreparedThomsonOwner_prepared_full {sourceCEM : ℂ}
    {input : SourcePreparedThomsonInput branch epsilon s n p k F cut z w eps prec left right a b l r
      nonzero hz hw}
    (contract : SourcePreparedThomsonOwnerContract sourceCEM input) :
    contract.ordinaryFull=
      sourcePhotonLeftReader branch epsilon s n
        (preparedCovector eps prec p k F cut z w left right a l b r)*input.amplitude := by
  rw [contract.ordinaryFull_from_prepared, mul_left_comm,
    sourcePreparedThomsonOrdinaryFull_normalized]

theorem sourcePreparedThomsonOwner_readout {sourceCEM : ℂ}
    {input : SourcePreparedThomsonInput branch epsilon s n p k F cut z w eps prec left right a b l r
      nonzero hz hw}
    (contract : SourcePreparedThomsonOwnerContract sourceCEM input) :
    sourcePreparedThomsonOwnerReadout contract=
      ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)⁻¹*sourceCEM := by
  unfold sourcePreparedThomsonOwnerReadout
  rw [contract.full_light_contact]
  ring

def SourcePreparedThomsonOwnerContract.toSourceThomsonContract {sourceCEM : ℂ}
    {input : SourcePreparedThomsonInput branch epsilon s n p k F cut z w eps prec left right a b l r
      nonzero hz hw}
    (contract : SourcePreparedThomsonOwnerContract sourceCEM input) :
    SourceThomsonMatchingContract sourceCEM :=
  { ordinaryFull := contract.ordinaryFull
    lightResponse := contract.lightResponse
    contactResponse := contract.contactResponse
    electronUnit := contract.electronUnit
    full_light_contact := contract.full_light_contact }

theorem sourcePreparedThomsonOwner_readout_as_matching {sourceCEM : ℂ}
    {input : SourcePreparedThomsonInput branch epsilon s n p k F cut z w eps prec left right a b l r
      nonzero hz hw}
    (contract : SourcePreparedThomsonOwnerContract sourceCEM input) :
    sourceThomsonContractReadout contract.toSourceThomsonContract branch =
      sourcePreparedThomsonOwnerReadout contract := rfl

end LowEnergy.PreparationPhysicalPreparedThomsonMatchingBridge
