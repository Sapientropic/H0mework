import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePreparedThomsonMatchingBridge
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePreparedThomsonOrdinaryInteraction

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LowEnergy.PreparationPhysicalPreparedThomsonFullLightReturn

open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open CanonicalGradedSpatialSource
open GaussComposite GaussComposite.SourceGraph
open GaussUnitaryHistory (Index)
open PreparationPhysicalSourcePreparedThomsonInputReturn
open PreparationPhysicalPreparedThomsonMatchingBridge
open PreparationPhysicalThomsonMatchingReturn
open PreparationVacuumPhysicalPoleSheet
open scoped BigOperators Matrix Topology InnerProductSpace

variable {branch : Fin 2} {epsilon s : ℝ} {n p k : PhysicalMomentum}
  {F : Index} {cut : ℕ} {z w : ℂ}
  {eps : ℝ} {prec : 0<eps} {left right : Bool} {a b l r : Fin 2}
  {nonzero : epsilon≠0} {hz : z.im≠0} {hw : w.im≠0}

/-! This is the exact return shape still required from the matching owner.

The existing `SourcePreparedThomsonOwnerContract` already keeps the ordinary
full read, light read, contact read, electron unit, and full-light/contact
equation.  The present carrier adds the zero-transfer value and a source-side
remainder radius without changing that owner contract or manufacturing either
missing response. -/
structure SourcePreparedThomsonFullLightReturn
    (sourceCEM : ℂ)
    (input : SourcePreparedThomsonInput branch epsilon s n p k F cut z w eps prec
      left right a b l r nonzero hz hw) where
  owner : SourcePreparedThomsonOwnerContract sourceCEM input
  zeroTransfer : ℂ
  zeroTransfer_from_owner :
    zeroTransfer = sourcePreparedThomsonOwnerReadout owner
  remainderRadius : ℝ
  remainderRadius_nonneg : 0 ≤ remainderRadius
  zeroTransfer_remainder :
    ‖zeroTransfer - sourcePreparedThomsonOwnerReadout owner‖ ≤ remainderRadius

def sourcePreparedThomsonNormalizedCEM (branch : Fin 2) (sourceCEM : ℂ) : ℂ :=
  ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)⁻¹ * sourceCEM

def SourcePreparedThomsonFullLightReturn.toMatchingContract
    {sourceCEM : ℂ}
    {input : SourcePreparedThomsonInput branch epsilon s n p k F cut z w eps prec
      left right a b l r nonzero hz hw}
    (ret : SourcePreparedThomsonFullLightReturn sourceCEM input) :
    SourceThomsonMatchingContract sourceCEM :=
  ret.owner.toSourceThomsonContract

theorem sourcePreparedThomsonFullLightReturn_zeroTransfer
    {sourceCEM : ℂ}
    {input : SourcePreparedThomsonInput branch epsilon s n p k F cut z w eps prec
      left right a b l r nonzero hz hw}
    (ret : SourcePreparedThomsonFullLightReturn sourceCEM input) :
    ret.zeroTransfer =
      sourcePreparedThomsonNormalizedCEM branch sourceCEM := by
  unfold sourcePreparedThomsonNormalizedCEM
  rw [ret.zeroTransfer_from_owner]
  exact sourcePreparedThomsonOwner_readout ret.owner

theorem sourcePreparedThomsonFullLightReturn_source_normalized_read
    {sourceCEM : ℂ}
    {input : SourcePreparedThomsonInput branch epsilon s n p k F cut z w eps prec
      left right a b l r nonzero hz hw}
    (ret : SourcePreparedThomsonFullLightReturn sourceCEM input) :
    ret.zeroTransfer = sourcePreparedThomsonNormalizedCEM branch sourceCEM :=
  sourcePreparedThomsonFullLightReturn_zeroTransfer ret

/-! The owner-provided radius is consumed as an actual controlled interval.
It is deliberately a bound around the source α read, not a measured target. -/
theorem sourcePreparedThomsonFullLightReturn_error_bound
    {sourceCEM : ℂ}
    {input : SourcePreparedThomsonInput branch epsilon s n p k F cut z w eps prec
      left right a b l r nonzero hz hw}
    (ret : SourcePreparedThomsonFullLightReturn sourceCEM input) :
    ‖ret.zeroTransfer -
      sourcePreparedThomsonNormalizedCEM branch sourceCEM‖ ≤
      ret.remainderRadius := by
  unfold sourcePreparedThomsonNormalizedCEM
  rw [←sourcePreparedThomsonOwner_readout ret.owner]
  exact ret.zeroTransfer_remainder

theorem sourcePreparedThomsonFullLightReturn_readout_as_matching
    {sourceCEM : ℂ}
    {input : SourcePreparedThomsonInput branch epsilon s n p k F cut z w eps prec
      left right a b l r nonzero hz hw}
    (ret : SourcePreparedThomsonFullLightReturn sourceCEM input) :
    sourceThomsonContractReadout ret.toMatchingContract branch = ret.zeroTransfer := by
  unfold SourcePreparedThomsonFullLightReturn.toMatchingContract
  rw [sourcePreparedThomsonOwner_readout_as_matching ret.owner]
  exact ret.zeroTransfer_from_owner.symm

end LowEnergy.PreparationPhysicalPreparedThomsonFullLightReturn
