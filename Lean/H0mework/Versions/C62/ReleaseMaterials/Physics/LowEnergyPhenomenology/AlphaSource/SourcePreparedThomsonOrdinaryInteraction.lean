import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceThomsonMatchingConsumer
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePreparedThomsonInput

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalPreparedThomsonOrdinaryInteraction
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open CanonicalGradedSpatialSource
open GaussComposite GaussComposite.SourceGraph
open GaussUnitaryHistory (Index)
open PreparationPhysicalThomsonMatchingReturn
open PreparationPhysicalSourcePreparedThomsonInputReturn
open PreparationPhysicalSourcePreparedPhotonReturn
open PreparationPhysicalNativePhotonFluxReturn
open PreparationVacuumPhysicalCharacteristic
open PreparationVacuumFieldCovector
open PreparationVacuumPhysicalPoleSheet
open scoped BigOperators Matrix Topology InnerProductSpace

/-! `SourcePreparedThomsonInput.normalizedAmplitude` is the prepared source
amplitude itself.  The matching-side ordinary full read has one additional
source photon-left-reader factor.  This file records that factor explicitly
before any light/contact or zero-transfer claim is made. -/

def sourcePreparedThomsonOrdinaryInteraction
    (branch : Fin 2) (n p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ)
    (eps : ℝ) (prec : 0<eps) (left right : Bool) (a b l r : Fin 2)
    (e : scaleDomain) (unit : spatialSquare n=1) : ℂ :=
  sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
    (preparedCovector eps prec p k F cut z w left right a l b r) /
      ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ) *
    sourcePreparedPhotonAmplitude branch e.val (sourceSheet branch n unit e.val) n p k F cut z w
      eps prec left right a b l r

theorem sourcePreparedThomsonOrdinaryInteraction_normalized
    (branch : Fin 2) (n p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ)
    (eps : ℝ) (prec : 0<eps) (left right : Bool) (a b l r : Fin 2)
    (e : scaleDomain) (unit : spatialSquare n=1) :
    sourcePreparedThomsonOrdinaryInteraction branch n p k F cut z w eps prec
      left right a b l r e unit =
      sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
        (preparedCovector eps prec p k F cut z w left right a l b r) *
        sourcePreparedPhotonAmplitudeNormalized branch e.val (sourceSheet branch n unit e.val) n
          p k F cut z w eps prec left right a b l r := by
  unfold sourcePreparedThomsonOrdinaryInteraction sourcePreparedPhotonAmplitudeNormalized
  rw [div_eq_mul_inv]
  ring

/-- At each scale the ordinary interaction consumes the concrete prepared
`ordinaryFull` field, while retaining the independent photon-left-reader factor. -/
theorem sourcePreparedThomsonOrdinaryInteraction_owner
    (branch : Fin 2) (n p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ)
    (eps : ℝ) (prec : 0<eps) (left right : Bool) (a b l r : Fin 2)
    (e : scaleDomain) (unit : spatialSquare n=1)
    (hz : z.im≠0) (hw : w.im≠0) :
    sourcePreparedThomsonOrdinaryInteraction branch n p k F cut z w eps prec
      left right a b l r e unit =
      sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
        (preparedCovector eps prec p k F cut z w left right a l b r) *
      sourcePreparedThomsonOrdinaryFull
        (sourcePreparedThomsonInput branch e.val (sourceSheet branch n unit e.val) n p k F cut z w
          eps prec left right a b l r (ne_of_gt e.property.1) hz hw) := by
  rw [sourcePreparedThomsonOrdinaryInteraction_normalized]
  rfl

/-- The ordinary DressedPhoton residue read is the same source-prepared
amplitude with its detector/source reader factor and the single hbar*c
normalization.  This consumes the existing matching theorem rather than
manufacturing an ordinary value from a contract premise. -/
theorem sourceThomsonOrdinaryInput_prepared
    (branch : Fin 2) (epsilon _s : ℝ) (n p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ)
    (eps : ℝ) (prec : 0<eps) (left right : Bool) (a b l r : Fin 2)
    (_nonzero : epsilon≠0) (_hz : z.im≠0) (_hw : w.im≠0)
    (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      (∑i,preparedCovector eps prec p k F cut z w left right a l b r i*
        (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
          preparedCovector eps prec p k F cut z w left right a l b r) i)/
        ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)=
      sourcePreparedThomsonOrdinaryInteraction branch n p k F cut z w eps prec
        left right a b l r e unit := by
  have generated := sourceThomsonOrdinaryInput
      eps prec p k F cut z w left right a l b r
      eps prec p k F cut z w left right a l b r branch n unit
  filter_upwards [generated] with e h
  unfold sourcePreparedThomsonOrdinaryInteraction sourcePreparedPhotonAmplitude
  exact h

end LowEnergy.PreparationPhysicalPreparedThomsonOrdinaryInteraction
