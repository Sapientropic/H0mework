import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceDressedPhotonCoupling

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalSourcePreparedPhotonReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open CanonicalGradedSpatialSource
open GaussComposite GaussComposite.SourceGraph
open GaussUnitaryHistory (Index)
open PreparationPhysicalDressedPhotonCouplingReturn
open PreparationPhysicalNativePhotonFluxReturn
open PreparationVacuumFullFieldRiesz
open PreparationVacuumFieldCovector
open PreparationVacuumSourcePreparedState PreparationVacuumSourcePreparedResponse
open CanonicalPreparationCore.Completed CanonicalPreparationCreation CanonicalScalarPreparation
open PreparationChartGuard PreparationScalarCoordinates
open CanonicalPhysicalYResolvent
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open Filter Set
open scoped BigOperators Matrix Topology InnerProductSpace

/-! The preparation is the actual source operator-domain state.  The names below
do not relabel it as an experimental electron or photon; they expose the same
complex source amplitude to the hbar-source times c-source readout. -/

def sourcePreparedPhotonAmplitude
    (branch : Fin 2) (epsilon s : ℝ) (n p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ)
    (eps : ℝ) (prec : 0<eps) (left right : Bool) (a b l r : Fin 2) : ℂ :=
  sourcePhotonWholePair branch epsilon s n p k F cut z w
    (completedLeg left a l (sourceProfile eps prec))
    (completedLeg right b r (sourceProfile eps prec))

def sourcePreparedPhotonAmplitudeNormalized
    (branch : Fin 2) (epsilon s : ℝ) (n p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ)
    (eps : ℝ) (prec : 0<eps) (left right : Bool) (a b l r : Fin 2) : ℂ :=
  ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)⁻¹ *
    sourcePreparedPhotonAmplitude branch epsilon s n p k F cut z w eps prec left right a b l r

theorem sourcePreparedPhotonProfile_generated (eps : ℝ) (prec : 0<eps) :
    sourceProfile eps prec =
      zeroLocalizedProfile actualNativeLocalizer
        (sourcePreparation eps prec).point.val := rfl

theorem sourcePreparedPhoton_unit (eps : ℝ) (prec : 0<eps) :
    ‖prepared (sourceProfile eps prec)‖=1 := by
  unfold sourceProfile
  rw [sourceCausalState_same_preparation]
  exact (sourcePreparation eps prec).unit

theorem sourcePreparedPhoton_charge (eps : ℝ) (prec : 0<eps) :
    inner ℂ (prepared (sourceProfile eps prec))
      (CanonicalGradedCharge.chargeReader GaussComposite.nativeY
        (prepared (sourceProfile eps prec)))=-1 := by
  unfold sourceProfile
  rw [sourceCausalState_same_preparation]
  exact (sourcePreparation eps prec).charge

theorem sourcePreparedPhotonAmplitude_normalized
    (branch : Fin 2) (epsilon s : ℝ) (n p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ)
    (eps : ℝ) (prec : 0<eps) (left right : Bool) (a b l r : Fin 2) :
    ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ) *
      sourcePreparedPhotonAmplitudeNormalized branch epsilon s n p k F cut z w eps prec left right a b l r =
      sourcePreparedPhotonAmplitude branch epsilon s n p k F cut z w eps prec left right a b l r := by
  unfold sourcePreparedPhotonAmplitudeNormalized
  have h : ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (mul_pos Stage10.ActionNormalization.phaseMomentum_positive
        (sourceSpeed_positive branch)).ne'
  field_simp [h]

theorem sourcePreparedPhotonAmplitude_price
    (branch : Fin 2) (epsilon s : ℝ) (n p k : PhysicalMomentum)
    (nonzero : epsilon≠0) (F : Index) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0)
    (eps : ℝ) (prec : 0<eps) (left right : Bool) (a b l r : Fin 2) :
    ‖sourcePreparedPhotonAmplitude branch epsilon s n p k F cut z w eps prec left right a b l r‖≤
      ∑i,‖sourceNativeFrequencyPolarization branch epsilon s n i‖*
        (‖completedLeg left a l (sourceProfile eps prec)‖*
          (normBound cut z*currentPrice (fieldBasis i) p F*normBound cut w)*
          ‖completedLeg right b r (sourceProfile eps prec)‖) := by
  exact sourcePhotonWholePair_price branch epsilon s n p k nonzero F cut z w hz hw
    (completedLeg left a l (sourceProfile eps prec))
    (completedLeg right b r (sourceProfile eps prec))

end LowEnergy.PreparationPhysicalSourcePreparedPhotonReturn
