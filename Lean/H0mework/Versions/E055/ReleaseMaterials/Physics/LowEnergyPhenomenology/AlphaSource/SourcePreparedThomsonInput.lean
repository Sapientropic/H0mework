import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePreparedPhotonAmplitude

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalSourcePreparedThomsonInputReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open CanonicalGradedSpatialSource
open GaussComposite GaussComposite.SourceGraph
open GaussUnitaryHistory (Index)
open PreparationPhysicalSourcePreparedPhotonReturn
open PreparationPhysicalNativePhotonFluxReturn
open PreparationVacuumPhysicalPoleSheet
open PreparationVacuumSourcePreparedState PreparationVacuumSourcePreparedResponse
open PreparationVacuumFieldCovector PreparationVacuumFullFieldRiesz CanonicalPhysicalYResolvent
open CanonicalPreparationCore.Completed CanonicalPreparationCreation CanonicalScalarPreparation
open PreparationChartGuard PreparationScalarCoordinates
open Filter Set
open scoped BigOperators Matrix Topology InnerProductSpace

/-! A typed ordinary input for the matching owner.  Every field is generated
from the same SourcePreparation; light/contact/zero-momentum matching remains
outside this structure. -/
structure SourcePreparedThomsonInput
    (branch : Fin 2) (epsilon s : ℝ) (n p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ)
    (eps : ℝ) (prec : 0<eps) (left right : Bool) (a b l r : Fin 2)
    (nonzero : epsilon≠0) (hz : z.im≠0) (hw : w.im≠0) where
  amplitude : ℂ
  normalizedAmplitude : ℂ
  normalization :
    ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ) * normalizedAmplitude = amplitude
  preparationUnit : ‖prepared (sourceProfile eps prec)‖=1
  preparationCharge :
    inner ℂ (prepared (sourceProfile eps prec))
      (CanonicalGradedCharge.chargeReader GaussComposite.nativeY
        (prepared (sourceProfile eps prec)))=-1
  price :
    ‖amplitude‖≤
      ∑i,‖sourceNativeFrequencyPolarization branch epsilon s n i‖*
        (‖completedLeg left a l (sourceProfile eps prec)‖*
          (normBound cut z*currentPrice (fieldBasis i) p F*normBound cut w)*
          ‖completedLeg right b r (sourceProfile eps prec)‖)

def sourcePreparedThomsonInput
    (branch : Fin 2) (epsilon s : ℝ) (n p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ)
    (eps : ℝ) (prec : 0<eps) (left right : Bool) (a b l r : Fin 2)
    (nonzero : epsilon≠0) (hz : z.im≠0) (hw : w.im≠0) :
    SourcePreparedThomsonInput branch epsilon s n p k F cut z w eps prec left right a b l r
      nonzero hz hw :=
  { amplitude := sourcePreparedPhotonAmplitude branch epsilon s n p k F cut z w eps prec left right a b l r
    normalizedAmplitude := sourcePreparedPhotonAmplitudeNormalized branch epsilon s n p k F cut z w eps prec left right a b l r
    normalization := sourcePreparedPhotonAmplitude_normalized branch epsilon s n p k F cut z w eps prec left right a b l r
    preparationUnit := sourcePreparedPhoton_unit eps prec
    preparationCharge := sourcePreparedPhoton_charge eps prec
    price := sourcePreparedPhotonAmplitude_price branch epsilon s n p k nonzero F cut z w hz hw eps prec left right a b l r }

def sourcePreparedThomsonOrdinaryFull
    {branch : Fin 2} {epsilon s : ℝ} {n p k : PhysicalMomentum}
    {F : Index} {cut : ℕ} {z w : ℂ}
    {eps : ℝ} {prec : 0<eps} {left right : Bool} {a b l r : Fin 2}
    {nonzero : epsilon≠0} {hz : z.im≠0} {hw : w.im≠0}
    (input : SourcePreparedThomsonInput branch epsilon s n p k F cut z w eps prec left right a b l r
      nonzero hz hw) : ℂ :=
  input.normalizedAmplitude

theorem sourcePreparedThomsonOrdinaryFull_normalized
    {branch : Fin 2} {epsilon s : ℝ} {n p k : PhysicalMomentum}
    {F : Index} {cut : ℕ} {z w : ℂ}
    {eps : ℝ} {prec : 0<eps} {left right : Bool} {a b l r : Fin 2}
    {nonzero : epsilon≠0} {hz : z.im≠0} {hw : w.im≠0}
    (input : SourcePreparedThomsonInput branch epsilon s n p k F cut z w eps prec left right a b l r
      nonzero hz hw) :
    ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ) *
      sourcePreparedThomsonOrdinaryFull input = input.amplitude := by
  exact input.normalization

end LowEnergy.PreparationPhysicalSourcePreparedThomsonInputReturn
