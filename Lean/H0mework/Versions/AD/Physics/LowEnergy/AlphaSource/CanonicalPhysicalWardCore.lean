import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPhysicalForce
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalGradedCharge

/-! The source charge Ward difference keeps the complete configuration torque
and its actual unlocalized spatial current on the original Number-one core. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalPhysicalWardCore
open SaturationMonoid.PhysicsCore
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceQuantumScalarChart GaussQuantumMultiplier
open CanonicalGradedSpatialSource CanonicalPhysicalSpatial
open CanonicalGradedCharge (chargeMatrix chargeAction chargeReader contractedCurrent)
open CanonicalGradedCurrent (sourceLabel sourceProjection)
open scoped Topology InnerProductSpace ContDiff Distributions
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _

theorem momentumAction_add (p k : PhysicalMomentum) : momentumAction (p+k)=momentumAction p+momentumAction k := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change quantizer (momentumMatrix z (p+k)) (f z)=
    quantizer (momentumMatrix z p) (f z)+quantizer (momentumMatrix z k) (f z)
  rw [momentumMatrix_add, map_add, add_apply]

theorem momentum_charge_commutes (p : PhysicalMomentum) (a : NativeLie) :
    Commute (momentumAction p) (chargeAction a) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have matrix : momentumMatrix z p*chargeMatrix a=chargeMatrix a*momentumMatrix z p :=
    (CanonicalGradedCharge.momentum_charge z p a).trans (CanonicalGradedCharge.charge_momentum z p a).symm
  exact congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (f z))
    (CanonicalPhysicalForce.quantized_commute _ _ matrix).eq

def currentAction (k : PhysicalMomentum) (a : NativeLie) : QuantumTest →ₗ[ℂ] QuantumTest :=
  ∑ i : Fin 3, (k i : ℂ) • CanonicalGradedLocalCurrent.sourceAction (.spatial i) a

theorem currentAction_apply (k : PhysicalMomentum) (a : NativeLie) (f : QuantumTest) (z : SourceCoordinateSlice) :
    currentAction k a f z=quantized (contractedCurrent z k a) (f z) := by
  change (∑ i : Fin 3, (k i : ℂ) • quantized (CanonicalGradedCurrent.gaugeMatrix z (.spatial i) a) (f z)) =
    quantizer (∑ i : Fin 3, (k i : ℂ) • CanonicalGradedCurrent.gaugeMatrix z (.spatial i) a) (f z)
  simp only [map_sum, map_smul, sum_apply, smul_apply]
  rfl

theorem actual_current (k : PhysicalMomentum) (a : NativeLie) (f : QuantumTest) :
    momentumAction k (chargeAction a (GaussCoreLabel.project sourceLabel f)) =
      currentAction k a (GaussCoreLabel.project sourceLabel f) := by
  apply DFunLike.ext
  intro z
  rw [currentAction_apply]
  exact congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (f z))
    (CanonicalGradedCharge.current_velocity_projection z k a)

def configurationTorque (a : NativeLie) : QuantumTest →ₗ[ℂ] QuantumTest :=
  diagonalAction.comp (chargeAction a)-(chargeAction a).comp diagonalAction

theorem physical_charge_ward (p k : PhysicalMomentum) (a : NativeLie) (f : QuantumTest) :
    physicalAction (p+k) (chargeAction a (GaussCoreLabel.project sourceLabel f))-
      chargeAction a (physicalAction p (GaussCoreLabel.project sourceLabel f)) =
    configurationTorque a (GaussCoreLabel.project sourceLabel f)+
      currentAction k a (GaussCoreLabel.project sourceLabel f) := by
  have commute := LinearMap.congr_fun (momentum_charge_commutes p a).eq (GaussCoreLabel.project sourceLabel f)
  change momentumAction p (chargeAction a (GaussCoreLabel.project sourceLabel f)) =
    chargeAction a (momentumAction p (GaussCoreLabel.project sourceLabel f)) at commute
  simp only [physicalAction, momentumAction_add, LinearMap.add_apply, map_add,
    configurationTorque, LinearMap.sub_apply, LinearMap.comp_apply]
  rw [commute, actual_current]
  abel

theorem chargeReader_source_core (a : NativeLie) (f : QuantumTest) :
    chargeReader a (sourceProjection (embed f))=embed (chargeAction a (GaussCoreLabel.project sourceLabel f)) := by
  rw [sourceProjection, ← GaussCoreLabel.embed_project, CanonicalGradedCharge.chargeReader_core]

theorem finite_charge_ward_eventually (p k : PhysicalMomentum) (a : NativeLie) (f : QuantumTest) :
    ∀ᶠ F in (GaussUnitaryHistory.sourceFilter : Filter GaussUnitaryHistory.Index),
      (compression (p+k) F*chargeReader a-chargeReader a*compression p F)
        (sourceProjection (embed f)) =
      embed (configurationTorque a (GaussCoreLabel.project sourceLabel f)+
        currentAction k a (GaussCoreLabel.project sourceLabel f)) := by
  let g := GaussCoreLabel.project sourceLabel f
  filter_upwards [eventually_exact (p+k) (coreEquiv (chargeAction a g)),
    eventually_exact p (coreEquiv g)] with F left right
  change compression (p+k) F (embed (chargeAction a g))=physical (p+k) (coreEquiv (chargeAction a g)) at left
  change compression p F (embed g)=physical p (coreEquiv g) at right
  have source (r : PhysicalMomentum) (u : QuantumTest) : physical r (coreEquiv u)=embed (physicalAction r u) := by
    change embed (physicalAction r (coreEquiv.symm (coreEquiv u)))=_
    rw [coreEquiv.symm_apply_apply]
  rw [source] at left right
  simp only [sub_apply, mul_apply_eq_comp]
  rw [chargeReader_source_core, left, sourceProjection, ← GaussCoreLabel.embed_project, right,
    CanonicalGradedCharge.chargeReader_core, ← map_sub, physical_charge_ward]

end LowEnergy.CanonicalPhysicalWardCore
