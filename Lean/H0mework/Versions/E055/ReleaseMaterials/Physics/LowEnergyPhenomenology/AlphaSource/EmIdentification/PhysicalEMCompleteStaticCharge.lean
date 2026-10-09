import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMCompleteStaticScalar
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceJointPreparedCoupling

/-! The actual joint `Qa` insertion into the complete static interaction:
the original `sourcePhaseGaugeLie` charge action on both original completed
detector legs produces the literal increment times the whole interaction
plus the actual bounded input/scalar remainder contraction. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalEMCompleteStaticCharge
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumStaticPoleResponse PreparationVacuumOriginalGreenFeedback
open PreparationVacuumFullOriginResponse PreparationVacuumPhysicalPoleSheet
open PreparationVacuumPhysicalCharacteristic
open PreparationPhysicalStaticSpatialCouplingReturn PreparationPhysicalStaticCompositeProjectionReturn
open PreparationPhysicalDressedSpinChargeReturn PreparationPhysicalJointEMCouplingUnitReturn
open PreparationVacuumFieldCovector PreparationVacuumSourcePreparedResponse
open CanonicalGradedSpatialSource
open GaussComposite.PhysicalEMCompleteStaticScalar
open GaussComposite GaussComposite.SourceGraph
open GaussUnitaryHistory (Index)
open MeasureTheory Filter Set
open scoped BigOperators Topology Matrix InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _

/-- The complete static interaction with the actual joint `Qa` insertion on
both original detector legs and the original prepared source current. -/
def emCompleteStaticChargeInteraction (direction : PhysicalMomentum) (unit : spatialSquare direction=1)
    (kappa : staticDomain)
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2) : ℂ :=
  ∑i,sourceJointChargedCurrent epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i*
    sourceSpatialStaticNativeField direction unit kappa
      (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i

/-- The actual bounded input/scalar remainder part of the same interaction. -/
def emCompleteStaticInputInteraction (direction : PhysicalMomentum) (unit : spatialSquare direction=1)
    (kappa : staticDomain)
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2) : ℂ :=
  ∑i,sourceJointInputCurrent epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i*
    sourceSpatialStaticNativeField direction unit kappa
      (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i

/-- The full input/scalar remainder contraction with the source static
residue; no projection is assumed for this actual remainder. -/
def emCompleteStaticInputResidue
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2) : ℂ :=
  ∑i,sourceJointInputCurrent epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i*
    staticResidue (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i

/-- Contraction of the generated charged current splits into the literal
joint increment times the original contraction plus the actual input
remainder contraction. -/
private theorem charged_contraction
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2) (v : Fin 289→ℂ) :
    (∑i,sourceJointChargedCurrent epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i*v i)=
      (sourceJointIncrement lD+sourceJointIncrement rD)*
        (∑i,preparedCovector epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i*v i)+
      ∑i,sourceJointInputCurrent epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i*v i:=by
  rw [sourceJointChargedCurrent_generated epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,Finset.mul_sum,
    Finset.sum_add_distrib,mul_assoc]

/-- Pointwise split of the charged interaction: actual joint insertion equals
the endpoint increment sum times the whole interaction plus the actual
input/scalar remainder interaction. -/
theorem em_complete_static_charge_split (direction : PhysicalMomentum) (unit : spatialSquare direction=1)
    (kappa : staticDomain)
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2) :
    emCompleteStaticChargeInteraction direction unit kappa
      epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
      epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS=
      (sourceJointIncrement lD+sourceJointIncrement rD)*
        sourceStaticSpatialInteraction direction unit kappa
          epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
          epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS+
      emCompleteStaticInputInteraction direction unit kappa
        epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
        epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS:=by
  exact charged_contraction epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
    (sourceSpatialStaticNativeField direction unit kappa
      (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS))

/-- The `κ²` charged interaction tends to the joint increment times the
complete actual static scalar minus the actual input residue.  The limit
comes from the original source static residue and continuous contraction
with the inserted current, then `sourceJointChargedCurrent_generated`. -/
theorem em_complete_static_charge_limit (direction : PhysicalMomentum) (unit : spatialSquare direction=1)
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2) :
    Tendsto (fun kappa : staticDomain=>(kappa.val:ℂ)^2*
      emCompleteStaticChargeInteraction direction unit kappa
        epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
        epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS)
      staticApproach (𝓝 ((sourceJointIncrement lD+sourceJointIncrement rD)*
        emCompleteStaticScalar
          epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
          epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS-
        emCompleteStaticInputResidue
          epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
          epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS)):=by
  have produced:=sourceSpatialStaticNativeFieldResidue direction unit
    (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS)
  have reader : Continuous (fun v : Fin 289→ℂ=>
      ∑i,sourceJointChargedCurrent epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i*v i):=by
    fun_prop
  have actual:=reader.continuousAt.tendsto.comp produced
  have fold : emCompleteStaticInputResidue
      epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
      epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS=
    ∑i,sourceJointInputCurrent epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i*
      staticResidue (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i:=rfl
  rw [charged_contraction epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
      (staticResidue (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS)),
    em_complete_static_residue
      epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
      epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS,←fold] at actual
  have negated:=actual.neg
  have target : -((sourceJointIncrement lD+sourceJointIncrement rD)*
      (-emCompleteStaticScalar
        epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
        epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS)+
      emCompleteStaticInputResidue
        epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
        epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS)=
    (sourceJointIncrement lD+sourceJointIncrement rD)*
      emCompleteStaticScalar
        epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
        epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS-
      emCompleteStaticInputResidue
        epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
        epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS:=by ring
  rw [target] at negated
  apply negated.congr'
  apply Filter.Eventually.of_forall
  intro kappa
  simp only [emCompleteStaticChargeInteraction,Function.comp_apply,Pi.smul_apply,smul_eq_mul,
    Finset.mul_sum,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The same insertion read on the original `h_source*c_source` unit. -/
theorem em_complete_static_charge_reduced_limit (direction : PhysicalMomentum) (unit : spatialSquare direction=1)
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2) :
    Tendsto (fun kappa : staticDomain=>(kappa.val:ℂ)^2*
      emCompleteStaticChargeInteraction direction unit kappa
        epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
        epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS/
        ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed 0:ℝ):ℂ))
      staticApproach (𝓝 (((sourceJointIncrement lD+sourceJointIncrement rD)*
        emCompleteStaticScalar
          epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
          epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS-
        emCompleteStaticInputResidue
          epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
          epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS)/
        ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed 0:ℝ):ℂ))):=
  (em_complete_static_charge_limit direction unit
    epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
    epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS).div_const _

end LowEnergy.GaussComposite.PhysicalEMCompleteStaticCharge
