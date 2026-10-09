import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceStaticSpatialCoupling

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
open PreparationPhysicalStaticSpatialCouplingReturn
open PreparationVacuumPhysicalPoleSheet
open PreparationVacuumPhysicalCharacteristic
open PreparationPhysicalDressedPhotonCouplingReturn
open PreparationVacuumStaticPoleResponse PreparationVacuumOriginalGreenFeedback
open PreparationVacuumFullOriginResponse PreparationVacuumFieldCovector PreparationVacuumSourcePreparedResponse
open GaussUnitaryHistory (Index)
open Filter Set
open scoped BigOperators Matrix Topology InnerProductSpace

/-- The complete prepared source/detector contraction of the original static native field.
It keeps both original completed-leg preparations and the full 289-field Green. -/
def sourceThomsonStaticInteraction
    (direction : PhysicalMomentum) (unit : spatialSquare direction=1) (kappa : staticDomain)
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2) : ℂ :=
  sourceStaticSpatialInteraction direction unit kappa
    epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
    epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS

/-- The same static leading coefficient read directly from the original full residue. -/
def sourceThomsonStaticCEM
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2) : ℂ :=
  ∑i,preparedCovector epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD i*
    staticResidue (preparedCovector epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS) i

/-- The zero-momentum/static pole is the source's C_EM read before hbar*c normalization. -/
def sourceThomsonAlphaSource (branch : Fin 2)
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2) : ℂ :=
  ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)⁻¹ *
    sourceThomsonStaticCEM epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
      epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS

/-- The original kappa family converges to the full static C_EM read. -/
theorem sourceThomsonStaticInteraction_generated
    (direction : PhysicalMomentum) (unit : spatialSquare direction=1)
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2) :
    Tendsto
      (fun kappa : staticDomain => (-(kappa.val:ℂ)^2) *
        sourceThomsonStaticInteraction direction unit kappa
          epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
          epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS)
      staticApproach
      (𝓝 (sourceThomsonStaticCEM epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
        epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS)) := by
  exact sourceStaticSpatialInteraction_generated direction unit
    epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
    epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS

/-- This is the exact source normalization: the same full tensor is divided once by hbar_source*c_source. -/
theorem sourceThomsonAlphaSource_eq_normalized
    (branch : Fin 2)
    (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
    (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
    (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
    (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2) :
    sourceThomsonAlphaSource branch epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
      epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS =
      ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)⁻¹ *
        sourceThomsonStaticCEM epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
          epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS := by
  rfl

/-- Source full-field Schur decomposition: pole, contact, and complement are retained separately. -/
def sourceThomsonFinitePole
    (direction : PhysicalMomentum) (unit : spatialSquare direction=1) (kappa : staticDomain)
    (forcing : Fin 289→ℂ) : Fin 289→ℂ :=
  nativeEffectiveFrame (sourceStaticSpatialPoint direction unit kappa)*ᵥ
    ((sourceStaticSpatialKernel direction unit kappa)⁻¹*ᵥ
      sourceSpatialStaticSourceReader direction unit kappa forcing)

/-- Source full-field Schur decomposition: finite pole, contact, and complement are retained separately. -/
theorem sourceThomsonSchur_split
    (direction : PhysicalMomentum) (unit : spatialSquare direction=1) (kappa : staticDomain)
    (forcing detector : Fin 289→ℂ) :
    (∑i,detector i*((-(kappa.val:ℂ)^2)*sourceSpatialStaticNativeField direction unit kappa forcing i)) =
      (∑i,detector i*sourceThomsonFinitePole direction unit kappa forcing i)+
      (∑i,detector i*((-(kappa.val:ℂ)^2)*sourceSpatialStaticRegularField direction unit kappa forcing i)) := by
  have h:=sourceSpatialStaticNativeFieldSchur direction unit kappa forcing
  rw [h]
  unfold sourceThomsonFinitePole sourceSpatialStaticRegularField sourceSpatialStaticSourceReader
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  have nonzero1 : (kappa.val:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (by exact_mod_cast ne_of_gt kappa.property.1)
  have nonzero : ((kappa.val:ℂ)^2)≠0 := pow_ne_zero 2 nonzero1
  apply Finset.sum_congr rfl
  intro i _
  field_simp [nonzero,nonzero1]
  ring

end LowEnergy.PreparationPhysicalThomsonMatchingReturn
