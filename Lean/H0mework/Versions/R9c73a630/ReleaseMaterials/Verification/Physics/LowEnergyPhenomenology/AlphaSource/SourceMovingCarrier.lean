import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.SourceModeCurrent

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSharedPoleCarrier
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open Stage9C.Material.SpinPair
open Stage10 Stage10.CanonicalMatter Stage9DEF Stage9DEF.Compatibility
open PreparationVacuumElectromagneticIdentity PreparationVacuumMovingPoleGaussReturn
open CanonicalGradedSpatialSource SourceQuantumFockGauge GaussCoreHilbert GaussFockLift
open SourceQuantumConfigurationHilbert
open YangMills.FullPairing
open scoped BigOperators Matrix InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local irreducible] actualRestStatePreparation sourceMovingPoleValues sourcePoleBase

def movingOverlap (momentum : PhysicalMomentum) : Matrix RestStateIndex RestStateIndex ℂ:=fun origin state=>
  ∑index : Source.Index,star (sourceMovingPoleValues 0 origin index)*sourceMovingPoleValues momentum state index

theorem movingOverlap_values (momentum : PhysicalMomentum) (state : RestStateIndex) :
    (∑origin : RestStateIndex,movingOverlap momentum origin state • sourceMovingPoleValues 0 origin)=
      sourceMovingPoleValues momentum state:=sourceMovingPole_complete 0 _

private def restCoordinateRead (state : RestStateIndex) : (Source.Index→ℂ)→ₗ[ℂ] ℂ where
  toFun := fun values=>(spinScale:ℂ)/2*∑index : Source.Index,star (sourceRestStateValues state index)*values index
  map_add' := by
    intro u v
    simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' := by
    intro c values
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp_rw [mul_left_comm _ c]
    rw [←Finset.mul_sum]
    ring

theorem movingOverlap_restCoefficient (momentum : PhysicalMomentum) (state rest : RestStateIndex) :
    sourceMovingRestCoefficient momentum state rest=
      ∑origin : RestStateIndex,movingOverlap momentum origin state*sourceMovingRestCoefficient 0 origin rest:=by
  have h:=congrArg (restCoordinateRead rest) (movingOverlap_values momentum state)
  simp only [map_sum,map_smul,smul_eq_mul] at h
  exact h.symm

theorem movingOverlap_preparation (momentum : PhysicalMomentum) (state : RestStateIndex) :
    actualMovingPolePreparation momentum state=
      ∑origin : RestStateIndex,movingOverlap momentum origin state • actualMovingPolePreparation 0 origin:=by
  calc
    _=∑rest : RestStateIndex,(∑origin : RestStateIndex,
        movingOverlap momentum origin state*sourceMovingRestCoefficient 0 origin rest) • actualRestStatePreparation rest:=by
      unfold actualMovingPolePreparation
      simp only [movingOverlap_restCoefficient momentum state]
    _= _:=by
      simp only [actualMovingPolePreparation,Finset.sum_smul,Finset.smul_sum,smul_smul]
      rw [Finset.sum_comm]

theorem movingOverlap_primal (momentum : PhysicalMomentum) (state : RestStateIndex) :
    sourcePolePrimalCoordinates momentum state=
      ∑origin : RestStateIndex,movingOverlap momentum origin state • sourcePolePrimalCoordinates 0 origin:=by
  unfold sourcePolePrimalCoordinates
  rw [movingOverlap_preparation]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul]

theorem movingOverlap_coordinates (momentum : PhysicalMomentum) (state : RestStateIndex) :
    sourcePoleCoordinates momentum state=
      ∑origin : RestStateIndex,movingOverlap momentum origin state • sourcePoleCoordinates 0 origin:=by
  funext index
  cases index with
  | inl i=>
    simpa only [sourcePoleCoordinates,Sum.elim_inl,Finset.sum_apply,Pi.smul_apply] using congrFun (movingOverlap_primal momentum state) i
  | inr i=>simp [sourcePoleCoordinates]

private def creationRead : (Mode→ℂ)→ₗ[ℂ] FiberOp where
  toFun := fun values=>∑i : Mode,values i • GaussCARHistory.createFiber i
  map_add' := by
    intro u v
    simp only [Pi.add_apply]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact add_smul (u i) (v i) (GaussCARHistory.createFiber i)
  map_smul' := by
    intro c values
    simp only [Pi.smul_apply,smul_eq_mul,Finset.smul_sum,smul_smul,RingHom.id_apply]

theorem movingOverlap_creation (momentum : PhysicalMomentum) (state : RestStateIndex) :
    sourcePoleCreation momentum state=
      ∑origin : RestStateIndex,movingOverlap momentum origin state • sourcePoleCreation 0 origin:=by
  have h:=congrArg creationRead (movingOverlap_coordinates momentum state)
  simp only [map_sum,map_smul] at h
  exact h

theorem movingOverlap_fiber (momentum : PhysicalMomentum) (state : RestStateIndex) :
    sourcePoleFiber momentum state=
      ∑origin : RestStateIndex,movingOverlap momentum origin state • sourcePoleFiber 0 origin:=by
  rw [←sourcePoleCreation_vacuum,movingOverlap_creation]
  simp only [sum_apply,smul_apply,sourcePoleCreation_vacuum]

theorem movingOverlap_prepared (epsilon : ℝ) (precision : 0<epsilon) (momentum : PhysicalMomentum) (state : RestStateIndex) :
    sourcePolePrepared epsilon precision momentum state=
      ∑origin : RestStateIndex,movingOverlap momentum origin state • sourcePolePrepared epsilon precision 0 origin:=by
  apply GaussHalfDensity.fockHalfDensityEquiv.injective
  simp only [map_sum,map_smul]
  apply PiLp.ext
  intro word
  rw [sourcePolePrepared_coordinates,movingOverlap_fiber]
  simp only [WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,sourcePolePrepared_coordinates,Finset.sum_smul,smul_smul,smul_eq_mul]

end LowEnergy.PreparationVacuumSharedPoleCarrier
