import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceMovingPoleGaussPreparation

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMovingPoleGaussReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumElectromagneticIdentity PreparationVacuumSourcePreparedState
open SourceQuantumFockGauge SourceQuantumConfigurationHilbert GaussCoreHilbert GaussFockLift GaussQuantumMultiplier
open CanonicalPreparationCreation CanonicalGradedCharge CanonicalGradedSpatialSource
open ProofFreeRicherAnholonomicSource Stage10 Stage10.CanonicalMatter DiracExteriorMatterAction
open QuantizationCheck.Fermion YangMills.FullPairing SU7MotherLieAlgebra
open Electromagnetic.ExternalState Stage9C.Material.SpinPair
open scoped BigOperators InnerProductSpace Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local irreducible] actualMovingPolePreparation sourcePreparation

private theorem fiberAction_entries (A : FiberOp) (v : FockFiber) (word : Occupation) :
    A v word=∑input : Occupation,entry A word input*v input :=by
  have basis : v=∑input : Occupation,v input • EuclideanSpace.single input 1 :=by
    apply PiLp.ext
    intro output
    simp [WithLp.ofLp_sum,Finset.sum_apply,EuclideanSpace.single,Pi.single_apply]
  conv_lhs => rw [basis,map_sum]
  simp only [map_smul,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,entry]
  exact Finset.sum_congr rfl (fun _ _=>mul_comm _ _)

theorem sourcePolePrepared_action_coordinates (epsilon : ℝ) (precision : 0<epsilon) (momentum : PhysicalMomentum)
    (state : RestStateIndex) (A : FiberOp) (word : Occupation) :
    GaussHalfDensity.fockHalfDensityEquiv (lift A (sourcePolePrepared epsilon precision momentum state)) word=
      (A (sourcePoleFiber momentum state) word) • sourcePoleBase epsilon precision :=by
  simp only [lift_apply,LinearIsometryEquiv.apply_symm_apply]
  rw [flatLift_apply]
  simp only [sourcePolePrepared_coordinates,smul_smul]
  rw [←Finset.sum_smul,←fiberAction_entries]

theorem sourcePolePrepared_action_pair (epsilon : ℝ) (precision : 0<epsilon)
    (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex) (A : FiberOp) :
    inner ℂ (sourcePolePrepared epsilon precision leftMomentum left)
      (lift A (sourcePolePrepared epsilon precision rightMomentum right))=
      inner ℂ (sourcePoleFiber leftMomentum left) (A (sourcePoleFiber rightMomentum right)) :=by
  have base : inner ℂ (sourcePoleBase epsilon precision) (sourcePoleBase epsilon precision)=1 :=by
    rw [inner_self_eq_norm_sq_to_K,sourcePoleBase_unit]
    norm_num
  rw [←GaussHalfDensity.fockHalfDensityEquiv.inner_map_map,PiLp.inner_apply]
  simp only [sourcePolePrepared_coordinates,sourcePolePrepared_action_coordinates,
    inner_smul_left,inner_smul_right,base,mul_one]
  rfl

def sourcePoleGaugeMatrix (mu : Fin 4) (direction : P286LieBlockData) : Matrix Mode Mode ℂ:=
  SourceRealScalarFock.branches (Quantum.operatorMatrix (sourceGaugeCanonicalAction mu direction))

theorem sourcePoleGaugeMatrix_original_real (mu : Fin 4) (direction : P286LieBlockData)
    (momentum primal : Quantum.Index→ℂ) :
    (∑i : Mode,∑j : Mode,SourceRealScalarFock.normalizedMomentum momentum i*
      sourcePoleGaugeMatrix mu direction i j*SourceRealScalarFock.normalizedPrimal primal j)=
      ((SourceRealScalarFock.complexBilinear
        (Quantum.operatorMatrix (sourceGaugeCanonicalAction mu direction)) momentum primal).re:ℂ) :=
  SourceRealScalarFock.branches_original_real_bilinear _ _ _

private theorem sourceFullPositive_action (action : Module.End ℂ DiracExteriorMatterCarrier) (matter : DiracExteriorMatterCarrier) :
    SourceRealScalarFock.branches (Quantum.operatorMatrix action)*ᵥSum.elim (Quantum.coordinates matter) (fun _=>0)=
      Sum.elim (Quantum.coordinates (action matter)) (fun _=>0) :=by
  funext mode
  cases mode with
  | inl i =>
    simp only [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,SourceRealScalarFock.branches,
      Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Sum.elim_inl,Sum.elim_inr,
      Matrix.zero_apply,mul_zero,Finset.sum_const_zero,add_zero]
    exact congrFun (Quantum.matrix_action action matter) i
  | inr i =>
    simp only [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,SourceRealScalarFock.branches,
      Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Sum.elim_inl,Sum.elim_inr,
      Matrix.zero_apply,mul_zero,zero_mul,Finset.sum_const_zero,add_zero]

theorem sourcePoleFiber_gauge_pair (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (mu : Fin 4) (direction : P286LieBlockData) :
    inner ℂ (sourcePoleFiber leftMomentum left)
      (quantized (sourcePoleGaugeMatrix mu direction) (sourcePoleFiber rightMomentum right))=
      Quantum.coordinatePair
        (actualMovingPolePreparation leftMomentum left (Stage9DEF.Compatibility.embed (Stage9DEF.Source.vector 0)))
        (sourceGaugeCanonicalAction mu direction
          (actualMovingPolePreparation rightMomentum right (Stage9DEF.Compatibility.embed (Stage9DEF.Source.vector 0)))) :=by
  simp only [sourcePoleFiber]
  rw [quantized_oneParticle,SourceQuantumFockGauge.fiber_pairing]
  simp only [oneParticleFiber,LinearEquiv.apply_symm_apply]
  rw [pairing_oneParticle]
  simp only [sourcePoleGaugeMatrix,sourcePoleCoordinates,sourcePolePrimalCoordinates]
  rw [sourceFullPositive_action]
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    star_zero,mul_zero,Finset.sum_const_zero,add_zero]
  rfl

def sourcePoleGaugeRead (epsilon : ℝ) (precision : 0<epsilon) (leftMomentum rightMomentum : PhysicalMomentum)
    (left right : RestStateIndex) (mu : Fin 4) (direction : P286LieBlockData) : ℂ:=
  4*(spinScale:ℂ)*inner ℂ (sourcePolePrepared epsilon precision leftMomentum left)
    (lift (quantized (sourcePoleGaugeMatrix mu direction)) (sourcePolePrepared epsilon precision rightMomentum right))

theorem sourcePoleGaugeRead_original (epsilon : ℝ) (precision : 0<epsilon)
    (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (mu : Fin 4) (direction : P286LieBlockData) :
    sourcePoleGaugeRead epsilon precision leftMomentum rightMomentum left right mu direction=
      actual.conjugateMatter 0 (canonicalDual (actualMovingPolePreparation leftMomentum left)
        (sourceGaugeDensityAction mu direction
          (actualMovingPolePreparation rightMomentum right (actual.matter 0)))) :=by
  rw [sourcePoleGaugeRead,sourcePolePrepared_action_pair,sourcePoleFiber_gauge_pair,original_prepared_vertex]
  congr 1
  rw [Quantum.coordinatePair_full,←YangMills.FullPairing.natural_inner]
  simp only [YangMills.FullPairing.prepared,operator_coordinates,sourceGaugeCanonicalAction,LinearMap.comp_apply]

theorem sourcePoleGaugeRead_vertex (epsilon : ℝ) (precision : 0<epsilon)
    (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (mu : Fin 4) (direction : P286LieBlockData) :
    sourcePoleGaugeRead epsilon precision leftMomentum rightMomentum left right mu direction=
      (ActionNormalization.phaseMomentum:ℂ)*sourceMovingGaugeVertex mu direction leftMomentum rightMomentum left right :=by
  rw [sourcePoleGaugeRead_original,actualMovingPole_gaugeDensity_vertex]

end LowEnergy.PreparationVacuumMovingPoleGaussReturn
