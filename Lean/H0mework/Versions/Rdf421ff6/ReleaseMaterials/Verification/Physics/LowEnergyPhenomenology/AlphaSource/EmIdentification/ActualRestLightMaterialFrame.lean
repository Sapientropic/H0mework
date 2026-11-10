import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualN3MaterialSylvester
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceRestMatterLight

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LowEnergy.GaussComposite.ActualSourceLightCircuit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 YangMills.FullPairing
open GaussCoreHilbert CanonicalGradedSpatialSource ActualSourcePreparationBridge
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open PreparationVacuumElectromagneticIdentity PreparationVacuumMixedFieldReturn
open scoped InnerProductSpace BigOperators
attribute [local irreducible] actualRestStatePreparation

abbrev RestBlock := Bool×Fin 2

def restPrimalWave (state : RestStateIndex) : Quantum.Index→ℂ :=
  Quantum.coordinates (naturalCoordinates.symm
    (operator (actualRestStatePreparation state) (YangMills.FullPairing.prepared 0)))

theorem rest_primal_wave_gram (left right : RestStateIndex) :
    (∑i : Quantum.Index,star (restPrimalWave left i)*restPrimalWave right i)=
      if left=right then 1 else 0 := by
  change Quantum.coordinatePair _ _=_
  rw [Quantum.coordinatePair_full,←YangMills.FullPairing.natural_inner]
  simp only [LinearEquiv.apply_symm_apply]
  exact actualRestState_orthonormal 0 left right

def restModeWave (dual : Bool) (state : RestStateIndex) : Mode→ℂ :=
  Sum.elim (fun i=>if dual then 0 else restPrimalWave state i)
    (fun i=>if dual then star (restPrimalWave state i) else 0)

theorem rest_mode_wave_gram (dual dual' : Bool) (left right : RestStateIndex) :
    (∑i : Mode,star (restModeWave dual left i)*restModeWave dual' right i)=
      if dual=dual' ∧ left=right then 1 else 0 := by
  cases dual <;> cases dual'
  · simpa only [restModeWave,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
      Bool.false_eq_true,if_false,star_zero,mul_zero,Finset.sum_const_zero,add_zero,
      true_and] using rest_primal_wave_gram left right
  · simp [restModeWave,Fintype.sum_sum_type]
  · simp [restModeWave,Fintype.sum_sum_type]
  · simpa only [restModeWave,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
      if_true,star_zero,zero_mul,Finset.sum_const_zero,zero_add,star_star,mul_comm,
      true_and,eq_comm] using rest_primal_wave_gram right left

def restBlockFrame (block : RestBlock) : Matrix Mode (Fin 4) ℂ :=
  fun mode state=>restModeWave block.1 (block.2,state) mode

/-- The two primal and two independently conjugate source frames generate their own orthogonal Gram. -/
theorem rest_block_frame_gram (left right : RestBlock) :
    (restBlockFrame left).conjTranspose*restBlockFrame right=
      if left=right then (1:Matrix (Fin 4) (Fin 4) ℂ) else 0 := by
  ext i j
  have h:=rest_mode_wave_gram left.1 right.1 (left.2,i) (right.2,j)
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,restBlockFrame]
  by_cases blocks : left=right
  · rw [if_pos blocks,Matrix.one_apply]
    by_cases states : i=j <;> simpa [Prod.mk.injEq,Prod.ext_iff,blocks,states] using h
  · rw [if_neg blocks,Matrix.zero_apply]
    have distinct : ¬(left.1=right.1 ∧ left.2=right.2) :=
      fun both=>blocks (Prod.ext both.1 both.2)
    by_cases states : i=j <;> simpa [Prod.mk.injEq,←and_assoc,distinct,states] using h

def restBlockRestriction (block : RestBlock) (A : FullMaterialMatrix) : RestMatterMatrix :=
  (restBlockFrame block).conjTranspose*A*restBlockFrame block

def restBlockLift (block : RestBlock) (A : RestMatterMatrix) : FullMaterialMatrix :=
  restBlockFrame block*A*(restBlockFrame block).conjTranspose

theorem rest_block_restriction_lift (left right : RestBlock) (A : RestMatterMatrix) :
    restBlockRestriction left (restBlockLift right A)=if left=right then A else 0 := by
  unfold restBlockRestriction restBlockLift
  calc
    _=((restBlockFrame left).conjTranspose*restBlockFrame right)*A*
      ((restBlockFrame right).conjTranspose*restBlockFrame left) := by simp only [Matrix.mul_assoc]
    _=if left=right then A else 0 := by
      rw [rest_block_frame_gram,rest_block_frame_gram]
      by_cases same : left=right
      · subst right;simp
      · simp [same,Ne.symm same]

theorem rest_block_lift_add (block : RestBlock) (A B : RestMatterMatrix) :
    restBlockLift block (A+B)=restBlockLift block A+restBlockLift block B := by
  simp only [restBlockLift,Matrix.mul_add,Matrix.add_mul]

theorem rest_block_lift_smul (block : RestBlock) (q : ℂ) (A : RestMatterMatrix) :
    restBlockLift block (q • A)=q • restBlockLift block A := by
  simp only [restBlockLift,Matrix.mul_smul,Matrix.smul_mul]

def restBlockLightMatrix (block : RestBlock) (A : FullMaterialMatrix) : FullMaterialMatrix :=
  restBlockLift block (sourceRestLight (restBlockRestriction block A))

def sourceRestLightMatrix (A : FullMaterialMatrix) : FullMaterialMatrix :=
  ∑block : RestBlock,restBlockLightMatrix block A

def sourceRestHeavyMatrix (A : FullMaterialMatrix) : FullMaterialMatrix :=
  ∑block : RestBlock,restBlockLift block
    (sourceRestHeavyUp (restBlockRestriction block A)+sourceRestHeavyDown (restBlockRestriction block A))

def restBlockProjector (block : RestBlock) : FullMaterialMatrix :=
  restBlockLift block 1

def sourceRestCarrierProjector : FullMaterialMatrix := ∑block : RestBlock,restBlockProjector block

def sourceRestSelectedMatrix (A : FullMaterialMatrix) : FullMaterialMatrix :=
  ∑block : RestBlock,restBlockProjector block*A*restBlockProjector block

theorem rest_block_light_heavy (block : RestBlock) (A : FullMaterialMatrix) :
    restBlockLightMatrix block A+restBlockLift block
      (sourceRestHeavyUp (restBlockRestriction block A)+sourceRestHeavyDown (restBlockRestriction block A))=
        restBlockProjector block*A*restBlockProjector block := by
  rw [restBlockLightMatrix,←rest_block_lift_add]
  have partition:=sourceRestMatter_partition (restBlockRestriction block A)
  have same : sourceRestLight (restBlockRestriction block A)+
      (sourceRestHeavyUp (restBlockRestriction block A)+sourceRestHeavyDown (restBlockRestriction block A))=
      restBlockRestriction block A := by rw [←add_assoc,partition]
  rw [same]
  simp only [restBlockLift,restBlockRestriction,restBlockProjector,Matrix.mul_one,Matrix.mul_assoc]

theorem source_rest_light_heavy_selected (A : FullMaterialMatrix) :
    sourceRestLightMatrix A+sourceRestHeavyMatrix A=sourceRestSelectedMatrix A := by
  rw [sourceRestLightMatrix,sourceRestHeavyMatrix,←Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun block _=>rest_block_light_heavy block A

/-- Light is the source-generated HS zero-spectrum projection in every actual rest frame. -/
theorem source_rest_light_generated (block : RestBlock) (A : FullMaterialMatrix) :
    restBlockLightMatrix block A=restBlockLift block
      (restBlockRestriction block A+(25/36:ℂ) •
        actualRestMatchingSylvester 0 block.2
          (actualRestMatchingSylvester 0 block.2 (restBlockRestriction block A))) := by
  rw [restBlockLightMatrix,sourceRestLight_generated 0 block.2]

theorem source_rest_light_kernel (block : RestBlock) (A : FullMaterialMatrix) :
    actualRestMatchingSylvester 0 block.2 (sourceRestLight (restBlockRestriction block A))=0 :=
  actualRestMatchingSylvester_light 0 block.2 _

end LowEnergy.GaussComposite.ActualSourceLightCircuit
