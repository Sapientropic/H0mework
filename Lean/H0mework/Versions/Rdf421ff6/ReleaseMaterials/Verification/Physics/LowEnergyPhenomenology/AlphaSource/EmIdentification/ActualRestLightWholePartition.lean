import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualRestLightMaterialFrame

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LowEnergy.GaussComposite.ActualSourceLightCircuit
open GaussCoreHilbert CanonicalGradedSpatialSource ActualSourcePreparationBridge
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open PreparationVacuumElectromagneticIdentity PreparationVacuumMixedFieldReturn
open scoped InnerProductSpace BigOperators Matrix Matrix.Norms.L2Operator
local instance : DecidableEq Mode:=Classical.decEq _
local instance fullMaterialFinite : FiniteDimensional ℂ FullMaterialMatrix:=Matrix.finiteDimensional

theorem rest_block_projector_product (left right : RestBlock) :
    restBlockProjector left*restBlockProjector right=if left=right then restBlockProjector left else 0 := by
  unfold restBlockProjector restBlockLift
  simp only [Matrix.mul_one]
  calc
    _=restBlockFrame left*((restBlockFrame left).conjTranspose*restBlockFrame right)*
      (restBlockFrame right).conjTranspose := by simp only [Matrix.mul_assoc]
    _=if left=right then restBlockFrame left*(restBlockFrame left).conjTranspose else 0 := by
      rw [rest_block_frame_gram]
      by_cases same : left=right
      · subst right;simp
      · simp [same]

theorem source_rest_carrier_idempotent : sourceRestCarrierProjector*sourceRestCarrierProjector=sourceRestCarrierProjector := by
  unfold sourceRestCarrierProjector
  simp only [Finset.sum_mul,Finset.mul_sum,rest_block_projector_product]
  simp

def sourceRestCrossMatrix (A : FullMaterialMatrix) : FullMaterialMatrix :=
  ∑left : RestBlock,∑right : RestBlock,
    if left=right then 0 else restBlockProjector left*A*restBlockProjector right

/-- Every direction outside the source two-four frames, including the weak spectator, remains in these three full-matrix arms. -/
def sourceRestOutsideMatrix (A : FullMaterialMatrix) : FullMaterialMatrix :=
  (1-sourceRestCarrierProjector)*A*(1-sourceRestCarrierProjector)+
    (1-sourceRestCarrierProjector)*A*sourceRestCarrierProjector+
    sourceRestCarrierProjector*A*(1-sourceRestCarrierProjector)

theorem source_rest_selected_cross (A : FullMaterialMatrix) :
    sourceRestSelectedMatrix A+sourceRestCrossMatrix A=sourceRestCarrierProjector*A*sourceRestCarrierProjector := by
  have expand : sourceRestCarrierProjector*A*sourceRestCarrierProjector=
      ∑left : RestBlock,∑right : RestBlock,restBlockProjector left*A*restBlockProjector right := by
    unfold sourceRestCarrierProjector
    rw [Finset.sum_mul,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro left _
    rw [Finset.mul_sum]
  rw [expand]
  unfold sourceRestSelectedMatrix sourceRestCrossMatrix
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro left _
  have diagonal : (∑right : RestBlock,if left=right then restBlockProjector left*A*restBlockProjector right else 0)=
      restBlockProjector left*A*restBlockProjector left := by simp
  rw [←diagonal,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro right _
  by_cases same : left=right <;> simp [same]

/-- Source light/heavy, cross-frame, and outside-frame effects exhaust the original complete matrix. -/
theorem source_rest_whole_matrix_partition (A : FullMaterialMatrix) :
    sourceRestLightMatrix A+sourceRestHeavyMatrix A+sourceRestCrossMatrix A+sourceRestOutsideMatrix A=A := by
  rw [source_rest_light_heavy_selected,source_rest_selected_cross]
  unfold sourceRestOutsideMatrix
  noncomm_ring

theorem rest_block_restriction_add (block : RestBlock) (A B : FullMaterialMatrix) :
    restBlockRestriction block (A+B)=restBlockRestriction block A+restBlockRestriction block B := by
  simp only [restBlockRestriction,Matrix.mul_add,Matrix.add_mul]

theorem rest_block_restriction_smul (block : RestBlock) (q : ℂ) (A : FullMaterialMatrix) :
    restBlockRestriction block (q • A)=q • restBlockRestriction block A := by
  simp only [restBlockRestriction,Matrix.mul_smul,Matrix.smul_mul]

private theorem rest_light_add (A B : RestMatterMatrix) : sourceRestLight (A+B)=sourceRestLight A+sourceRestLight B := by
  ext i j
  by_cases same : (i=0 ↔ j=0) <;> simp [sourceRestLight,same]

private theorem rest_light_smul (q : ℂ) (A : RestMatterMatrix) : sourceRestLight (q • A)=q • sourceRestLight A := by
  ext i j
  by_cases same : (i=0 ↔ j=0) <;> simp [sourceRestLight,same]

def sourceRestLightMap : FullMaterialMatrix→L[ℂ]FullMaterialMatrix :=
  (show FullMaterialMatrix→ₗ[ℂ]FullMaterialMatrix from
    {toFun:=sourceRestLightMatrix
     map_add':=by
       intro A B
       simp only [sourceRestLightMatrix,restBlockLightMatrix,rest_block_restriction_add,
         rest_light_add,rest_block_lift_add,Finset.sum_add_distrib]
     map_smul':=by
       intro q A
       simp only [sourceRestLightMatrix,restBlockLightMatrix,rest_block_restriction_smul,
         rest_light_smul,rest_block_lift_smul,Finset.smul_sum,RingHom.id_apply]}).toContinuousLinearMap

theorem source_rest_light_map_value (A : FullMaterialMatrix) : sourceRestLightMap A=sourceRestLightMatrix A := rfl

theorem source_rest_light_frame_retraction (block : RestBlock) (A : FullMaterialMatrix) :
    restBlockRestriction block (sourceRestLightMatrix A)=sourceRestLight (restBlockRestriction block A) := by
  unfold sourceRestLightMatrix restBlockLightMatrix
  have sum : restBlockRestriction block (∑b : RestBlock,restBlockLift b
      (sourceRestLight (restBlockRestriction b A)))=
      ∑b : RestBlock,restBlockRestriction block (restBlockLift b
        (sourceRestLight (restBlockRestriction b A))) := by
    simp only [restBlockRestriction,Matrix.mul_sum,Matrix.sum_mul]
  rw [sum]
  simp only [rest_block_restriction_lift]
  simp

theorem source_rest_light_idempotent (A : FullMaterialMatrix) : sourceRestLightMatrix (sourceRestLightMatrix A)=sourceRestLightMatrix A := by
  unfold sourceRestLightMatrix
  apply Finset.sum_congr rfl
  intro block _
  change restBlockLift block
    (sourceRestLight (restBlockRestriction block (sourceRestLightMatrix A)))=restBlockLift block
      (sourceRestLight (restBlockRestriction block A))
  rw [source_rest_light_frame_retraction,sourceRestLight_idempotent]

/-- The actual omitted source arms are generated explicitly, before quantization or configuration integration. -/
def sourceRestRemainderMatrix (A : FullMaterialMatrix) : FullMaterialMatrix :=
  sourceRestHeavyMatrix A+sourceRestCrossMatrix A+sourceRestOutsideMatrix A

private theorem rest_remainder_value (A : FullMaterialMatrix) :
    sourceRestRemainderMatrix A=A-sourceRestLightMatrix A := by
  have whole:=source_rest_whole_matrix_partition A
  apply eq_sub_iff_add_eq.mpr
  unfold sourceRestRemainderMatrix
  calc
    _=sourceRestLightMatrix A+sourceRestHeavyMatrix A+sourceRestCrossMatrix A+sourceRestOutsideMatrix A := by abel
    _=A :=whole

def sourceRestRemainderMap : FullMaterialMatrix→L[ℂ]FullMaterialMatrix :=
  (show FullMaterialMatrix→ₗ[ℂ]FullMaterialMatrix from
    {toFun:=sourceRestRemainderMatrix
     map_add':=by
       intro A B
       rw [rest_remainder_value,rest_remainder_value,rest_remainder_value]
       change A+B-sourceRestLightMap (A+B)=_
       rw [map_add];abel
     map_smul':=by
       intro q A
       rw [rest_remainder_value,rest_remainder_value]
       change q • A-sourceRestLightMap (q • A)=q • (A-sourceRestLightMap A)
       rw [map_smul,smul_sub]}).toContinuousLinearMap

theorem source_rest_light_remainder (A : FullMaterialMatrix) :
    sourceRestLightMap A+sourceRestRemainderMap A=A := by
  change sourceRestLightMatrix A+sourceRestRemainderMatrix A=A
  rw [rest_remainder_value];abel

end LowEnergy.GaussComposite.ActualSourceLightCircuit
