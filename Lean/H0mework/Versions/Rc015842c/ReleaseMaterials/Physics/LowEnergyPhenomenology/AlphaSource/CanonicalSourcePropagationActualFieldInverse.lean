import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationActualFieldPencil

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationFieldFeedback
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPropagationPencil SourcePropagationResolvent
open PreparationVacuumPhysicalTailPrice PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open Filter Set MeasureTheory
open scoped Topology BigOperators Matrix InnerProductSpace
open SourcePropagationSpectralAxis
local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ Op:=NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ TransferOp:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ TransferOp:=NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedSpace ℝ TransferOp:=ContinuousLinearMap.toNormedSpace
local instance : IsBoundedSMul ℝ TransferOp:=by
  convert! (NormedSpace.toIsBoundedSMul (𝕜:=ℝ) (E:=TransferOp)) using 1
local instance : ContinuousSMul ℝ TransferOp:=by
  convert! (IsBoundedSMul.continuousSMul (α:=ℝ) (β:=TransferOp)) using 1
local instance : ContinuousENorm TransferOp:=by
  convert! (SeminormedAddGroup.toContinuousENorm (E:=TransferOp)) using 1
local instance : AddCommGroup TransferOp:=ContinuousLinearMap.addCommGroup
local instance : IsTopologicalAddGroup TransferOp:=by
  have normal : @IsTopologicalAddGroup TransferOp
      (inferInstance : PseudoMetricSpace TransferOp).toUniformSpace.toTopologicalSpace
      (inferInstance : NormedAddCommGroup TransferOp).toAddCommGroup.toAddGroup:=inferInstance
  convert! normal using 1
local instance : IsScalarTower ℂ TransferOp TransferOp:=⟨by
  intro c A B
  apply ContinuousLinearMap.ext
  intro X
  rfl⟩
local instance : SMulCommClass ℂ TransferOp TransferOp:=⟨by
  intro c A B
  apply ContinuousLinearMap.ext
  intro X
  exact (map_smul A c (B X)).symm⟩

attribute [local irreducible] fieldPencil fieldEvolution fieldEvolutionDerivative propagationPencil
  sourceInverse actualResolvent jointGenerator

/-- Source-owned inverse of the complete background-dependent propagation pencil. -/
def fieldInverse (q : PhysicalResponsePoint) (lambda : ℂ) (h : Field289) : TransferOp:=
  Ring.inverse (fieldPencil q lambda h)

def basePencilUnit (q : PhysicalResponsePoint) (lambda : ℂ) (off : lambda.re≠0) : TransferOpˣ:=
  ⟨propagationPencil q lambda,actualResolvent q lambda,
    actualResolvent_left q lambda off,actualResolvent_right q lambda off⟩

def normBasePencilUnit (q : PhysicalResponsePoint) (lambda : ℂ) (off : lambda.re≠0) :
    @Units TransferOp (inferInstance : NormedRing TransferOp).toRing.toSemiring.toMonoid where
  val:=propagationPencil q lambda
  inv:=actualResolvent q lambda
  val_inv:=by convert! actualResolvent_left q lambda off using 1
  inv_val:=by convert! actualResolvent_right q lambda off using 1

theorem fieldInverse_initial (q : PhysicalResponsePoint) (lambda : ℂ) (off : lambda.re≠0) :
    fieldInverse q lambda 0=actualResolvent q lambda :=by
  unfold fieldInverse
  rw [fieldPencil_initial]
  have paid:=Ring.inverse_unit (basePencilUnit q lambda off)
  convert! paid using 1

theorem fieldPencil_units_generated (q : PhysicalResponsePoint) (lambda : ℂ) (off : lambda.re≠0) :
    ∀ᶠh : Field289 in 𝓝 0,IsUnit (fieldPencil q lambda h) :=by
  have normalBase : @IsUnit TransferOp (inferInstance : NormedRing TransferOp).toRing.toSemiring.toMonoid
      (fieldPencil q lambda 0):=by
    convert! (normBasePencilUnit q lambda off).isUnit using 1
    exact fieldPencil_initial q lambda
  have opened : {A : TransferOp | @IsUnit TransferOp (inferInstance : NormedRing TransferOp).toRing.toSemiring.toMonoid A}∈
      @nhds TransferOp (inferInstance : NormedRing TransferOp).toSeminormedRing.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (fieldPencil q lambda 0):=Units.isOpen.mem_nhds normalBase
  have sameOpen : {A : TransferOp | IsUnit A}∈𝓝 (fieldPencil q lambda 0):=by
    convert! opened using 1
  have h:=(fieldPencil_C2 q lambda).continuousAt.preimage_mem_nhds sameOpen
  convert! h using 1

theorem fieldInverse_C2 (q : PhysicalResponsePoint) (lambda : ℂ) (off : lambda.re≠0) :
    ContDiffAt ℝ 2 (fieldInverse q lambda) 0 :=by
  let u:=normBasePencilUnit q lambda off
  have point : (u:TransferOp)=fieldPencil q lambda 0:=by rw [fieldPencil_initial];rfl
  have outer : ContDiffAt ℝ 2 (Ring.inverse : TransferOp→TransferOp) (fieldPencil q lambda 0):=by
    rw [←point]
    have h:=contDiffAt_ringInverse (𝕜:=ℝ) (R:=TransferOp) (n:=2) u
    convert! h using 1
  exact outer.comp 0 (fieldPencil_C2 q lambda)

theorem fieldInverse_left_generated (q : PhysicalResponsePoint) (lambda : ℂ) (off : lambda.re≠0) :
    ∀ᶠh : Field289 in 𝓝 0,fieldPencil q lambda h*fieldInverse q lambda h=1 :=by
  filter_upwards [fieldPencil_units_generated q lambda off] with h unit
  unfold fieldInverse
  exact Ring.mul_inverse_cancel _ unit

theorem fieldInverse_right_generated (q : PhysicalResponsePoint) (lambda : ℂ) (off : lambda.re≠0) :
    ∀ᶠh : Field289 in 𝓝 0,fieldInverse q lambda h*fieldPencil q lambda h=1 :=by
  filter_upwards [fieldPencil_units_generated q lambda off] with h unit
  unfold fieldInverse
  exact Ring.inverse_mul_cancel _ unit

/-- Every current direction acts through the complete source-produced inverse on both sides. -/
def fieldInverseDerivative (q : PhysicalResponsePoint) (lambda : ℂ) : Field289→L[ℝ] TransferOp:=
  (ContinuousLinearMap.mulLeftRight ℝ TransferOp (actualResolvent q lambda) (actualResolvent q lambda)).comp
    (fieldEvolutionDerivative q)

theorem fieldInverseDerivative_apply (q : PhysicalResponsePoint) (lambda : ℂ) (force : Field289) :
    fieldInverseDerivative q lambda force=
      actualResolvent q lambda*driveOperator q force*actualResolvent q lambda :=by
  have original : fieldInverseDerivative q lambda force=
      actualResolvent q lambda*(fieldEvolutionDerivative q force)*actualResolvent q lambda:=rfl
  exact original.trans (congrArg
    (fun A : TransferOp=>actualResolvent q lambda*A*actualResolvent q lambda)
    (fieldEvolutionDerivative_actual q force))

attribute [local irreducible] fieldInverse fieldInverseDerivative

private theorem inverse_algebra {R : Type*} [Ring R] (A B : R) : -(A*(-B)*A)=A*B*A :=by
  rw [mul_neg,neg_mul,neg_neg]

theorem fieldInverse_ray_derivative (q : PhysicalResponsePoint) (lambda : ℂ) (off : lambda.re≠0)
    (force : Field289) :
    HasDerivAt (fun r : ℝ=>fieldInverse q lambda (r • force))
      (fieldInverseDerivative q lambda force) 0 :=by
  let u:=normBasePencilUnit q lambda off
  have point : (u:TransferOp)=fieldPencil q lambda 0:=by rw [fieldPencil_initial];rfl
  have ray : HasDerivAt (fun r : ℝ=>r • force) force 0:=by
    convert! fieldRay_derivative force 0 using 1
  have normal:=(fieldPencil_C2 q lambda).differentiableAt (by norm_num) |>.hasFDerivAt
  have source : HasDerivAt (fun r : ℝ=>fieldPencil q lambda (r • force)) (-driveOperator q force) 0:=by
    have h:=normal.comp_hasDerivAt_of_eq 0 ray (by simp)
    convert! h using 1
    exact (fieldPencil_current q lambda force).symm
  have inverse : HasFDerivAt (Ring.inverse : TransferOp→TransferOp)
      (-ContinuousLinearMap.mulLeftRight ℝ TransferOp (actualResolvent q lambda) (actualResolvent q lambda))
      (fieldPencil q lambda 0):=by
    have h:=hasFDerivAt_ringInverse (𝕜:=ℝ) u
    convert! h using 1
    exact point.symm
  have h:=inverse.comp_hasDerivAt_of_eq (𝕜:=ℝ) (E:=TransferOp) (F:=TransferOp) (0:ℝ) source (by simp)
  have mapped : HasDerivAt (fun r : ℝ=>fieldInverse q lambda (r • force))
      ((-ContinuousLinearMap.mulLeftRight ℝ TransferOp (actualResolvent q lambda) (actualResolvent q lambda))
        (-driveOperator q force)) 0:=by
    convert! h using 1
    funext r
    unfold fieldInverse
    rfl
  have value : (-ContinuousLinearMap.mulLeftRight ℝ TransferOp (actualResolvent q lambda) (actualResolvent q lambda))
        (-driveOperator q force)=actualResolvent q lambda*driveOperator q force*actualResolvent q lambda:=by
    simp only [neg_apply,ContinuousLinearMap.mulLeftRight_apply]
    convert! inverse_algebra (R:=TransferOp) (actualResolvent q lambda) (driveOperator q force) using 1
  exact mapped.congr_deriv (value.trans (fieldInverseDerivative_apply q lambda force).symm)

end LowEnergy.SourcePropagationFieldFeedback
