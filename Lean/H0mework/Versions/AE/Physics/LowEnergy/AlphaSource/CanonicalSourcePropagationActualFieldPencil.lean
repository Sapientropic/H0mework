import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationAxisReadback

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
abbrev Op:=SourcePropagationResolvent.Op
abbrev TransferOp:=SourcePropagationResolvent.TransferOp
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

attribute [local irreducible] jointGenerator jointCurrent jointHessian evolutionGenerator propagationPencil

/-- The same two original source generators at their common real field background. -/
def fieldGenerators (q : PhysicalResponsePoint) (h : Field289) : Op×Op:=
  ⟨(-Complex.I) • jointGenerator (q.p+q.k) q.F 0 h,
    (-Complex.I) • jointGenerator q.p q.F 0 h⟩

def evolutionMap : (Op×Op)→L[ℂ] TransferOp:=
  -(ContinuousLinearMap.mul ℂ Op).comp (ContinuousLinearMap.fst ℂ Op Op)+
    (ContinuousLinearMap.mul ℂ Op).flip.comp (ContinuousLinearMap.snd ℂ Op Op)

def fieldEvolution (q : PhysicalResponsePoint) (h : Field289) : TransferOp:=
  evolutionMap (fieldGenerators q h)

def fieldPencil (q : PhysicalResponsePoint) (lambda : ℂ) (h : Field289) : TransferOp:=
  lambda • ContinuousLinearMap.id ℂ Op-fieldEvolution q h

theorem fieldEvolution_apply (q : PhysicalResponsePoint) (h : Field289) (A : Op) :
    fieldEvolution q h A=-((-Complex.I) • jointGenerator (q.p+q.k) q.F 0 h)*A+
      A*((-Complex.I) • jointGenerator q.p q.F 0 h) :=rfl

theorem fieldPencil_initial (q : PhysicalResponsePoint) (lambda : ℂ) :
    fieldPencil q lambda 0=propagationPencil q lambda :=by
  apply ContinuousLinearMap.ext
  intro A
  simp only [fieldPencil,fieldEvolution_apply,propagationPencil,sub_apply,smul_apply,ContinuousLinearMap.id_apply,evolutionGenerator_apply,leftGenerator,rightGenerator]

def realEvolutionMap :
    @ContinuousLinearMap ℝ ℝ inferInstance inferInstance (RingHom.id ℝ) (Op×Op)
      (inferInstance : PseudoMetricSpace (Op×Op)).toUniformSpace.toTopologicalSpace
      (inferInstance : NormedAddCommGroup (Op×Op)).toAddCommGroup.toAddCommMonoid
      TransferOp (inferInstance : PseudoMetricSpace TransferOp).toUniformSpace.toTopologicalSpace
      (inferInstance : NormedAddCommGroup TransferOp).toAddCommGroup.toAddCommMonoid
      (inferInstance : NormedSpace ℝ (Op×Op)).toModule
      (inferInstance : NormedSpace ℝ TransferOp).toModule:=by
  convert! evolutionMap.restrictScalars ℝ using 1

theorem fieldGenerators_C2 (q : PhysicalResponsePoint) : ContDiffAt ℝ 2 (fieldGenerators q) 0 :=by
  exact ((jointGenerator_C2 (q.p+q.k) q.F 0).const_smul (-Complex.I)).prodMk
    ((jointGenerator_C2 q.p q.F 0).const_smul (-Complex.I))

theorem fieldEvolution_C2 (q : PhysicalResponsePoint) : ContDiffAt ℝ 2 (fieldEvolution q) 0 :=by
  have h:=(ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Op×Op) (F:=TransferOp) realEvolutionMap).contDiffAt.comp 0 (fieldGenerators_C2 q)
  convert! h using 1

theorem fieldPencil_C2 (q : PhysicalResponsePoint) (lambda : ℂ) : ContDiffAt ℝ 2 (fieldPencil q lambda) 0 :=by
  exact contDiffAt_const.sub (fieldEvolution_C2 q)

/-- All original source current directions are retained before the two-sided propagation map. -/
def fieldCurrentPair (q : PhysicalResponsePoint) : Field289→L[ℝ] (Op×Op):=
  ((-Complex.I) • jointCurrent (q.p+q.k) q.F 0 0).prod
    ((-Complex.I) • jointCurrent q.p q.F 0 0)

theorem fieldCurrentPair_apply (q : PhysicalResponsePoint) (force : Field289) :
    fieldCurrentPair q force=(leftCurrent q force,rightCurrent q force) :=rfl

theorem fieldGenerators_derivative (q : PhysicalResponsePoint) :
    HasFDerivAt (fieldGenerators q) (fieldCurrentPair q) 0 :=by
  have left:=(jointGenerator_C2 (q.p+q.k) q.F 0).differentiableAt (by norm_num) |>.hasFDerivAt
  have right:=(jointGenerator_C2 q.p q.F 0).differentiableAt (by norm_num) |>.hasFDerivAt
  have h:=(left.const_smul (-Complex.I)).prodMk (right.const_smul (-Complex.I))
  convert! h using 1
  unfold fieldCurrentPair jointCurrent
  rfl

def fieldEvolutionDerivative (q : PhysicalResponsePoint) : Field289→L[ℝ] TransferOp:=
  (evolutionMap.restrictScalars ℝ).comp (fieldCurrentPair q)

theorem fieldEvolution_derivative (q : PhysicalResponsePoint) :
    HasFDerivAt (fieldEvolution q) (fieldEvolutionDerivative q) 0 :=by
  have normal : @HasFDerivAt ℝ _ Field289
      (inferInstance : NormedAddCommGroup Field289).toAddCommGroup
      (inferInstance : NormedSpace ℝ Field289).toModule
      (inferInstance : PseudoMetricSpace Field289).toUniformSpace.toTopologicalSpace
      (Op×Op) (inferInstance : NormedAddCommGroup (Op×Op)).toAddCommGroup
      (inferInstance : NormedSpace ℝ (Op×Op)).toModule
      (inferInstance : PseudoMetricSpace (Op×Op)).toUniformSpace.toTopologicalSpace
      (fieldGenerators q) (fieldCurrentPair q) 0:=by
    convert! fieldGenerators_derivative q using 1
  have h:=(ContinuousLinearMap.hasFDerivAt (𝕜:=ℝ) (E:=Op×Op) (F:=TransferOp) realEvolutionMap).comp (E:=Field289) (F:=Op×Op) (G:=TransferOp) 0 normal
  convert! h using 1

theorem fieldEvolutionDerivative_actual (q : PhysicalResponsePoint) (force : Field289) :
    fieldEvolutionDerivative q force=driveOperator q force :=by
  apply ContinuousLinearMap.ext
  intro A
  rfl

theorem fieldPencil_derivative (q : PhysicalResponsePoint) (lambda : ℂ) :
    HasFDerivAt (fieldPencil q lambda) (-fieldEvolutionDerivative q) 0 :=by
  have normal : @HasFDerivAt ℝ _ Field289
      (inferInstance : NormedAddCommGroup Field289).toAddCommGroup
      (inferInstance : NormedSpace ℝ Field289).toModule
      (inferInstance : PseudoMetricSpace Field289).toUniformSpace.toTopologicalSpace
      TransferOp (inferInstance : NormedAddCommGroup TransferOp).toAddCommGroup
      (inferInstance : NormedSpace ℝ TransferOp).toModule
      (inferInstance : PseudoMetricSpace TransferOp).toUniformSpace.toTopologicalSpace
      (fieldEvolution q) (fieldEvolutionDerivative q) 0:=by
    convert! fieldEvolution_derivative q using 1
  convert! normal.const_sub (lambda • ContinuousLinearMap.id ℂ Op) using 1

attribute [local irreducible] fieldEvolutionDerivative fieldPencil

theorem fieldPencil_current (q : PhysicalResponsePoint) (lambda : ℂ) (force : Field289) :
    fderiv ℝ (fieldPencil q lambda) 0 force=-driveOperator q force :=by
  have normal : @HasFDerivAt ℝ _ Field289
      (inferInstance : NormedAddCommGroup Field289).toAddCommGroup
      (inferInstance : NormedSpace ℝ Field289).toModule
      (inferInstance : PseudoMetricSpace Field289).toUniformSpace.toTopologicalSpace
      TransferOp (inferInstance : NormedAddCommGroup TransferOp).toAddCommGroup
      (inferInstance : NormedSpace ℝ TransferOp).toModule
      (inferInstance : PseudoMetricSpace TransferOp).toUniformSpace.toTopologicalSpace
      (fieldPencil q lambda) (-fieldEvolutionDerivative q) 0:=by
    convert! fieldPencil_derivative q lambda using 1
  have h:=congrArg (fun D : Field289→L[ℝ] TransferOp=>D force) normal.fderiv
  have expected : (-fieldEvolutionDerivative q) force=-driveOperator q force:=by
    rw [neg_apply,fieldEvolutionDerivative_actual]
  convert! h.trans expected using 1

end LowEnergy.SourcePropagationFieldFeedback
