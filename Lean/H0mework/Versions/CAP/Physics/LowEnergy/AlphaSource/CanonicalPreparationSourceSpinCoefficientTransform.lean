import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceSpinBranches
import Mathlib.LinearAlgebra.Matrix.Kronecker

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumSpinGaussContraction
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open Stage9C.Material.SpinPair StageNineLorentzConnectionVariation
open PreparationVacuumGravityLegendreSource PreparationVacuumCoframeLegendreSource
open PreparationVacuumCoframeQuantumCurrent PreparationVacuumCoframeSpinReduction
open PreparationVacuumSourceFieldFamily SourceQuantumConfigurationHilbert
open SourceQuantumGaugeSliceCoordinates GaussHistoryHilbert PreparationVacuumMixedFieldReturn
open scoped Topology BigOperators Matrix Kronecker

def sourceCoframeSlots (e : LorentzianCoframe) : Matrix LorentzIndex LorentzIndex ℝ:=
  e ⊗ₖ (1:Matrix (Fin 6) (Fin 6) ℝ)

theorem sourceCoframeSlots_entry (e : LorentzianCoframe) (i j : LorentzIndex) :
    sourceCoframeSlots e i j=if i.2=j.2 then e i.1 j.1 else 0:=by
  rcases i with ⟨mu,a⟩
  rcases j with ⟨nu,b⟩
  simp only [sourceCoframeSlots,Matrix.kronecker_apply,Matrix.one_apply,mul_ite,mul_one,mul_zero]

theorem sourceCoframeSlots_mul (e f : LorentzianCoframe) :
    sourceCoframeSlots e*sourceCoframeSlots f=sourceCoframeSlots (e*f):=by
  rw [sourceCoframeSlots,sourceCoframeSlots,sourceCoframeSlots,←Matrix.mul_kronecker_mul,one_mul]

theorem sourceCoframeSlots_one : sourceCoframeSlots (1:LorentzianCoframe)=1:=
  Matrix.one_kronecker_one

theorem sourceCoframeSlots_inverse (e : LorentzianCoframe) (nondegenerate : e.det≠0) :
    sourceCoframeSlots e*sourceCoframeSlots e⁻¹=1 ∧ sourceCoframeSlots e⁻¹*sourceCoframeSlots e=1:=by
  constructor
  · rw [sourceCoframeSlots_mul,Matrix.mul_nonsing_inv e (isUnit_iff_ne_zero.mpr nondegenerate),sourceCoframeSlots_one]
  · rw [sourceCoframeSlots_mul,Matrix.nonsing_inv_mul e (isUnit_iff_ne_zero.mpr nondegenerate),sourceCoframeSlots_one]

def sourceFlatLorentzMatrix : Matrix LorentzIndex LorentzIndex ℝ:=Matrix.of sourceFlatLorentzInverse

theorem sourceLorentzInverse_slots (e : LorentzianCoframe) :
    sourceLorentzInverse e=e.det⁻¹ •
      ((sourceCoframeSlots e).transpose*sourceFlatLorentzMatrix*sourceCoframeSlots e):=by
  unfold sourceLorentzInverse
  congr 1
  ext i j
  simp only [sourceLorentzInverseNumerator,sourceFlatLorentzMatrix,Matrix.of_apply,Matrix.mul_apply,Matrix.transpose_apply,
    sourceCoframeSlots_entry,Fintype.sum_prod_type,ite_mul,mul_ite]
  simp
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]

private def complexCoordinate (a : Fin 8) : DiracMatrix→ₗ[ℂ] ℂ where
  toFun A:=sourceSpinCoordinates A a
  map_add' A B:=by
    cases a using Fin.cases with
    | zero=>simp only [sourceSpinCoordinates,Fin.cases_zero,Matrix.trace_add,add_div]
    | succ a=>simp only [sourceSpinCoordinates,Fin.cases_succ,Matrix.mul_add,Matrix.trace_add]
  map_smul' c A:=by
    cases a using Fin.cases with
    | zero=>simp only [sourceSpinCoordinates,Fin.cases_zero,Matrix.trace_smul,smul_eq_mul,RingHom.id_apply];ring
    | succ a=>simp only [sourceSpinCoordinates,Fin.cases_succ,Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul,RingHom.id_apply]

private def realCoordinate (a : Fin 8) : DiracMatrix→ₗ[ℝ] ℝ:=
  if a.val<4 then Complex.imCLM.toLinearMap.comp ((complexCoordinate a).restrictScalars ℝ)
    else Complex.reCLM.toLinearMap.comp ((complexCoordinate a).restrictScalars ℝ)

def sourceFlatSpinCoefficient : Matrix LorentzIndex (Fin 8) ℝ:=
  Matrix.of (fun i a=>realCoordinate a (sourceSpinWord i.1 i.2)/2)

def sourceSpinCoefficientMatrix (z : SourceCoordinateSlice) : Matrix LorentzIndex (Fin 8) ℝ:=
  Matrix.of (fun i a=>sourceGaussRealSpinCoefficient z i a)

theorem sourceSpinCoefficientMatrix_generated (z : SourceCoordinateSlice) :
    sourceSpinCoefficientMatrix z=lapse •
      (sourceCoframeSlots (sourceGaussCoframe z)⁻¹*sourceFlatSpinCoefficient):=by
  ext i a
  have actual : sourceSpinCoefficientMatrix z i a=realCoordinate a (sourceGaussSpinClifford z i):=by
    by_cases phase : a.val<4
    · simp only [sourceSpinCoefficientMatrix,Matrix.of_apply,sourceGaussRealSpinCoefficient,
        sourceGaussSpinCoordinates,realCoordinate,phase,ite_true]
      rfl
    · simp only [sourceSpinCoefficientMatrix,Matrix.of_apply,sourceGaussRealSpinCoefficient,
        sourceGaussSpinCoordinates,realCoordinate,phase,ite_false]
      rfl
  rw [actual,sourceSpinWords_generated]
  have realWord (r : ℝ) (W : DiracMatrix) : (r:ℂ) • W=r • W:=by
    ext b c
    change (r:ℂ)*W b c=r • W b c
    exact Complex.real_smul.symm
  simp only [realWord]
  simp only [map_sum,map_smul,RingHom.id_apply,smul_eq_mul,sourceSpinWordWeight,
    loweredLorentzConnectionCoefficient_ofBivectorOneForm,sourceConnectionBasis]
  simp only [sourceCoframeSlots_entry,sourceFlatSpinCoefficient,Matrix.of_apply,Matrix.smul_apply,
    Matrix.mul_apply,Fintype.sum_prod_type,ite_mul]
  rcases i with ⟨nu,p⟩
  simp only [Prod.mk.injEq,mul_ite,ite_mul,ite_div,mul_zero,zero_mul,zero_div,
    ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  ring

def sourceSpinOrderedTensor (z : SourceCoordinateSlice) : Matrix (Fin 8) (Fin 8) ℝ:=
  (sourceSpinCoefficientMatrix z).transpose*sourceLorentzInverse (sourceGaussCoframe z)*
    sourceSpinCoefficientMatrix z

def sourceFlatOrderedTensor : Matrix (Fin 8) (Fin 8) ℝ:=
  sourceFlatSpinCoefficient.transpose*sourceFlatLorentzMatrix*sourceFlatSpinCoefficient

theorem sourceSpinOrderedTensor_generated (z : physicalChart) :
    sourceSpinOrderedTensor z.val=(lapse^2*(sourceGaussCoframe z.val).det⁻¹) • sourceFlatOrderedTensor:=by
  let E:=sourceCoframeSlots (sourceGaussCoframe z.val)
  let Q:=sourceCoframeSlots (sourceGaussCoframe z.val)⁻¹
  have inverse : E*Q=1:=
    (sourceCoframeSlots_inverse _ (sourceGaussCoframe_nondegenerate z)).1
  have transposeInverse : Q.transpose*E.transpose=1:=by
    rw [←Matrix.transpose_mul,inverse,Matrix.transpose_one]
  rw [sourceSpinOrderedTensor,sourceSpinCoefficientMatrix_generated,sourceLorentzInverse_slots,
    Matrix.transpose_smul,Matrix.transpose_mul]
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  change _ • (sourceFlatSpinCoefficient.transpose*Q.transpose*
    (E.transpose*sourceFlatLorentzMatrix*E)*(Q*sourceFlatSpinCoefficient))=_
  have collapse : sourceFlatSpinCoefficient.transpose*Q.transpose*
      (E.transpose*sourceFlatLorentzMatrix*E)*(Q*sourceFlatSpinCoefficient)=sourceFlatOrderedTensor:=by
    simp only [Matrix.mul_assoc]
    rw [←Matrix.mul_assoc Q.transpose E.transpose,transposeInverse,Matrix.one_mul]
    rw [←Matrix.mul_assoc E Q,inverse,Matrix.one_mul]
    simp only [sourceFlatOrderedTensor,Matrix.mul_assoc]
  rw [collapse]
  congr 1
  ring

end LowEnergy.PreparationVacuumSpinGaussContraction
