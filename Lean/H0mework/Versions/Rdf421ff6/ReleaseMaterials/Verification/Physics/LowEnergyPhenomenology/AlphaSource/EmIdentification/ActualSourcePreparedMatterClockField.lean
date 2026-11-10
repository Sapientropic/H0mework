import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualPreparedMatterClockReturn
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedSchurClockField

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedMatterClockField
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedOrderedStatic
open ActualSourcePreparedClockReducedPencil ActualSourcePreparedEMClockEquation
open ActualSourcePreparedAuxiliaryClockReduction ActualSourcePreparedAuxiliaryClockRows
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedTemporalQuantumWard
open ActualPreparedMatterSupport ActualPreparedMatterClock
open scoped Matrix BigOperators
attribute [local irreducible] sourceMatterClockPencil sourceAuxiliaryReducedPencil
  sourceAuxiliaryClockFactor sourceAuxiliaryReducedFieldNumerator Matrix.det Matrix.adjugate Matrix.mulVec

def sourceMatterClockDeterminant (event : DressedEvent) (n : PhysicalMomentum) : (ℂ[X])[X] :=
  (sourceMatterClockPencil event n).det

/-- Same original 289 coordinates and source forcing, after every inactive
quantum row has supplied its common clock factor. -/
def sourceMatterClockFieldNumerator (event : DressedEvent) (n : PhysicalMomentum) : Fin 289 → (ℂ[X])[X] :=
  sourceAuxiliaryClockFactor event n • ((sourceMatterClockPencil event n).adjugate*ᵥsourceEMClockForce)

private theorem remaining_force (event : DressedEvent) (n : PhysicalMomentum) :
    Matrix.diagonal (sourceMatterRemainingRowWeight event n)*ᵥsourceEMClockForce=sourceEMClockForce := by
  funext i
  rw [Matrix.mulVec_diagonal]
  by_cases outside : (73 ≤ i.val ∧ i.val < 121) ∨ (145 ≤ i.val ∧ i.val < 217)
  · have zero := actual_em_force_inactive_zero i (by omega)
    simp only [sourceMatterRemainingRowWeight,outside,if_true,sourceEMClockForce,zero,map_zero,mul_zero]
  · simp only [sourceMatterRemainingRowWeight,outside,if_false,one_mul]

private theorem remaining_product (event : DressedEvent) (n : PhysicalMomentum) :
    (∏i : Fin 289,sourceMatterRemainingRowWeight event n i)=(sourceAuxiliaryClockFactor event n)^120 := by
  have count : (Finset.univ.filter (fun i : Fin 289 =>
      (73 ≤ i.val ∧ i.val < 121) ∨ (145 ≤ i.val ∧ i.val < 217))).card=120 := by decide
  simp only [sourceMatterRemainingRowWeight]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const,one_pow,mul_one,count]

private theorem cofactor_factor {I : Type*} [Fintype I] [DecidableEq I]
    (K M : Matrix I I ((ℂ[X])[X])) (w e : I → (ℂ[X])[X]) (a b : (ℂ[X])[X])
    (N F : I → (ℂ[X])[X]) (original : N=a • (K.adjugate*ᵥe)) (reduced : F=a • (M.adjugate*ᵥe))
    (rows : K=Matrix.diagonal w*M) (forcing : Matrix.diagonal w*ᵥe=e)
    (weight : (∏i,w i)=b) : N=b • F := by
  rw [original,reduced]
  have initial := congrArg (fun B : Matrix I I ((ℂ[X])[X]) => B*ᵥe) (Matrix.adjugate_mul (Matrix.diagonal w))
  rw [←Matrix.mulVec_mulVec,forcing,Matrix.smul_mulVec,Matrix.one_mulVec,Matrix.det_diagonal,weight] at initial
  rw [rows,Matrix.adjugate_mul_distrib,←Matrix.mulVec_mulVec,initial,Matrix.mulVec_smul]
  simp only [smul_smul]
  congr 1
  exact mul_comm a b

/-- The remaining c^120 factor is generated on the entire field cofactor
before either scale is specialized; no original Green chart is needed. -/
theorem source_matter_clock_field_factor (event : DressedEvent) (n : PhysicalMomentum) :
    sourceAuxiliaryReducedFieldNumerator event n=
      (sourceAuxiliaryClockFactor event n)^120 • sourceMatterClockFieldNumerator event n := by
  exact cofactor_factor _ _ _ _ _ _ _ _
    (by unfold sourceAuxiliaryReducedFieldNumerator; rfl)
    (by unfold sourceMatterClockFieldNumerator; rfl) (source_matter_auxiliary_row_factor event n)
    (remaining_force event n) (remaining_product event n)

private theorem map_field {I : Type*} [Fintype I] [DecidableEq I]
    (f : ((ℂ[X])[X]) →+* ℂ) (a : (ℂ[X])[X]) (P : Matrix I I ((ℂ[X])[X]))
    (E : I → (ℂ[X])[X]) : f ∘ (a • (P.adjugate*ᵥE))=f a • ((P.map f).adjugate*ᵥ(f ∘ E)) := by
  funext i
  change f (a*(P.adjugate*ᵥE) i)=_
  rw [map_mul,f.map_mulVec]
  have adj := f.map_adjugate P
  simp only [RingHom.mapMatrix_apply] at adj
  rw [adj]
  rfl

private theorem force_eval (eps sigma : ℝ) :
    sourceClockEval eps sigma ∘ sourceEMClockForce=sourceTemporalEMForce := by
  funext i
  simp only [Function.comp_apply,sourceEMClockForce,sourceClockEval,RingHom.comp_apply,clockSpecialize,
    Polynomial.coe_mapRingHom,Polynomial.map_C,Polynomial.coe_evalRingHom,Polynomial.eval_C]

private theorem actual_weighted_force (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) :
    Matrix.diagonal (sourceMatterClockForcingWeight event n eps sigma)*ᵥsourceTemporalEMForce=
      sourceClockEval eps sigma (sourceAuxiliaryClockFactor event n) • sourceTemporalEMForce := by
  funext i
  rw [Matrix.mulVec_diagonal]
  by_cases outside : (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val
  · have zero := actual_em_force_inactive_zero i outside
    simp only [sourceMatterClockForcingWeight,outside,if_true,zero,mul_zero,Pi.smul_apply,smul_eq_mul]
  · simp only [sourceMatterClockForcingWeight,outside,if_false,Pi.smul_apply,smul_eq_mul]

theorem source_matter_clock_determinant_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) :
    sourceClockEval eps sigma (sourceMatterClockDeterminant event n)=
      sourceMatterClockActualDeterminant event n eps sigma := by
  unfold sourceMatterClockDeterminant sourceMatterClockActualDeterminant
  simpa only [RingHom.mapMatrix_apply] using (sourceClockEval eps sigma).map_det (sourceMatterClockPencil event n)

theorem source_matter_clock_field_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) :
    sourceClockEval eps sigma ∘ sourceMatterClockFieldNumerator event n=
      sourceMatterClockActualFieldNumerator event n eps sigma := by
  unfold sourceMatterClockFieldNumerator
  rw [map_field,force_eval]
  unfold sourceMatterClockActualFieldNumerator
  rw [←Matrix.mulVec_mulVec,actual_weighted_force,Matrix.mulVec_smul]

/-- The same actual prepared field consumes the new source numerator on its
unchanged original chart; every native Dirac and BF coordinate survives. -/
theorem source_matter_clock_field_fraction (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ)
    (positive : 0<sigma) (regular : correctedDet event eps 0 sigma n≠0) (i : Fin 289) :
    sourceTemporalCorrectedField event eps sigma n i=
      sourceClockEval eps sigma (sourceMatterClockFieldNumerator event n i)/
        sourceClockEval eps sigma (sourceMatterClockDeterminant event n) := by
  rw [source_matter_clock_determinant_eval]
  have numerator := congrFun (source_matter_clock_field_eval event n eps sigma) i
  change sourceClockEval eps sigma (sourceMatterClockFieldNumerator event n i)=
    sourceMatterClockActualFieldNumerator event n eps sigma i at numerator
  rw [numerator]
  apply (eq_div_iff (source_matter_actual_determinant_nonzero event n eps sigma positive regular)).mpr
  have field := congrFun (source_matter_actual_field_clear event n eps sigma positive regular) i
  change sourceMatterClockActualDeterminant event n eps sigma*
    sourceTemporalCorrectedField event eps sigma n i=_ at field
  exact (mul_comm _ _).trans field

end LowEnergy.GaussComposite.ActualSourcePreparedMatterClockField
