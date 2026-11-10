import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedAuxiliaryClockSchur
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualPreparedMatterSupportNative

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedAuxiliarySchurActualReturn
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic SourcePropagationNativeActionHessian
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedEMTensorClock ActualEMAction
open ActualDressedUniformMaterialCoefficients ActualDressedOrderedStatic ActualDressedZeroDamping
open ActualDressedEMNativeAuxiliary ActualDressedEMAuxiliaryFeedback ActualPreparedMatterSupport
open ActualSourcePreparedClockReducedPencil ActualSourcePreparedFourClockCarrier
open ActualSourcePreparedAuxiliaryClockReduction ActualSourcePreparedAuxiliaryActualReturn
open ActualSourcePreparedAuxiliaryClockSchur ActualSourcePreparedEMClockEquation
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedTemporalQuantumWard
open scoped Matrix BigOperators
attribute [local irreducible] sourceClockReducedPencil sourceAuxiliaryReducedPencil
  sourceAuxiliaryRowWeight sourceAuxiliaryClockBlock sourceAuxiliaryClockInverse
  sourceAuxiliaryClockSchurPencil sourceTemporalCorrectedField Matrix.det Matrix.mulVec

private def wholeIndex : Fin 217 ⊕ (Fin 6 × Fin 12) ≃ Fin 289 :=
  (Equiv.sumCongr (Equiv.refl (Fin 217)) finProdFinEquiv).trans finSumFinEquiv

private theorem whole_left (i : Fin 217) : wholeIndex (Sum.inl i)=nativeRestIndex i := rfl

private theorem whole_right (i : Fin 6 × Fin 12) : wholeIndex (Sum.inr i)=gaugeAuxiliaryIndex i := by
  apply Fin.ext
  change 217+(i.2.val+12*i.1.val)=217+12*i.1.val+i.2.val
  omega

private theorem clock_factor_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) :
    sourceClockEval eps sigma (sourceAuxiliaryClockFactor event n)=
      (sigma : ℂ)^3*sourceClockEval eps sigma (sourceFourClockDenominator event n) := by
  have clock : sourceClockEval eps sigma (X : (ℂ[X])[X])=(sigma : ℂ) := by
    simp only [sourceClockEval,RingHom.comp_apply,clockSpecialize,Polynomial.coe_mapRingHom,
      Polynomial.map_X,Polynomial.coe_evalRingHom,Polynomial.eval_X]
  simp only [sourceAuxiliaryClockFactor,map_mul,map_pow,clock]

private theorem weight_value (event : DressedEvent) (n : PhysicalMomentum)
    (r : Fin 217 ⊕ (Fin 6 × Fin 12)) :
    sourceAuxiliaryRowWeight event n (wholeIndex r)=
      Sum.elim (fun _ : Fin 217 => 1) (fun _ : Fin 6 × Fin 12 => sourceAuxiliaryClockFactor event n) r := by
  unfold sourceAuxiliaryRowWeight
  change Sum.elim (fun _ : Fin 217 => 1) (fun _ : Fin 6 × Fin 12 => sourceAuxiliaryClockFactor event n)
    (wholeIndex.symm (wholeIndex r))=_
  rw [Equiv.symm_apply_apply]

private theorem weight_nonzero (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ)
    (positive : 0<sigma) (i : Fin 289) :
    sourceClockEval eps sigma (sourceAuxiliaryRowWeight event n i)≠0 := by
  obtain ⟨r,rfl⟩ := wholeIndex.surjective i
  cases r with
  | inl r =>
      rw [weight_value]
      change (sourceClockEval eps sigma) 1≠0
      rw [map_one]
      norm_num
  | inr r =>
      simp only [weight_value,Sum.elim_inr]
      rw [clock_factor_eval]
      exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr positive.ne'))
        (ActualSourcePreparedReducedQuantumCofactor.source_reduced_clock_denominator_nonzero event n eps sigma positive)

private theorem auxiliary_force_zero (i : Fin 6 × Fin 12) :
    sourceTemporalEMForce (gaugeAuxiliaryIndex i)=0 := by
  apply actual_em_force_inactive_zero
  right
  dsimp only [gaugeAuxiliaryIndex,gaugeBSlot]
  omega

private theorem weighted_force (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) :
    Matrix.diagonal (sourceClockEval eps sigma ∘ sourceAuxiliaryRowWeight event n)*ᵥ
      sourceTemporalEMForce=sourceTemporalEMForce := by
  funext i
  rw [Matrix.mulVec_diagonal]
  obtain ⟨r,rfl⟩ := wholeIndex.surjective i
  cases r with
  | inl r => simp only [Function.comp_apply,weight_value,Sum.elim_inl,map_one,one_mul]
  | inr r =>
      simp only [Function.comp_apply,weight_value,Sum.elim_inr]
      rw [whole_right,auxiliary_force_zero,mul_zero]

private theorem unweight_field {I : Type*} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) (w v E : I → ℂ) (a : ℂ)
    (nonzero : ∀i,w i≠0) (force : Matrix.diagonal w*ᵥE=E)
    (field : (Matrix.diagonal w*P)*ᵥv=a • E) : P*ᵥv=a • E := by
  rw [←Matrix.mulVec_mulVec] at field
  have rhs : Matrix.diagonal w*ᵥ(a • E)=a • E := by rw [Matrix.mulVec_smul,force]
  funext i
  apply mul_left_cancel₀ (nonzero i)
  have entry := congrFun field i
  have right := congrFun rhs i
  rw [Matrix.mulVec_diagonal] at entry right
  exact entry.trans right.symm

/-- The same actual GE0 consumes the unweighted full pencil, with its original
forcing, physical clock and Green regularity. -/
theorem source_auxiliary_actual_pencil_field (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (positive : 0<sigma) (regular : correctedDet event eps 0 sigma n≠0) :
    (sourceAuxiliaryReducedPencil event n).map (sourceClockEval eps sigma)*ᵥ
      sourceTemporalCorrectedField event eps sigma n=
      sourceClockEval eps sigma (sourceAuxiliaryClockFactor event n) • sourceTemporalEMForce := by
  have original := source_clock_reduced_actual_field event n eps sigma positive regular
  have mapped := congrArg (fun P : Matrix (Fin 289) (Fin 289) ((ℂ[X])[X]) =>
    P.map (sourceClockEval eps sigma)) (source_auxiliary_pencil_row_factor event n)
  rw [Matrix.map_mul,Matrix.diagonal_map (sourceClockEval eps sigma).map_zero] at mapped
  rw [mapped,←clock_factor_eval] at original
  exact unweight_field _ _ _ _ _ (weight_nonzero event n eps sigma positive)
    (weighted_force event n eps sigma) original

private theorem blocks_reindex {M A I : Type*} [Fintype M] [Fintype A]
    (e : M ⊕ A ≃ I) (P : Matrix I I ℂ) :
    P.submatrix e e=Matrix.fromBlocks
      (P.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl))
      (P.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr))
      (P.submatrix (e ∘ Sum.inr) (e ∘ Sum.inl))
      (P.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)) := by
  ext (i|i) (j|j) <;> rfl

private theorem block_field {M A I : Type*} [Fintype M] [Fintype A] [Fintype I]
    [DecidableEq A] (e : M ⊕ A ≃ I) (P : Matrix I I ℂ)
    (H : Matrix A A ℂ) (v E : I → ℂ) (a : ℂ)
    (inverse : H*P.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)=1)
    (zero : E ∘ e ∘ Sum.inr=0) (field : P*ᵥv=a • E) :
    v ∘ e ∘ Sum.inr= -(H*ᵥ(P.submatrix (e ∘ Sum.inr) (e ∘ Sum.inl)*ᵥ(v ∘ e ∘ Sum.inl))) ∧
    (P.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)-
      P.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr)*H*
        P.submatrix (e ∘ Sum.inr) (e ∘ Sum.inl))*ᵥ(v ∘ e ∘ Sum.inl)=
      a • (E ∘ e ∘ Sum.inl) := by
  have reindexed : P.submatrix e e*ᵥ(v ∘ e)=(P*ᵥv) ∘ e := by
    rw [Matrix.submatrix_mulVec_equiv]
    have same : (v ∘ e) ∘ e.symm=v := by funext i; simp only [Function.comp_apply,Equiv.apply_symm_apply]
    rw [same]
  rw [blocks_reindex,Matrix.fromBlocks_mulVec,field] at reindexed
  have aux := congrArg (fun z : M ⊕ A → ℂ => z ∘ Sum.inr) reindexed
  have rest := congrArg (fun z : M ⊕ A → ℂ => z ∘ Sum.inl) reindexed
  simp only [Function.comp_def,Sum.elim_inr,Pi.smul_apply,smul_eq_mul] at aux
  simp only [Function.comp_def,Sum.elim_inl,Pi.smul_apply,smul_eq_mul] at rest
  have right_zero : (fun x => a*E (e (Sum.inr x)))=0 := by
    funext i
    have point := congrFun zero i
    change E (e (Sum.inr i))=0 at point
    simp only [point,Pi.zero_apply,mul_zero]
  rw [right_zero] at aux
  have forced : P.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)*ᵥ(v ∘ e ∘ Sum.inr)=
      -(P.submatrix (e ∘ Sum.inr) (e ∘ Sum.inl)*ᵥ(v ∘ e ∘ Sum.inl)) :=
    eq_neg_of_add_eq_zero_right aux
  have solved := congrArg (fun z => H*ᵥz) forced
  rw [Matrix.mulVec_mulVec,inverse,Matrix.one_mulVec,Matrix.mulVec_neg] at solved
  constructor
  · exact solved
  · change P.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)*ᵥ(v ∘ e ∘ Sum.inl)+
      P.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr)*ᵥ(v ∘ e ∘ Sum.inr)=
        a • (E ∘ e ∘ Sum.inl) at rest
    rw [solved,Matrix.mulVec_neg] at rest
    rw [Matrix.sub_mulVec,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]
    simpa only [sub_eq_add_neg] using rest

private theorem clock_blocks (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) :
    ((sourceAuxiliaryReducedPencil event n).map (sourceClockEval eps sigma)).submatrix
      (wholeIndex ∘ Sum.inr) (wholeIndex ∘ Sum.inr)=
      (sourceAuxiliaryClockBlock event n).map (sourceClockEval eps sigma) := by
  ext i j
  simp only [Matrix.submatrix_apply,Matrix.map_apply,Function.comp_apply,whole_right,sourceAuxiliaryClockBlock]

private theorem mapped_inverse {I : Type*} [Fintype I] [DecidableEq I]
    (f : ((ℂ[X])[X]) →+* ℂ) (H F : Matrix I I ((ℂ[X])[X])) (inverse : H*F=1) :
    H.map f*F.map f=1 := by
  rw [←Matrix.map_mul,inverse]
  exact Matrix.map_one f f.map_zero f.map_one

/-- The original 72 auxiliary fields are reconstructed, not set to zero. -/
theorem source_auxiliary_actual_field_reconstruction (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (positive : 0<sigma) (regular : correctedDet event eps 0 sigma n≠0) :
    emAuxiliarySlice (sourceTemporalCorrectedField event eps sigma n)=
      -((sourceAuxiliaryClockInverse.map (sourceClockEval eps sigma))*ᵥ
        (((sourceAuxiliaryReducedPencil event n).submatrix gaugeAuxiliaryIndex nativeRestIndex).map
          (sourceClockEval eps sigma)*ᵥemRestSlice (sourceTemporalCorrectedField event eps sigma n))) := by
  have inverse : sourceAuxiliaryClockInverse.map (sourceClockEval eps sigma)*
      ((sourceAuxiliaryReducedPencil event n).map (sourceClockEval eps sigma)).submatrix
        (wholeIndex ∘ Sum.inr) (wholeIndex ∘ Sum.inr)=1 := by
    rw [clock_blocks]
    exact mapped_inverse _ _ _ (source_auxiliary_clock_block_inverse event n).1
  have zero : sourceTemporalEMForce ∘ wholeIndex ∘ Sum.inr=0 := by
    funext i
    simp only [Function.comp_apply,whole_right,auxiliary_force_zero,Pi.zero_apply]
  have generated := (block_field wholeIndex
    ((sourceAuxiliaryReducedPencil event n).map (sourceClockEval eps sigma))
    (sourceAuxiliaryClockInverse.map (sourceClockEval eps sigma))
    (sourceTemporalCorrectedField event eps sigma n) sourceTemporalEMForce
    (sourceClockEval eps sigma (sourceAuxiliaryClockFactor event n)) inverse zero
    (source_auxiliary_actual_pencil_field event n eps sigma positive regular)).1
  change (fun i => sourceTemporalCorrectedField event eps sigma n (gaugeAuxiliaryIndex i))=
    -((sourceAuxiliaryClockInverse.map (sourceClockEval eps sigma))*ᵥ
      (((sourceAuxiliaryReducedPencil event n).submatrix gaugeAuxiliaryIndex nativeRestIndex).map
        (sourceClockEval eps sigma)*ᵥ(fun i => sourceTemporalCorrectedField event eps sigma n (nativeRestIndex i))))
  simpa only [Function.comp_def,whole_left,whole_right,Matrix.submatrix_map] using generated

private theorem schur_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) :
    (sourceAuxiliaryClockSchurPencil event n).map (sourceClockEval eps sigma)=
      ((sourceAuxiliaryReducedPencil event n).submatrix nativeRestIndex nativeRestIndex).map (sourceClockEval eps sigma)-
      ((sourceAuxiliaryReducedPencil event n).submatrix nativeRestIndex gaugeAuxiliaryIndex).map (sourceClockEval eps sigma)*
        sourceAuxiliaryClockInverse.map (sourceClockEval eps sigma)*
        ((sourceAuxiliaryReducedPencil event n).submatrix gaugeAuxiliaryIndex nativeRestIndex).map (sourceClockEval eps sigma) := by
  unfold sourceAuxiliaryClockSchurPencil
  change (((sourceAuxiliaryReducedPencil event n).submatrix nativeRestIndex nativeRestIndex-
    (sourceAuxiliaryReducedPencil event n).submatrix nativeRestIndex gaugeAuxiliaryIndex*
      sourceAuxiliaryClockInverse*
      (sourceAuxiliaryReducedPencil event n).submatrix gaugeAuxiliaryIndex nativeRestIndex).map (sourceClockEval eps sigma))=_
  rw [Matrix.map_sub,Matrix.map_mul,Matrix.map_mul]
  exact (sourceClockEval eps sigma).map_sub

/-- Schur217 acts on the restriction of the same actual full field. All
prepared cross-column feedback survives its algebraic auxiliary elimination. -/
theorem source_auxiliary_actual_schur_field (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (positive : 0<sigma) (regular : correctedDet event eps 0 sigma n≠0) :
    (sourceAuxiliaryClockSchurPencil event n).map (sourceClockEval eps sigma)*ᵥ
      emRestSlice (sourceTemporalCorrectedField event eps sigma n)=
      sourceClockEval eps sigma (sourceAuxiliaryClockFactor event n) • emRestSlice sourceTemporalEMForce := by
  have inverse : sourceAuxiliaryClockInverse.map (sourceClockEval eps sigma)*
      ((sourceAuxiliaryReducedPencil event n).map (sourceClockEval eps sigma)).submatrix
        (wholeIndex ∘ Sum.inr) (wholeIndex ∘ Sum.inr)=1 := by
    rw [clock_blocks]
    exact mapped_inverse _ _ _ (source_auxiliary_clock_block_inverse event n).1
  have zero : sourceTemporalEMForce ∘ wholeIndex ∘ Sum.inr=0 := by
    funext i
    simp only [Function.comp_apply,whole_right,auxiliary_force_zero,Pi.zero_apply]
  have generated := (block_field wholeIndex
    ((sourceAuxiliaryReducedPencil event n).map (sourceClockEval eps sigma))
    (sourceAuxiliaryClockInverse.map (sourceClockEval eps sigma))
    (sourceTemporalCorrectedField event eps sigma n) sourceTemporalEMForce
    (sourceClockEval eps sigma (sourceAuxiliaryClockFactor event n)) inverse zero
    (source_auxiliary_actual_pencil_field event n eps sigma positive regular)).2
  rw [schur_eval]
  change (_*ᵥ(fun i => sourceTemporalCorrectedField event eps sigma n (nativeRestIndex i)))=
    sourceClockEval eps sigma (sourceAuxiliaryClockFactor event n) • (fun i => sourceTemporalEMForce (nativeRestIndex i))
  simpa only [Function.comp_def,whole_left,whole_right,Matrix.submatrix_map] using generated

private theorem mapped_det_product {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (f : ((ℂ[X])[X]) →+* ℂ)
    (P : Matrix I I ((ℂ[X])[X])) (F : Matrix J J ((ℂ[X])[X]))
    (S : Matrix (Fin 217) (Fin 217) ((ℂ[X])[X]))
    (factor : P.det=F.det*S.det) : (P.map f).det=(F.map f).det*(S.map f).det := by
  have mappedP : f P.det=(P.map f).det := by simpa only [RingHom.mapMatrix_apply] using f.map_det P
  have mappedF : f F.det=(F.map f).det := by simpa only [RingHom.mapMatrix_apply] using f.map_det F
  have mappedS : f S.det=(S.map f).det := by simpa only [RingHom.mapMatrix_apply] using f.map_det S
  rw [←mappedP,factor,map_mul,mappedF,mappedS]

/-- Schur regularity is inherited from the original full Green chart. The
algebraic auxiliary inverse alone never supplies this nonzero condition. -/
theorem source_auxiliary_actual_schur_regular (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (positive : 0<sigma) (regular : correctedDet event eps 0 sigma n≠0) :
    ((sourceAuxiliaryClockSchurPencil event n).map (sourceClockEval eps sigma)).det≠0 := by
  have inherited := source_auxiliary_actual_determinant_nonzero event n eps sigma positive regular
  change ((sourceAuxiliaryReducedPencil event n).map (sourceClockEval eps sigma)).det≠0 at inherited
  have factor := mapped_det_product (sourceClockEval eps sigma)
    (sourceAuxiliaryReducedPencil event n) (sourceAuxiliaryClockBlock event n)
    (sourceAuxiliaryClockSchurPencil event n) (source_auxiliary_clock_schur_determinant event n)
  rw [factor] at inherited
  exact (mul_ne_zero_iff.mp inherited).2

private theorem cofactor_field {I : Type*} [Fintype I] [DecidableEq I]
    (S : Matrix I I ℂ) (v E : I → ℂ) (a : ℂ) (field : S*ᵥv=a • E) :
    S.det • v=a • (S.adjugate*ᵥE) := by
  have adj := congrArg (fun P : Matrix I I ℂ => P*ᵥv) (Matrix.adjugate_mul S)
  rw [←Matrix.mulVec_mulVec,field,Matrix.mulVec_smul,Matrix.smul_mulVec,Matrix.one_mulVec] at adj
  exact adj.symm

/-- The actual 217-field restriction has a source cofactor and the same
original forcing/clock. It supplies a direct finite numerical read mouth. -/
theorem source_auxiliary_actual_schur_cofactor (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (positive : 0<sigma) (regular : correctedDet event eps 0 sigma n≠0) :
    ((sourceAuxiliaryClockSchurPencil event n).map (sourceClockEval eps sigma)).det •
      emRestSlice (sourceTemporalCorrectedField event eps sigma n)=
      sourceClockEval eps sigma (sourceAuxiliaryClockFactor event n) •
        (((sourceAuxiliaryClockSchurPencil event n).map (sourceClockEval eps sigma)).adjugate*ᵥ
          emRestSlice sourceTemporalEMForce) := by
  exact cofactor_field _ _ _ _ (source_auxiliary_actual_schur_field event n eps sigma positive regular)

end LowEnergy.GaussComposite.ActualSourcePreparedAuxiliarySchurActualReturn
