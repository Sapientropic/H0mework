import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedAuxiliarySchurBalance

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedSchurClockField
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedEMNativeAuxiliary ActualSourcePreparedEMClockEquation
open ActualSourcePreparedClockReducedPencil ActualSourcePreparedAuxiliaryClockReduction
open ActualSourcePreparedAuxiliaryClockSchur ActualSourcePreparedAuxiliarySchurBalance
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedTemporalQuantumWard
open scoped Matrix BigOperators
attribute [local irreducible] sourceAuxiliaryClockSchurPencil sourceAuxiliaryReducedPencil
  sourceAuxiliaryClockInverse Matrix.det Matrix.adjugate Matrix.mulVec

private def wholeIndex : Fin 217 ⊕ (Fin 6 × Fin 12) ≃ Fin 289 :=
  (Equiv.sumCongr (Equiv.refl (Fin 217)) finProdFinEquiv).trans finSumFinEquiv

def sourceSchurClockDeterminant (event : DressedEvent) (n : PhysicalMomentum) : (ℂ[X])[X] :=
  (sourceAuxiliaryClockSchurPencil event n).det

def sourceSchurClockRestNumerator (event : DressedEvent) (n : PhysicalMomentum) : Fin 217 → (ℂ[X])[X] :=
  sourceAuxiliaryClockFactor event n •
    ((sourceAuxiliaryClockSchurPencil event n).adjugate*ᵥ(sourceEMClockForce ∘ nativeRestIndex))

/-- The full field cofactor is generated before either physical coordinate is
specialized. It retains the same auxiliary reconstruction and all289 slots. -/
def sourceSchurClockFullFieldNumerator (event : DressedEvent) (n : PhysicalMomentum) : Fin 289 → (ℂ[X])[X] :=
  Sum.elim (sourceSchurClockRestNumerator event n)
    (-(sourceAuxiliaryClockInverse*ᵥ((sourceAuxiliaryReducedPencil event n).submatrix
      gaugeAuxiliaryIndex nativeRestIndex*ᵥsourceSchurClockRestNumerator event n))) ∘ wholeIndex.symm

private theorem map_cofactor {I : Type*} [Fintype I] [DecidableEq I]
    (f : ((ℂ[X])[X]) →+* ℂ) (a : (ℂ[X])[X])
    (P : Matrix I I ((ℂ[X])[X])) (E : I → (ℂ[X])[X]) :
    f ∘ (a • (P.adjugate*ᵥE))=f a • ((P.map f).adjugate*ᵥ(f ∘ E)) := by
  funext i
  change f (a*(P.adjugate*ᵥE) i)=_
  rw [map_mul,f.map_mulVec]
  have adj := f.map_adjugate P
  simp only [RingHom.mapMatrix_apply] at adj
  rw [adj]
  rfl

private theorem clock_force_eval (eps sigma : ℝ) :
    sourceClockEval eps sigma ∘ sourceEMClockForce=sourceTemporalEMForce := by
  funext i
  simp only [Function.comp_apply,sourceEMClockForce,sourceClockEval,RingHom.comp_apply,
    ActualDressedOrderedStatic.clockSpecialize,Polynomial.coe_mapRingHom,Polynomial.map_C,
    Polynomial.coe_evalRingHom,Polynomial.eval_C]

theorem source_schur_clock_determinant_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) :
    sourceClockEval eps sigma (sourceSchurClockDeterminant event n)=sourceSchurDeterminant event n eps sigma := by
  unfold sourceSchurClockDeterminant sourceSchurDeterminant
  simpa only [RingHom.mapMatrix_apply] using (sourceClockEval eps sigma).map_det (sourceAuxiliaryClockSchurPencil event n)

theorem source_schur_clock_rest_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) :
    sourceClockEval eps sigma ∘ sourceSchurClockRestNumerator event n=sourceSchurRestNumerator event n eps sigma := by
  unfold sourceSchurClockRestNumerator sourceSchurRestNumerator
  have force : sourceClockEval eps sigma ∘ (sourceEMClockForce ∘ nativeRestIndex)=emRestSlice sourceTemporalEMForce := by
    rw [←Function.comp_assoc,clock_force_eval]
    rfl
  rw [←force]
  exact map_cofactor _ _ _ _

private theorem map_restored {M A I : Type*} [Fintype M] [Fintype A]
    (f : ((ℂ[X])[X]) →+* ℂ) (e : M ⊕ A ≃ I) (r : M → (ℂ[X])[X])
    (H : Matrix A A ((ℂ[X])[X])) (D : Matrix A M ((ℂ[X])[X])) :
    f ∘ (Sum.elim r (-(H*ᵥ(D*ᵥr))) ∘ e.symm)=
      Sum.elim (f ∘ r) (-(H.map f*ᵥ(D.map f*ᵥ(f ∘ r)))) ∘ e.symm := by
  have mapped (P : Matrix A M ((ℂ[X])[X])) (v : M → (ℂ[X])[X]) :
      f ∘ (P*ᵥv)=P.map f*ᵥ(f ∘ v) := by funext i;exact f.map_mulVec P v i
  have outer : f ∘ (H*ᵥ(D*ᵥr))=H.map f*ᵥ(D.map f*ᵥ(f ∘ r)) := by
    funext i
    rw [Function.comp_apply,f.map_mulVec,mapped]
  funext i
  obtain ⟨x,rfl⟩ := e.surjective i
  cases x with
  | inl x => simp only [Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl]
  | inr x =>
      simp only [Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr,Pi.neg_apply,map_neg]
      exact congrArg Neg.neg (congrFun outer x)

theorem source_schur_clock_full_field_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) :
    sourceClockEval eps sigma ∘ sourceSchurClockFullFieldNumerator event n=sourceSchurFullFieldNumerator event n eps sigma := by
  unfold sourceSchurClockFullFieldNumerator sourceSchurFullFieldNumerator
  rw [map_restored,source_schur_clock_rest_eval]
  rfl

/-- The complete source bivariate quotient is consumed by the original actual
field on its unchanged chart, giving the next IR coefficient/remainder mouth. -/
theorem source_schur_clock_full_field_fraction (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (positive : 0<sigma) (regular : correctedDet event eps 0 sigma n≠0) (i : Fin 289) :
    sourceTemporalCorrectedField event eps sigma n i=
      sourceClockEval eps sigma (sourceSchurClockFullFieldNumerator event n i)/
        sourceClockEval eps sigma (sourceSchurClockDeterminant event n) := by
  rw [source_schur_clock_determinant_eval]
  have numerator := congrFun (source_schur_clock_full_field_eval event n eps sigma) i
  change sourceClockEval eps sigma (sourceSchurClockFullFieldNumerator event n i)=sourceSchurFullFieldNumerator event n eps sigma i at numerator
  rw [numerator]
  exact source_schur_full_field_fraction event n eps sigma positive regular i

end LowEnergy.GaussComposite.ActualSourcePreparedSchurClockField
