import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedMatterClockBalance

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedMatterClockPrincipal
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic PreparationVacuumOriginalGreenFeedback
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedOrderedStatic
open ActualDressedUniformMaterialCoefficients ActualDressedZeroDamping
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open ActualEMAction ActualEMCarrierOwn SourcePropagationNativeActionHessian
open ActualDressedEMNativeAuxiliary ActualDressedEMCorrectedCouplingSource
open ActualSourcePreparedClockReducedPencil ActualSourcePreparedEMClockEquation
open ActualSourcePreparedAuxiliaryClockReduction ActualSourcePreparedAuxiliaryClockRows ActualSourcePreparedTemporalEMConstraint
open ActualSourcePreparedMatterClockField ActualSourcePreparedMatterClockBalance
open ActualPreparedMatterSupport ActualPreparedMatterClock
open ActualSourcePreparedEMNativeRow ActualSourcePreparedEMNativeRead
open scoped Matrix BigOperators
attribute [local irreducible] sourceMatterClockPencil sourceMatterClockFieldNumerator
  sourceMatterClockDeterminant sourceAuxiliaryClockFactor sourceEMClockForce
  commonJacobi emOriginalJacobi Matrix.det Matrix.adjugate Matrix.mulVec

private theorem cofactor_equation {I : Type*} [Fintype I] [DecidableEq I]
    (P : Matrix I I ((ℂ[X])[X])) (a d : (ℂ[X])[X]) (E N : I → (ℂ[X])[X])
    (numerator : N=a • (P.adjugate*ᵥE)) (denominator : d=P.det) :
    P*ᵥN=(a*d) • E := by
  rw [numerator,denominator,Matrix.mulVec_smul,Matrix.mulVec_mulVec,
    Matrix.mul_adjugate,Matrix.smul_mulVec,Matrix.one_mulVec,smul_smul]

/-- Every original field coordinate satisfies the same source cofactor
equation before either scale is specialized, including singular points. -/
theorem source_matter_clock_field_equation (event : DressedEvent) (n : PhysicalMomentum) :
    sourceMatterClockPencil event n*ᵥsourceMatterClockFieldNumerator event n=
      (sourceAuxiliaryClockFactor event n*sourceMatterClockDeterminant event n) • sourceEMClockForce := by
  exact cofactor_equation _ _ _ _ _
    (by unfold sourceMatterClockFieldNumerator; rfl)
    (by unfold sourceMatterClockDeterminant; rfl)


private theorem force_eval (eps sigma : ℝ) :
    sourceClockEval eps sigma ∘ sourceEMClockForce=sourceTemporalEMForce := by
  funext i
  simp only [Function.comp_apply,sourceEMClockForce,sourceClockEval,RingHom.comp_apply,
    clockSpecialize,Polynomial.coe_mapRingHom,Polynomial.map_C,
    Polynomial.coe_evalRingHom,Polynomial.eval_C]

private theorem map_equation {I : Type*} [Fintype I]
    (f : ((ℂ[X])[X]) →+* ℂ) (P : Matrix I I ((ℂ[X])[X]))
    (N E : I → (ℂ[X])[X]) (a : (ℂ[X])[X]) (equation : P*ᵥN=a • E) :
    P.map f*ᵥ(f ∘ N)=f a • (f ∘ E) := by
  funext i
  have point := congrArg f (congrFun equation i)
  change f ((P*ᵥN) i)=f (a*E i) at point
  rw [f.map_mulVec,map_mul] at point
  exact point

private theorem field_equation_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) :
    (sourceMatterClockPencil event n).map (sourceClockEval eps sigma)*ᵥ
      sourceMatterClockActualFieldNumerator event n eps sigma=
      sourceClockEval eps sigma (sourceAuxiliaryClockFactor event n*sourceMatterClockDeterminant event n) •
        sourceTemporalEMForce := by
  have mapped := map_equation (sourceClockEval eps sigma) _ _ _ _
    (source_matter_clock_field_equation event n)
  rw [source_matter_clock_field_eval,force_eval] at mapped
  exact mapped


private theorem auxiliary_row (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ)
    (i : Fin 6 × Fin 12) (j : Fin 289) :
    (sourceMatterClockPencil event n).map (sourceClockEval eps sigma) (gaugeAuxiliaryIndex i) j=
      emOriginalJacobi (frequencyRay eps 0 n) (gaugeAuxiliaryIndex i) j := by
  have outside : (73 ≤ (gaugeAuxiliaryIndex i).val ∧ (gaugeAuxiliaryIndex i).val < 121) ∨
      145 ≤ (gaugeAuxiliaryIndex i).val := by
    change (73 ≤ 217+12*i.1.val+i.2.val ∧ 217+12*i.1.val+i.2.val < 121) ∨
      145 ≤ 217+12*i.1.val+i.2.val
    omega
  simp only [Matrix.map_apply,sourceMatterClockPencil,if_pos outside]
  have source := congrFun (congrFun (common_jacobi_eval n eps sigma 0) (gaugeAuxiliaryIndex i)) j
  change MvPolynomial.eval (irValues eps sigma 0) (commonJacobi n (gaugeAuxiliaryIndex i) j)=_ at source
  change (clockSpecialize eps (staticIRClockSlice (commonJacobi n (gaugeAuxiliaryIndex i) j))).eval (sigma : ℂ)=_
  rw [ir_clock_specialize,damping_slice_eval]
  exact source


/-- The literal inactive auxiliary rows generate zero original Jacobi force
on the full cofactor. No inverse chart or limiting return is a premise. -/
theorem source_matter_clock_field_auxiliary_native (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) :
    emAuxiliarySlice (emOriginalJacobi (frequencyRay eps 0 n)*ᵥ
      sourceMatterClockActualFieldNumerator event n eps sigma)=0 := by
  funext i
  change (emOriginalJacobi (frequencyRay eps 0 n)*ᵥsourceMatterClockActualFieldNumerator event n eps sigma) (gaugeAuxiliaryIndex i)=0
  have point := congrFun (field_equation_eval event n eps sigma) (gaugeAuxiliaryIndex i)
  have outside : (73 ≤ (gaugeAuxiliaryIndex i).val ∧ (gaugeAuxiliaryIndex i).val < 121) ∨
      145 ≤ (gaugeAuxiliaryIndex i).val := by
    change (73 ≤ 217+12*i.1.val+i.2.val ∧ 217+12*i.1.val+i.2.val < 121) ∨
      145 ≤ 217+12*i.1.val+i.2.val
    omega
  have force := actual_em_force_inactive_zero (gaugeAuxiliaryIndex i) outside
  simpa only [Matrix.mulVec,dotProduct,auxiliary_row,Pi.smul_apply,smul_eq_mul,
    force,mul_zero] using point

private theorem lapse_coefficient : (3/25:ℂ)*rootTwo*rootFifteen=(lapse:ℂ) := by
  have two : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have fifteen : (Real.sqrt 15)^2=15 := Real.sq_sqrt (by norm_num)
  have positive : 0≤(3/25:ℝ)*Real.sqrt 2*Real.sqrt 15 := by positivity
  have equal : (3/25:ℝ)*Real.sqrt 2*Real.sqrt 15=lapse := by
    nlinarith [lapse_sq,lapse_pos,mul_self_nonneg ((3/25:ℝ)*Real.sqrt 2*Real.sqrt 15-lapse)]
  unfold rootTwo rootFifteen
  have h := congrArg (fun x : ℝ => (x:ℂ)) equal
  push_cast at h
  exact h

@[local simp] private theorem momentum_one (spatial : Fin 3 → ℂ) (z : ℂ) :
    Fin.cases z spatial (1 : Fin 4)=spatial 0 := rfl
@[local simp] private theorem momentum_two (spatial : Fin 3 → ℂ) (z : ℂ) :
    Fin.cases z spatial (2 : Fin 4)=spatial 1 := rfl
@[local simp] private theorem momentum_three (spatial : Fin 3 → ℂ) (z : ℂ) :
    Fin.cases z spatial (3 : Fin 4)=spatial 2 := rfl

private theorem force_observation (v : Fin 289 → ℂ) :
    dotProduct sourceTemporalEMForce v=(emInsertion.transpose*ᵥv) 0 := by
  unfold sourceTemporalEMForce Matrix.mulVec dotProduct
  rfl

/-- The nine source Hessian coefficients contract to the temporal EM
principal in the unchanged physical coordinates and original action units. -/
theorem source_em_native_principal_read (eps : ℝ) (n : PhysicalMomentum) (v : Fin 289 → ℂ) :
    (sourceMatrix sourceEMNativePrincipalTerms (frequencyRay eps 0 n)*ᵥv) 0=
      2*(lapse:ℂ)*(eps:ℂ)^4*(spatialSquare n:ℂ)*dotProduct sourceTemporalEMForce v := by
  rw [force_observation,em_projection_coordinates,←lapse_coefficient]
  rw [show gaugeSlot (0:Fin 4) 6=(15:Fin 289) from rfl,
    show gaugeSlot (0:Fin 4) 7=(16:Fin 289) from rfl,
    show gaugeSlot (0:Fin 4) 11=(20:Fin 289) from rfl]
  norm_num [sourceMatrix,sourceEMNativePrincipalTerms,SourceTerm.matrix,Powers.value,
    coefficientValue,Matrix.add_mulVec,Matrix.single_mulVec,Pi.single_apply,
    frequencyRay,physicalFrequencyMomentum,gaugeSlot,spatialSquare,mul_pow,
    Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow]
  ring

private theorem background_momentum (p : Fin 4 → ℂ) :
    sourceMatrix sourceEMNativeBackgroundTerms p=sourceMatrix sourceEMNativeBackgroundTerms 0 := by
  simp [sourceMatrix,sourceEMNativeBackgroundTerms,SourceTerm.matrix,Powers.value]

private theorem native_schur_balance (p : Fin 4 → ℂ) (static : p 0=0) (v : Fin 289 → ℂ)
    (auxiliary : emAuxiliarySlice (emOriginalJacobi p*ᵥv)=0) :
    dotProduct sourceTemporalEMForce (emOriginalJacobi p*ᵥv)-sourceEMNativeBackgroundRead v-
      sourceEMNativeLowerRead p v=(sourceMatrix sourceEMNativePrincipalTerms p*ᵥv) 0 := by
  have row := source_em_native_schur_row p static v
  rw [actual_native_complete_force_identity,nativeCompleteForceRead,auxiliary,
    Matrix.mulVec_zero,Matrix.mulVec_zero,sub_zero,actual_complete_em_observation] at row
  simp only [sourceMatrix_append,Matrix.add_mulVec,Pi.add_apply,background_momentum] at row
  rw [←force_observation] at row
  change sourceEMNativeBackgroundRead v+sourceEMNativeLowerRead p v+
    (sourceMatrix sourceEMNativePrincipalTerms p*ᵥv) 0=
    dotProduct sourceTemporalEMForce (emOriginalJacobi p*ᵥv) at row
  linear_combination -row

private theorem force_gram : dotProduct sourceTemporalEMForce sourceTemporalEMForce=(3/4:ℂ) := by
  have gram := congrFun (congrFun ActualEMCurrentSplit.em_coordinate_gram 0) 0
  change (∑j,emInsertion j 0*emInsertion j 0)=(3/4:ℂ)
  simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.smul_apply,Matrix.one_apply,
    if_true,smul_eq_mul,mul_one] using gram

/-- Background, lower and the full quantum driver return jointly to the
original temporal cofactor principal, without separate endpoint hypotheses. -/
theorem source_matter_clock_balance_principal_eval (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) :
    sourceClockEval eps sigma (sourceMatterClockBalanceNumerator event n)+
      (3/4:ℂ)*sourceMatterClockActualDeterminant event n eps sigma=
      2*(lapse:ℂ)*(eps:ℂ)^4*(spatialSquare n:ℂ)*
        dotProduct sourceTemporalEMForce (sourceMatterClockActualFieldNumerator event n eps sigma) := by
  have static : frequencyRay eps 0 n 0=0 := by
    change -Complex.I*((0*eps^2:ℝ):ℂ)=0
    simp
  have native := native_schur_balance (frequencyRay eps 0 n) static
    (sourceMatterClockActualFieldNumerator event n eps sigma)
    (source_matter_clock_field_auxiliary_native event n eps sigma)
  rw [source_em_native_lower_spatial_factor,source_em_native_principal_read] at native
  rw [source_matter_clock_balance_numerator_eval]
  unfold sourceMatterClockActualDriverNumerator
  rw [dotProduct_sub,dotProduct_smul,smul_eq_mul,force_gram]
  linear_combination native

private theorem positive_real_polynomial_zero (P : ℂ[X])
    (zero : ∀ s : ℝ, 0<s → P.eval (s:ℂ)=0) : P=0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  have injective : Function.Injective (fun k : ℕ => ((k+1:ℕ):ℂ)) := by
    intro a b same
    change ((a+1:ℕ):ℂ)=((b+1:ℕ):ℂ) at same
    have natural : a+1=b+1 := by exact_mod_cast same
    omega
  refine (Set.infinite_range_of_injective injective).mono ?_
  rintro z ⟨k,rfl⟩
  change P.eval ((k+1:ℕ):ℂ)=0
  have point : (((k:ℝ)+1:ℝ):ℂ)=((k+1:ℕ):ℂ) := by push_cast; rfl
  rw [←point]
  exact zero ((k:ℝ)+1) (by positivity)

private theorem clock_polynomial_zero (P : (ℂ[X])[X])
    (zero : ∀ eps sigma : ℝ, 0<sigma → sourceClockEval eps sigma P=0) : P=0 := by
  have specialized (eps : ℝ) : clockSpecialize eps P=0 :=
    positive_real_polynomial_zero _ (fun sigma positive => zero eps sigma positive)
  apply Polynomial.ext
  intro k
  rw [coeff_zero]
  apply positive_real_polynomial_zero
  intro eps _
  have coefficient := congrArg (fun Q : ℂ[X] => Q.coeff k) (specialized eps)
  simpa only [clockSpecialize,Polynomial.coe_mapRingHom,coeff_map,coeff_zero,
    Polynomial.coe_evalRingHom] using coefficient

private theorem constant_eval (eps sigma : ℝ) (z : ℂ) :
    sourceClockEval eps sigma (C (C z))=z := by
  simp only [sourceClockEval,RingHom.comp_apply,clockSpecialize,Polynomial.coe_mapRingHom,
    Polynomial.map_C,Polynomial.coe_evalRingHom,Polynomial.eval_C]

private theorem epsilon_eval (eps sigma : ℝ) :
    sourceClockEval eps sigma (C (X:ℂ[X]))=(eps:ℂ) := by
  simp only [sourceClockEval,RingHom.comp_apply,clockSpecialize,Polynomial.coe_mapRingHom,
    Polynomial.map_C,Polynomial.coe_evalRingHom,Polynomial.eval_C,Polynomial.eval_X]

private theorem lift_principal {I : Type*} [Fintype I]
    (B D : (ℂ[X])[X]) (E N : I → (ℂ[X])[X]) (z : ℂ)
    (point : ∀ eps sigma : ℝ, sourceClockEval eps sigma B+(3/4:ℂ)*sourceClockEval eps sigma D=
      z*(eps:ℂ)^4*dotProduct (sourceClockEval eps sigma ∘ E) (sourceClockEval eps sigma ∘ N)) :
    B+C (C (3/4:ℂ))*D=C (C z)*(C (X:ℂ[X]))^4*dotProduct E N := by
  apply sub_eq_zero.mp
  apply clock_polynomial_zero
  intro eps sigma _
  rw [map_sub,map_add,map_mul,map_mul,map_mul,map_pow,
    constant_eval,constant_eval,epsilon_eval,(sourceClockEval eps sigma).map_dotProduct]
  exact sub_eq_zero.mpr (point eps sigma)

/-- The complete source balance carries the original temporal principal
cofactor already in its two independent polynomial coordinates. -/
theorem source_matter_clock_balance_principal (event : DressedEvent) (n : PhysicalMomentum) :
    sourceMatterClockBalanceNumerator event n+C (C (3/4:ℂ))*sourceMatterClockDeterminant event n=
      C (C (2*(lapse:ℂ)*(spatialSquare n:ℂ)))*(C (X:ℂ[X]))^4*
        dotProduct sourceEMClockForce (sourceMatterClockFieldNumerator event n) := by
  apply lift_principal
  intro eps sigma
  rw [force_eval,source_matter_clock_field_eval,source_matter_clock_determinant_eval]
  have paid := source_matter_clock_balance_principal_eval event n eps sigma
  linear_combination paid

end LowEnergy.GaussComposite.ActualSourcePreparedMatterClockPrincipal
