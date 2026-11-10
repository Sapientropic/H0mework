import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedSchur97PhysicalRead

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedSchur97Polynomial
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalCharacteristic
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedOrderedStatic ActualDressedUniformMaterialCoefficients
open ActualSourcePreparedClockReducedPencil ActualPreparedMatterSupport ActualPreparedMatterClock
open ActualSourcePreparedInactiveNativeData ActualSourcePreparedInactiveNativeWeights
open ActualSourcePreparedInactiveNativeInverse ActualSourcePreparedInactiveSchurReturn
open ActualSourcePreparedSchur97PhysicalRead
open scoped Matrix BigOperators

private def clockConstant : ℂ →+* (ℂ[X])[X] :=
  (Polynomial.C : ℂ[X] →+* (ℂ[X])[X]).comp (Polynomial.C : ℂ →+* ℂ[X])
private def clockMomentum (n : PhysicalMomentum) : Fin 4 → (ℂ[X])[X] :=
  Fin.cases 0 (fun j => clockConstant (Complex.I*(n j:ℂ))*(C (X:ℂ[X]))^2)
private def clockTerm (n : PhysicalMomentum) (a : SourceTerm) : Matrix (Fin 289) (Fin 289) ((ℂ[X])[X]) :=
  Matrix.single a.row a.column (clockConstant (coefficientValue a.coefficient)*
    clockMomentum n 0^a.powers.temporal*clockMomentum n 1^a.powers.first*
      clockMomentum n 2^a.powers.second*clockMomentum n 3^a.powers.third)
private def clockTerms (n : PhysicalMomentum) (ts : List SourceTerm) : Matrix (Fin 289) (Fin 289) ((ℂ[X])[X]) :=
  (ts.map (clockTerm n)).sum

private theorem constant_eval (eps sigma : ℝ) (z : ℂ) : sourceClockEval eps sigma (clockConstant z)=z := by
  simp only [clockConstant,RingHom.comp_apply,sourceClockEval,clockSpecialize,
    Polynomial.coe_mapRingHom,Polynomial.map_C,Polynomial.coe_evalRingHom,Polynomial.eval_C]
private theorem epsilon_eval (eps sigma : ℝ) : sourceClockEval eps sigma (C (X:ℂ[X]))=(eps:ℂ) := by
  simp only [sourceClockEval,RingHom.comp_apply,clockSpecialize,Polynomial.coe_mapRingHom,
    Polynomial.map_C,Polynomial.coe_evalRingHom,Polynomial.eval_C,Polynomial.eval_X]
private theorem momentum_eval (n : PhysicalMomentum) (eps sigma : ℝ) :
    sourceClockEval eps sigma ∘ clockMomentum n=frequencyRay eps 0 n := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [clockMomentum,frequencyRay,physicalFrequencyMomentum]
  · simp only [clockMomentum,Fin.cases_succ,Function.comp_apply,map_mul,map_pow,constant_eval,epsilon_eval]
    change Complex.I*(n j:ℂ)*(eps:ℂ)^2=Complex.I*((eps^2*n j:ℝ):ℂ)
    push_cast
    ring
private theorem terms_eval (n : PhysicalMomentum) (eps sigma : ℝ) (ts : List SourceTerm) :
    (clockTerms n ts).map (sourceClockEval eps sigma)=sourceMatrix ts (frequencyRay eps 0 n) := by
  induction ts with
  | nil => simp [clockTerms,sourceMatrix]
  | cons a rest ih =>
      simp only [clockTerms,List.map_cons,List.sum_cons] at ih ⊢
      rw [Matrix.map_add _ (fun a b => (sourceClockEval eps sigma).map_add a b),ih]
      simp only [sourceMatrix_cons]
      congr 1
      rw [clockTerm,Matrix.map_single]
      simp only [map_mul,map_pow,constant_eval,SourceTerm.matrix,Powers.value]
      have p := momentum_eval n eps sigma
      have point (i : Fin 4) : sourceClockEval eps sigma (clockMomentum n i)=frequencyRay eps 0 n i := congrFun p i
      rw [point 0,point 1,point 2,point 3]
      simp only [mul_assoc]

def nativeClockSquare (n : PhysicalMomentum) : (ℂ[X])[X] :=
  clockConstant (-(spatialSquare n:ℂ))*(C (X:ℂ[X]))^4

def nativeClockDenominator (n : PhysicalMomentum) : (ℂ[X])[X] :=
  nativeClockSquare n*(nativeClockSquare n+clockConstant (72/25))*
    (nativeClockSquare n+clockConstant (81/50))

private def weightComplement (n : PhysicalMomentum) (i : NativeInactive) : (ℂ[X])[X] :=
  if i.val ∈ sourceInactivePoleIndices then nativeClockSquare n+clockConstant (81/50)
  else if i.val ∈ sourceInactiveMassIndices then nativeClockSquare n*(nativeClockSquare n+clockConstant (72/25))
  else nativeClockDenominator n

/-- The already checked compact source numerator clears every native192 row
with a single source spatial denominator; no new inverse witness is supplied. -/
def nativeClockInverseNumerator (n : PhysicalMomentum) : Matrix NativeInactive NativeInactive ((ℂ[X])[X]) :=
  Matrix.diagonal (weightComplement n)*
    (clockTerms n sourceInactiveInverseNumeratorTerms).submatrix Subtype.val Subtype.val

private theorem square_eval (n : PhysicalMomentum) (eps sigma : ℝ) :
    sourceClockEval eps sigma (nativeClockSquare n)=nativeSpatialSquare (frequencyRay eps 0 n) := by
  rw [nativeClockSquare,map_mul,map_pow,constant_eval,epsilon_eval,source_inactive_native_physical_square]
  ring

private theorem complement_product (n : PhysicalMomentum) (eps sigma : ℝ) (i : NativeInactive) :
    sourceClockEval eps sigma (weightComplement n i)*nativeInactiveWeight (frequencyRay eps 0 n) i.val=
      sourceClockEval eps sigma (nativeClockDenominator n) := by
  unfold weightComplement nativeInactiveWeight nativeClockDenominator
  have outside : (73 ≤ i.val.val ∧ i.val.val < 121) ∨ 145 ≤ i.val.val := i.property
  rw [if_pos outside]
  split_ifs <;> simp only [map_mul,map_add,constant_eval,square_eval] <;> ring

private theorem map_submatrix {I J K L : Type*} (P : Matrix I J ((ℂ[X])[X]))
    (r : K → I) (c : L → J) (f : ((ℂ[X])[X]) →+* ℂ) :
    (P.submatrix r c).map f=(P.map f).submatrix r c := rfl

private theorem map_smul {I J : Type*} (f : ((ℂ[X])[X]) →+* ℂ)
    (d : (ℂ[X])[X]) (P : Matrix I J ((ℂ[X])[X])) :
    (d • P).map f=f d • P.map f := by
  ext i j
  exact f.map_mul d (P i j)

private theorem mapped_diagonal {I : Type*} [DecidableEq I] (f : ((ℂ[X])[X]) →+* ℂ)
    (w : I → (ℂ[X])[X]) : (Matrix.diagonal w).map f=Matrix.diagonal (f ∘ w) := by
  ext i j
  by_cases same : i=j <;> simp only [Matrix.map_apply,Matrix.diagonal_apply,same,if_true,if_false,map_zero,Function.comp_apply]

/-- The full192 inverse has a common polynomial clearing on the original
physical source ball; all three spatial coordinates remain in its numerator. -/
theorem source_native_clock_inverse_clear (n : PhysicalMomentum) (eps sigma : ℝ)
    (unit : spatialSquare n=1) (positive : 0<eps) (small : eps≤1/2) :
    (nativeClockInverseNumerator n).map (sourceClockEval eps sigma)=
      sourceClockEval eps sigma (nativeClockDenominator n) • nativeInactiveInverse (frequencyRay eps 0 n) := by
  unfold nativeClockInverseNumerator
  rw [Matrix.map_mul,mapped_diagonal,map_submatrix,terms_eval]
  have weights : sourceClockEval eps sigma ∘ weightComplement n=
      fun i : NativeInactive => sourceClockEval eps sigma (nativeClockDenominator n)*
        (nativeInactiveWeight (frequencyRay eps 0 n) i.val)⁻¹ := by
    funext i
    apply (eq_mul_inv_iff_mul_eq₀ (source_inactive_native_weight_nonzero eps n unit positive small i.val i.property)).mpr
    exact complement_product n eps sigma i
  rw [weights]
  unfold nativeInactiveInverse nativeInactiveNumerator
  rw [←Matrix.smul_mul,←Matrix.diagonal_smul]
  rfl

/-- A genuine bivariate polynomial97 pencil for the same full quantum
response, including every active/inactive cross column. -/
def sourceSchur97Polynomial (event : DressedEvent) (n : PhysicalMomentum) :
    Matrix NativeActive NativeActive ((ℂ[X])[X]) :=
  nativeClockDenominator n • (sourceMatterClockPencil event n).submatrix Subtype.val Subtype.val-
    (sourceMatterClockPencil event n).submatrix
      (Subtype.val : NativeActive → Fin 289) (Subtype.val : NativeInactive → Fin 289)*
    nativeClockInverseNumerator n*
    (sourceMatterClockPencil event n).submatrix
      (Subtype.val : NativeInactive → Fin 289) (Subtype.val : NativeActive → Fin 289)

theorem source_schur97_polynomial_eval (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (unit : spatialSquare n=1) (positive : 0<eps) (small : eps≤1/2) :
    (sourceSchur97Polynomial event n).map (sourceClockEval eps sigma)=
      sourceClockEval eps sigma (nativeClockDenominator n) • sourceMatterNativeSchur event n eps sigma := by
  unfold sourceSchur97Polynomial
  rw [Matrix.map_sub _ (fun a b => (sourceClockEval eps sigma).map_sub a b),map_smul,Matrix.map_mul,Matrix.map_mul,
    source_native_clock_inverse_clear n eps sigma unit positive small]
  simp only [map_submatrix]
  unfold sourceMatterNativeSchur sourceMatterNativeMatrix
  rw [Matrix.mul_smul,Matrix.smul_mul,←smul_sub]

theorem source_native_clock_denominator_nonzero (n : PhysicalMomentum) (eps sigma : ℝ)
    (unit : spatialSquare n=1) (positive : 0<eps) (small : eps≤1/2) :
    sourceClockEval eps sigma (nativeClockDenominator n)≠0 := by
  have pole := source_inactive_native_weight_nonzero eps n unit positive small 73 (by decide)
  have mass := source_inactive_native_weight_nonzero eps n unit positive small 75 (by decide)
  have generated : sourceClockEval eps sigma (nativeClockDenominator n)=
      nativeInactiveWeight (frequencyRay eps 0 n) 73*nativeInactiveWeight (frequencyRay eps 0 n) 75 := by
    simp only [nativeClockDenominator,map_mul,map_add,constant_eval,square_eval]
    norm_num [nativeInactiveWeight,sourceInactivePoleIndices,sourceInactiveMassIndices,Fin.ext_iff]
  exact generated.symm ▸ mul_ne_zero pole mass

/-- The polynomial clearing contributes exactly d^97 to the evaluated
source determinant; this factor is not an additional physical IR pole. -/
theorem source_schur97_polynomial_determinant_eval (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (unit : spatialSquare n=1) (positive : 0<eps) (small : eps≤1/2) :
    sourceClockEval eps sigma (sourceSchur97Polynomial event n).det=
      (sourceClockEval eps sigma (nativeClockDenominator n))^97*
        (sourceMatterNativeSchur event n eps sigma).det := by
  have mapped := (sourceClockEval eps sigma).map_det (sourceSchur97Polynomial event n)
  simp only [RingHom.mapMatrix_apply] at mapped
  rw [mapped,source_schur97_polynomial_eval event n eps sigma unit positive small,Matrix.det_smul,
    source_inactive_native_dimensions.2]

theorem source_schur97_polynomial_original_regular_iff (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (unit : spatialSquare n=1) (positive : 0<eps) (small : eps≤1/2) (damping : 0<sigma) :
    sourceClockEval eps sigma (sourceSchur97Polynomial event n).det≠0 ↔ correctedDet event eps 0 sigma n≠0 := by
  rw [source_schur97_polynomial_determinant_eval event n eps sigma unit positive small]
  have nonzero := pow_ne_zero 97 (source_native_clock_denominator_nonzero n eps sigma unit positive small)
  exact (⟨fun h => (mul_ne_zero_iff.mp h).2,fun h => mul_ne_zero nonzero h⟩ :
    (sourceClockEval eps sigma (nativeClockDenominator n))^97*(sourceMatterNativeSchur event n eps sigma).det≠0 ↔
      (sourceMatterNativeSchur event n eps sigma).det≠0).trans
        (source_schur97_original_regular_iff event n eps sigma unit positive small damping).symm

end LowEnergy.GaussComposite.ActualSourcePreparedSchur97Polynomial
