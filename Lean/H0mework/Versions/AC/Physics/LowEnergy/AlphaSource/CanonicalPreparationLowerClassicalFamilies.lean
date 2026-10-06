import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationLowerClassicalMetrics

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLowerClassical
open SaturationMonoid.PhysicsCore
open PreparationVacuumPrincipalBudget PreparationVacuumCoefficientBudget PreparationVacuumPrimitiveMatrix
open PreparationVacuumRationalW PreparationVacuumCentralBudget PreparationVacuumEngineBudget
open PreparationVacuumCanonicalMoyal PreparationVacuumClockSymbol PreparationVacuumEngineSmooth
open PreparationVacuumMoyalBudget PreparationVacuumMoyalSymmetry PreparationVacuumTimeReader
open PreparationVacuumLowerLeaves PreparationVacuumLowerTensor PreparationVacuumTemporalOrdering PreparationVacuumEnergyTail
open PreparationScalarCoordinates PreparationCoordinates PreparationMeasure
open SourceQuantumScalarChart SourceQuantumNativeDimensions SourceQuantumResidualGaugeSlice
open SourceQuantumConfigurationHilbert GaussHistoryHilbert GaussNativeEnergy GaussNativePotential
open CanonicalPreparationCutoff GaussLiveMomentum GaussNativeForm PreparationActualFactor PreparationPhaseGuard
open scoped BigOperators ContDiff Topology Matrix RealInnerProductSpace

private theorem embedded_sum_le {a b : ℕ} (e : Fin a ↪ Fin b) (f : Fin b → ℝ)
    (positive : ∀ i,0 ≤ f i) : (∑ i,f (e i)) ≤ ∑ i,f i := by
  rw [←Finset.sum_image]
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => positive i)
  · exact fun i _ j _ h => e.injective h

private theorem linear_higher (f : Phase →L[ℝ] ℝ) (n : ℕ) (w : Word (n+2)) (x : Phase) :
    PreparationVacuumCanonicalMoyal.jet (n+2) f w x=0 := by
  unfold PreparationVacuumCanonicalMoyal.jet
  rw [iteratedFDeriv_succ_apply_right]
  simp only [ContinuousLinearMap.fderiv]
  rw [iteratedFDeriv_const_of_ne (by omega)]
  simp

theorem annulus_momentumColumn_budget {a : ℕ} (e : Fin a ↪ Fin 100) (x : Phase)
    (annulus : (∑ i : Fin 100,(x.2 i)^2) ≤ 4) (N : ℕ) :
    MatrixBound (momentumColumn e) N (affineArray (2*a) 1) x := by
  have entries (i : Fin 100) : |x.2 i| ≤ 2 := by
    have small := Finset.single_le_sum (s:=Finset.univ) (fun j _ => sq_nonneg (x.2 j)) (Finset.mem_univ i)
    have small := small.trans annulus
    nlinarith [abs_nonneg (x.2 i),sq_abs (x.2 i)]
  have total : ∀ m,∀ w : Word m,
      (∑ i : Fin a,|PreparationVacuumCanonicalMoyal.jet m (fun y => y.2 (e i)) w x|) ≤ affineArray (2*a) 1 m := by
    intro m w
    cases m with
    | zero =>
      simp only [PreparationVacuumCanonicalMoyal.jet,iteratedFDeriv_zero_apply,affineArray]
      calc
        _ ≤ ∑ _i : Fin a,(2 : ℝ) := Finset.sum_le_sum (fun i _ => entries (e i))
        _ = _ := by simp; ring
    | succ m => cases m with
      | zero =>
        have one (i : Fin 100) : PreparationVacuumCanonicalMoyal.jet 1 (fun y => y.2 i) w x=momentumCoordinate i (PreparationVacuumCanonicalMoyal.slotDirection (w 0)) := by
          change PreparationVacuumCanonicalMoyal.jet 1 (momentumCoordinate i) w x=_
          simp [PreparationVacuumCanonicalMoyal.jet,ContinuousLinearMap.fderiv]
        simp_rw [one]
        apply (embedded_sum_le e (fun i => |momentumCoordinate i (PreparationVacuumCanonicalMoyal.slotDirection (w 0))|) (fun i => abs_nonneg _)).trans
        rcases w 0 with ⟨i,b⟩
        cases b <;> simp [momentumCoordinate,PreparationVacuumCanonicalMoyal.slotDirection,pDirection,qDirection,affineArray,apply_ite,abs_zero,abs_one]
      | succ m =>
        have zero (i : Fin a) : PreparationVacuumCanonicalMoyal.jet (m+2) (fun y => y.2 (e i)) w x=0 := linear_higher (momentumCoordinate (e i)) m w x
        simp only [zero,abs_zero,Finset.sum_const_zero,affineArray,le_refl]
  intro m _ w
  constructor
  · intro i
    simpa [momentumColumn] using
      (Finset.single_le_sum (fun j _ => abs_nonneg (PreparationVacuumCanonicalMoyal.jet m (fun y => y.2 (e j)) w x)) (Finset.mem_univ i)).trans (total m w)
  · intro j
    exact total m w


theorem annulus_rawScalar_budget (x : Phase) (hx : x∈poleDomain)
    (annulus : (∑ i : Fin 100,(x.2 i)^2) ≤ 4) (N : ℕ) (input : CoefficientInputs x N) :
    MatrixBound rawScalarColumn N scalarMomentumArray x := by
  have same : rawScalarColumn=(fun y => scalarCoefficients y.1*momentumColumn p94Embedding y) := by
    funext y
    ext a j
    exact actual_rawScalar_momentum_matrix y a
  rw [same]
  exact finite_matrix_product _ _ (fun a k => sourceCoefficient_smooth _ k)
    (momentumColumn_smooth p94Embedding) N scalarFactorArray p94Array scalarFactor_nonnegative
    (affineArray_nonnegative 188 1 (by norm_num) (by norm_num)) x hx input.scalar
    (by simpa only [p94Array,Nat.cast_ofNat,show (2 : ℝ)*94=188 by norm_num] using annulus_momentumColumn_budget p94Embedding x annulus N)

theorem annulus_rawGauge_budget (x : Phase) (hx : x∈poleDomain)
    (annulus : (∑ i : Fin 100,(x.2 i)^2) ≤ 4) (N : ℕ) (input : CoefficientInputs x N) :
    MatrixBound rawGaugeColumn N gaugeMomentumArray x := by
  have same : rawGaugeColumn=(fun y => gaugeCoefficients y.1*momentumColumn p94Embedding y) := by
    funext y
    ext a j
    exact actual_rawGauge_momentum_matrix y a
  rw [same]
  exact finite_matrix_product _ _ (fun a k => sourceCoefficient_smooth _ k)
    (momentumColumn_smooth p94Embedding) N gaugeFactorArray p94Array gaugeFactor_nonnegative
    (affineArray_nonnegative 188 1 (by norm_num) (by norm_num)) x hx input.gauge
    (by simpa only [p94Array,Nat.cast_ofNat,show (2 : ℝ)*94=188 by norm_num] using annulus_momentumColumn_budget p94Embedding x annulus N)



private theorem original_coordinate_expansion {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (e : V ≃ₗ[ℝ] (Fin n→ℝ)) (v : V) : v=∑ a,e v a • e.symm (Pi.single a 1) := by
  apply e.injective
  simp only [map_sum,map_smul,LinearEquiv.apply_symm_apply]
  ext j
  simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]

theorem scalarContraction_raw (x : Phase) (s : Fin 3) :
    scalarContraction (fullCoordinates.symm x.1) (nativeCovector x.2) s=
      ∑ a : Fin 70,rawScalarMomentum a x*gradientColumn s x a 0 := by
  let v := scalarGradient (fullCoordinates.symm x.1) s
  have functional : scalarContraction (fullCoordinates.symm x.1) (nativeCovector x.2) s=scalarFunctional x v := by
    conv_rhs => rw [←scalarBasis.sum_repr' v]
    simp only [map_sum,map_smul,smul_eq_mul]
    change (∑ a : ScalarIndex,scalarMomentum _ _ a*inner ℝ (scalarBasis a) v)=_
    apply Finset.sum_congr rfl
    intro a ha
    have same : scalarFunctional x (scalarBasis a)=scalarMomentum (fullCoordinates.symm x.1) (nativeCovector x.2) a := rfl
    rw [same]
    ring
  rw [functional]
  conv_lhs => rw [original_coordinate_expansion scalarRealify v]
  simp only [map_sum,map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a ha
  change scalarRealify v a*rawScalarMomentum a x=rawScalarMomentum a x*scalarRealify v a
  ring

theorem gaugeContraction_raw (x : Phase) (s t : Fin 3) :
    gaugeContraction (fullCoordinates.symm x.1) (nativeCovector x.2) s t=
      ∑ a : Fin 12,rawGaugeMomentum (combinedRow s a) x*magneticColumn x (combinedRow t a) 0 := by
  let v := magneticField (fullCoordinates.symm x.1) t
  have functional : gaugeContraction (fullCoordinates.symm x.1) (nativeCovector x.2) s t=gaugeFunctional x s v := by
    conv_rhs => rw [←lieBasis.sum_repr' v]
    simp only [map_sum,map_smul,smul_eq_mul]
    change (∑ a : LieIndex,electricMomentum _ _ s a*inner ℝ (lieBasis a) v)=_
    apply Finset.sum_congr rfl
    intro a ha
    have same : gaugeFunctional x s (lieBasis a)=electricMomentum (fullCoordinates.symm x.1) (nativeCovector x.2) s a := rfl
    rw [same]
    ring
  rw [functional]
  conv_lhs => rw [original_coordinate_expansion rawCoordinates v]
  simp only [map_sum,map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a ha
  change rawCoordinates v a*ambientMomentum (fullCoordinates.symm x.1) (nativeCovector x.2)
    (0,gaugeInsertion s (rawCoordinates.symm (Pi.single a 1)))=_
  rw [gaugeInsertion_raw]
  simp only [magneticColumn,spatial_combined,native_combined]
  change rawCoordinates v a*rawGaugeMomentum (combinedRow s a) x=
    rawGaugeMomentum (combinedRow s a) x*rawCoordinates v a
  ring

def spatialEmbedding (s : Fin 3) : Fin 12 ↪ Fin 36 where
  toFun := combinedRow s
  inj' := by
    intro i j h
    simpa only [native_combined] using congrArg nativeRow h

def selectColumn {a b : ℕ} (e : Fin a ↪ Fin b) (F : RectSymbol b 1) : RectSymbol a 1 := fun x i j => F x (e i) j

theorem selectColumn_budget {a b : ℕ} (e : Fin a ↪ Fin b) (F : RectSymbol b 1)
    (M : ℕ) (B : PreparationVacuumCentralBudget.ArrayBound) (x : Phase) (bound : MatrixBound F M B x) :
    MatrixBound (selectColumn e F) M B x := by
  intro m hm w
  exact ⟨fun i => (bound m hm w).1 (e i),fun j =>
    (embedded_sum_le e (fun i => |PreparationVacuumCanonicalMoyal.jet m (fun y => F y i j) w x|) (fun _ => abs_nonneg _)).trans
      ((bound m hm w).2 j)⟩

def scalarContractionSymbol (s : Fin 3) : Symbol := fun x =>
  scalarContraction (fullCoordinates.symm x.1) (nativeCovector x.2) s

def gaugeContractionSymbol (s t : Fin 3) : Symbol := fun x =>
  gaugeContraction (fullCoordinates.symm x.1) (nativeCovector x.2) s t

theorem scalarContraction_matrix (s : Fin 3) : scalarContractionSymbol s=
    (fun x => ((rawScalarColumn x)ᵀ*gradientColumn s x) 0 0) := by
  funext x
  exact scalarContraction_raw x s

theorem gaugeContraction_matrix (s t : Fin 3) : gaugeContractionSymbol s t=
    (fun x => ((selectColumn (spatialEmbedding s) rawGaugeColumn x)ᵀ*
      selectColumn (spatialEmbedding t) magneticColumn x) 0 0) := by
  funext x
  exact gaugeContraction_raw x s t

theorem scalarContraction_budget (s : Fin 3) (M : ℕ) (x : Phase) (hx : x∈poleDomain)
    (box : x.1∈sourceClosedBox) (annulus : (∑ i : Fin 100,(x.2 i)^2) ≤ 4)
    (input : CoefficientInputs x M) :
    FiniteBound (scalarContractionSymbol s) M (productArray scalarMomentumArray UiArray) x := by
  rw [scalarContraction_matrix]
  have bound := finite_matrix_product (fun y => (rawScalarColumn y)ᵀ) (gradientColumn s)
    (fun _ i => rawScalarMomentum_smooth i) (gradientColumn_smooth s) M scalarMomentumArray UiArray
    (productArray_nonnegative _ _ scalarFactor_nonnegative (affineArray_nonnegative 188 1 (by norm_num) (by norm_num)))
    (fun m => mul_nonneg (by norm_num) (productArray_nonnegative _ _
      (affineArray_nonnegative 15 1 (by norm_num) (by norm_num))
      (affineArray_nonnegative 919 1 (by norm_num) (by norm_num)) m)) x hx
    (finite_matrix_transpose _ _ _ _ (annulus_rawScalar_budget x hx annulus M input))
    (gradientColumn_budget s M x hx box)
  exact fun m hm w => rect_entry (bound m hm w) 0 0


theorem UiArray_nonnegative (m : ℕ) : 0 ≤ UiArray m :=
  mul_nonneg (by norm_num) (productArray_nonnegative _ _
    (affineArray_nonnegative 15 1 (by norm_num) (by norm_num))
    (affineArray_nonnegative 919 1 (by norm_num) (by norm_num)) m)

theorem magneticFieldArray_nonnegative (m : ℕ) : 0 ≤ magneticFieldArray m :=
  mul_nonneg (by norm_num) (powerArray_nonnegative _
    (affineArray_nonnegative 15 1 (by norm_num) (by norm_num)) 2 m)

theorem gaugeContraction_budget (s t : Fin 3) (M : ℕ) (x : Phase) (hx : x∈poleDomain)
    (box : x.1∈sourceClosedBox) (annulus : (∑ i : Fin 100,(x.2 i)^2) ≤ 4)
    (input : CoefficientInputs x M) :
    FiniteBound (gaugeContractionSymbol s t) M (productArray gaugeMomentumArray magneticFieldArray) x := by
  rw [gaugeContraction_matrix]
  have bound := finite_matrix_product
    (fun y => (selectColumn (spatialEmbedding s) rawGaugeColumn y)ᵀ)
    (selectColumn (spatialEmbedding t) magneticColumn)
    (fun _ i => rawGaugeMomentum_smooth _) (fun i j => magneticColumn_smooth _ j)
    M gaugeMomentumArray magneticFieldArray
    (productArray_nonnegative _ _ gaugeFactor_nonnegative (affineArray_nonnegative 188 1 (by norm_num) (by norm_num)))
    magneticFieldArray_nonnegative x hx
    (finite_matrix_transpose _ _ _ _ (selectColumn_budget _ _ _ _ _ (annulus_rawGauge_budget x hx annulus M input)))
    (selectColumn_budget _ _ _ _ _ (magneticColumn_budget M x hx box))
  exact fun m hm w => rect_entry (bound m hm w) 0 0

def originalGram : Matrix (Fin 12) (Fin 12) ℚ := fun i j =>
  if i=j then (if i=11 then 1 else 2) else if (i=6 ∧ j=7) ∨ (i=7 ∧ j=6) then 1 else 0

theorem originalGram_norm : ∀ i : Fin 12,
    (∑ j,|originalGram i j|) ≤ 3 ∧ (∑ j,|originalGram j i|) ≤ 3 := by decide +kernel

theorem originalGram_real (i j : Fin 12) : (originalGram i j : ℝ)=
    (if i=j then (if i=11 then 1 else 2) else 0)+
      (if i=6 then (if j=7 then 1 else 0) else 0)+
      (if i=7 then (if j=6 then 1 else 0) else 0) := by
  fin_cases i <;> fin_cases j <;> norm_num [originalGram,Fin.ext_iff]

theorem originalGram_mul (v : Fin 12→ℝ) (i : Fin 12) :
    (∑ j : Fin 12,(originalGram i j : ℝ)*v j)=
      (if i=11 then 1 else 2)*v i+(if i=6 then v 7 else 0)+(if i=7 then v 6 else 0) := by
  simp_rw [originalGram_real,add_mul]
  simp [Finset.sum_add_distrib,ite_mul]

theorem originalGram_source (a b : NativeLie) : inner ℝ a b=
    ∑ i : Fin 12,∑ j : Fin 12,rawCoordinates a i*(originalGram i j : ℝ)*rawCoordinates b j := by
  have collapse : (∑ i : Fin 12,∑ j : Fin 12,rawCoordinates a i*(originalGram i j : ℝ)*rawCoordinates b j)=
      ∑ i : Fin 12,rawCoordinates a i*((if i=11 then 1 else 2)*rawCoordinates b i+
        (if i=6 then rawCoordinates b 7 else 0)+(if i=7 then rawCoordinates b 6 else 0)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [←originalGram_mul (rawCoordinates b) i,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [collapse]
  conv_lhs => rw [←rawCoordinates.symm_apply_apply a,←rawCoordinates.symm_apply_apply b]
  rw [original_raw_inner]
  generalize rawCoordinates a=u
  generalize rawCoordinates b=v
  rw [show (Finset.univ : Finset (Fin 12))={0,1,2,3,4,5,6,7,8,9,10,11} by decide +kernel]
  rw [Finset.sum_insert (by decide : (0 : Fin 12)∉({1,2,3,4,5,6,7,8,9,10,11} : Finset (Fin 12))),
    Finset.sum_insert (by decide : (1 : Fin 12)∉({2,3,4,5,6,7,8,9,10,11} : Finset (Fin 12))),
    Finset.sum_insert (by decide : (2 : Fin 12)∉({3,4,5,6,7,8,9,10,11} : Finset (Fin 12))),
    Finset.sum_insert (by decide : (3 : Fin 12)∉({4,5,6,7,8,9,10,11} : Finset (Fin 12))),
    Finset.sum_insert (by decide : (4 : Fin 12)∉({5,6,7,8,9,10,11} : Finset (Fin 12))),
    Finset.sum_insert (by decide : (5 : Fin 12)∉({6,7,8,9,10,11} : Finset (Fin 12))),
    Finset.sum_insert (by decide : (6 : Fin 12)∉({7,8,9,10,11} : Finset (Fin 12))),
    Finset.sum_insert (by decide : (7 : Fin 12)∉({8,9,10,11} : Finset (Fin 12))),
    Finset.sum_insert (by decide : (8 : Fin 12)∉({9,10,11} : Finset (Fin 12))),
    Finset.sum_insert (by decide : (9 : Fin 12)∉({10,11} : Finset (Fin 12))),
    Finset.sum_insert (by decide : (10 : Fin 12)∉({11} : Finset (Fin 12))),Finset.sum_singleton]
  norm_num [Fin.ext_iff]
  ring

def magneticGramSymbol (s t : Fin 3) : Symbol := fun x =>
  inner ℝ (magneticField (fullCoordinates.symm x.1) s) (magneticField (fullCoordinates.symm x.1) t)

def scalarGramSymbol (s t : Fin 3) : Symbol := fun x =>
  inner ℝ (scalarGradient (fullCoordinates.symm x.1) s) (scalarGradient (fullCoordinates.symm x.1) t)

theorem scalarGram_matrix (s t : Fin 3) : scalarGramSymbol s t=
    (fun x => ((gradientColumn s x)ᵀ*gradientColumn t x) 0 0) := by
  funext x
  exact scalar_inner_realified _ _

theorem scalarGram_smooth (s t : Fin 3) : SmoothSymbol (scalarGramSymbol s t) := by
  rw [scalarGram_matrix]
  exact matrix_product_smooth _ _ (fun i j => gradientColumn_smooth s j i) (gradientColumn_smooth t) 0 0

theorem scalarGram_budget (s t : Fin 3) (M : ℕ) (x : Phase) (hx : x∈poleDomain)
    (box : x.1∈sourceClosedBox) : FiniteBound (scalarGramSymbol s t) M (powerArray UiArray 2) x := by
  rw [scalarGram_matrix,powerArray_two]
  have bound := finite_matrix_product (fun y => (gradientColumn s y)ᵀ) (gradientColumn t)
    (fun i j => gradientColumn_smooth s j i) (gradientColumn_smooth t) M UiArray UiArray
    UiArray_nonnegative UiArray_nonnegative x hx
    (finite_matrix_transpose _ _ _ _ (gradientColumn_budget s M x hx box)) (gradientColumn_budget t M x hx box)
  exact fun m hm w => rect_entry (bound m hm w) 0 0

def realOriginalGram : Matrix (Fin 12) (Fin 12) ℝ := fun i j => (originalGram i j : ℝ)

theorem magneticGram_matrix (s t : Fin 3) : magneticGramSymbol s t=
    (fun x => ((selectColumn (spatialEmbedding s) magneticColumn x)ᵀ*
      realOriginalGram*selectColumn (spatialEmbedding t) magneticColumn x) 0 0) := by
  funext x
  rw [magneticGramSymbol,originalGram_source]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,selectColumn,spatialEmbedding,Function.Embedding.coeFn_mk,magneticColumn,realOriginalGram,
    spatial_combined,native_combined,Finset.sum_mul]
  rw [Finset.sum_comm]

def magneticGramArray : ArrayBound := productArray
  (productArray magneticFieldArray (constantArray 3)) magneticFieldArray

theorem magneticGram_smooth (s t : Fin 3) : SmoothSymbol (magneticGramSymbol s t) := by
  rw [magneticGram_matrix]
  have left := matrix_product_smooth
    (fun y => (selectColumn (spatialEmbedding s) magneticColumn y)ᵀ) (fun _ => realOriginalGram)
    (fun i j => magneticColumn_smooth (combinedRow s j) i) (fun _ _ => contDiffOn_const)
  exact matrix_product_smooth
    (fun y => (selectColumn (spatialEmbedding s) magneticColumn y)ᵀ*realOriginalGram)
    (selectColumn (spatialEmbedding t) magneticColumn) left
    (fun i j => magneticColumn_smooth (combinedRow t i) j) 0 0

theorem magneticGram_budget (s t : Fin 3) (M : ℕ) (x : Phase) (hx : x∈poleDomain)
    (box : x.1∈sourceClosedBox) : FiniteBound (magneticGramSymbol s t) M magneticGramArray x := by
  rw [magneticGram_matrix]
  have gram : RectBound realOriginalGram 3 := by
    constructor <;> intro i
    · change (∑ j,|(originalGram i j : ℝ)|) ≤ 3
      exact_mod_cast (originalGram_norm i).1
    · change (∑ j,|(originalGram j i : ℝ)|) ≤ 3
      exact_mod_cast (originalGram_norm i).2
  have first := finite_matrix_product (fun y => (selectColumn (spatialEmbedding s) magneticColumn y)ᵀ)
    (fun _ => realOriginalGram) (fun i j => magneticColumn_smooth (combinedRow s j) i) (fun _ _ => contDiffOn_const)
    M magneticFieldArray (constantArray 3) magneticFieldArray_nonnegative (constantArray_nonnegative 3 (by norm_num)) x hx
    (finite_matrix_transpose _ _ _ _ (selectColumn_budget _ _ _ _ _ (magneticColumn_budget M x hx box)))
    (PreparationVacuumPrincipalBudget.finite_matrix_constant _ 3 gram M x)
  have result := finite_matrix_product
    (fun y => (selectColumn (spatialEmbedding s) magneticColumn y)ᵀ*realOriginalGram)
    (selectColumn (spatialEmbedding t) magneticColumn)
    (matrix_product_smooth (fun y => (selectColumn (spatialEmbedding s) magneticColumn y)ᵀ)
      (fun _ => realOriginalGram) (fun i j => magneticColumn_smooth (combinedRow s j) i) (fun _ _ => contDiffOn_const))
    (fun i j => magneticColumn_smooth (combinedRow t i) j) M (productArray magneticFieldArray (constantArray 3)) magneticFieldArray
    (productArray_nonnegative _ _ magneticFieldArray_nonnegative (constantArray_nonnegative 3 (by norm_num)))
    magneticFieldArray_nonnegative x hx first (selectColumn_budget _ _ _ _ _ (magneticColumn_budget M x hx box))
  exact fun m hm w => rect_entry (result m hm w) 0 0


theorem scalarContraction_smooth (s : Fin 3) : SmoothSymbol (scalarContractionSymbol s) := by
  rw [scalarContraction_matrix]
  exact matrix_product_smooth _ _ (fun _ i => rawScalarMomentum_smooth i) (gradientColumn_smooth s) 0 0

theorem gaugeContraction_smooth (s t : Fin 3) : SmoothSymbol (gaugeContractionSymbol s t) := by
  rw [gaugeContraction_matrix]
  exact matrix_product_smooth _ _ (fun _ i => rawGaugeMomentum_smooth _) (fun i j => magneticColumn_smooth _ j) 0 0

def electricMatrix (n : ℝ) (beta : Fin 3→ℝ) : RectSymbol 3 3 := fun x i j => actualElectric n beta i j x
def electricBudget : ArrayBound := fun m => PreparationVacuumRationalW.electricArray m

theorem electricMatrix_budget (n : ℝ) (beta : Fin 3→ℝ) (time : TimeBox n beta)
    (M : ℕ) (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x) :
    MatrixBound (electricMatrix n beta) M electricBudget x := by
  intro m hm w
  exact ⟨actual_electric_row_budget n beta time m w x box,actual_electric_column_budget n beta time m w x box⟩

def gaugeMixMatrix (n : ℝ) (beta : Fin 3→ℝ) : RectSymbol 3 3 := fun x => electricMatrix n beta x*actualMixed n beta x

def scalarFirstSymbol (n : ℝ) (beta : Fin 3→ℝ) : Symbol := fun x =>
  actualScalarFirstTime n beta (fullCoordinates.symm x.1) (nativeCovector x.2)

def gaugeFirstSymbol (n : ℝ) (beta : Fin 3→ℝ) : Symbol := fun x =>
  actualGaugeFirstTime n beta (fullCoordinates.symm x.1) (nativeCovector x.2)

def scalarFirstArray : ArrayBound := fun m =>
  3*productArray (productArray scalarWArray shiftArray) (productArray scalarMomentumArray UiArray) m

def gaugeFirstArray : ArrayBound := fun m =>
  9*productArray (productArray electricBudget mixedArray) (productArray gaugeMomentumArray magneticFieldArray) m

def firstSampleArray : ArrayBound := fun m => scalarFirstArray m+gaugeFirstArray m

theorem scalarFirst_formula (n : ℝ) (beta : Fin 3→ℝ) : scalarFirstSymbol n beta=
    -(fun x => ∑ i : Fin 3,(PreparationVacuumRationalW.scalarWeight n beta x*actualShift n beta x 0 i)*scalarContractionSymbol i x) := by
  funext x
  unfold scalarFirstSymbol actualScalarFirstTime PreparationVacuumRationalW.scalarWeight actualShift scalarContractionSymbol
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem gaugeFirst_formula (n : ℝ) (beta : Fin 3→ℝ) : gaugeFirstSymbol n beta=
    -(fun x => ∑ i : Fin 3,∑ j : Fin 3,gaugeMixMatrix n beta x i j*gaugeContractionSymbol i j x) := rfl

theorem scalarFirst_smooth (n : ℝ) (beta : Fin 3→ℝ) (time : TimeBox n beta) : SmoothSymbol (scalarFirstSymbol n beta) := by
  rw [scalarFirst_formula]
  exact (ContDiffOn.sum (fun i _ => ((scalar_weight_smooth n beta (time_positive n beta time).1.ne').mul
    (actual_shift_smooth n beta time 0 i)).mul (scalarContraction_smooth i))).neg

theorem gaugeFirst_smooth (n : ℝ) (beta : Fin 3→ℝ) (time : TimeBox n beta) : SmoothSymbol (gaugeFirstSymbol n beta) := by
  rw [gaugeFirst_formula]
  exact (ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
    (matrix_product_smooth _ _ (electric_smooth n beta time) (actual_mixed_smooth n beta) i j).mul
      (gaugeContraction_smooth i j)))).neg

theorem scalarFirst_budget (n : ℝ) (beta : Fin 3→ℝ) (time : TimeBox n beta)
    (M : ℕ) (x : Phase) (hx : x∈poleDomain) (box : PreparationVacuumCoframeBudget.sourceBox x)
    (annulus : (∑ i : Fin 100,(x.2 i)^2) ≤ 4) (input : CoefficientInputs x M) :
    FiniteBound (scalarFirstSymbol n beta) M scalarFirstArray x := by
  have closed := PreparationPhaseScalar.closed_box_outer x.1 box
  have smooth (i : Fin 3) : SmoothSymbol (fun y => (PreparationVacuumRationalW.scalarWeight n beta y*actualShift n beta y 0 i)*scalarContractionSymbol i y) :=
    ((scalar_weight_smooth n beta (time_positive n beta time).1.ne').mul
      (actual_shift_smooth n beta time 0 i)).mul (scalarContraction_smooth i)
  have entry (i : Fin 3) : FiniteBound (fun y => (PreparationVacuumRationalW.scalarWeight n beta y*actualShift n beta y 0 i)*scalarContractionSymbol i y) M
      (productArray (productArray scalarWArray shiftArray) (productArray scalarMomentumArray UiArray)) x := by
    have left := finite_product (PreparationVacuumRationalW.scalarWeight n beta) (fun y => actualShift n beta y 0 i)
      (scalar_weight_smooth n beta (time_positive n beta time).1.ne') (actual_shift_smooth n beta time 0 i)
      scalarWArray shiftArray (fun m => by unfold scalarWArray; positivity) M x hx
      (fun m hm w => scalar_weight_budget n beta time m w x box)
      (fun m hm w => rect_entry (actual_shift_budget n beta time M x box m hm w) 0 i)
    exact finite_product _ _ ((scalar_weight_smooth n beta (time_positive n beta time).1.ne').mul
      (actual_shift_smooth n beta time 0 i)) (scalarContraction_smooth i) _ _
      (productArray_nonnegative _ _ (fun m => by unfold scalarWArray; positivity) (fun m => Nat.cast_nonneg _)) M x hx left
      (scalarContraction_budget i M x hx closed annulus input)
  rw [scalarFirst_formula]
  have summed := finite_sum Finset.univ _ (fun i _ => smooth i)
    (fun _ => productArray (productArray scalarWArray shiftArray) (productArray scalarMomentumArray UiArray)) M x hx (fun i _ => entry i)
  have bound : FiniteBound (fun y => ∑ i : Fin 3,(PreparationVacuumRationalW.scalarWeight n beta y*actualShift n beta y 0 i)*scalarContractionSymbol i y) M scalarFirstArray x := by
    intro m hm w
    have h := summed m hm w
    exact h.trans_eq (by simp [scalarFirstArray,Finset.sum_const,nsmul_eq_mul])
  exact finite_neg _ (ContDiffOn.sum (fun i _ => smooth i)) _ M x hx bound

theorem gaugeFirst_budget (n : ℝ) (beta : Fin 3→ℝ) (time : TimeBox n beta)
    (M : ℕ) (x : Phase) (hx : x∈poleDomain) (box : PreparationVacuumCoframeBudget.sourceBox x)
    (annulus : (∑ i : Fin 100,(x.2 i)^2) ≤ 4) (input : CoefficientInputs x M) :
    FiniteBound (gaugeFirstSymbol n beta) M gaugeFirstArray x := by
  have closed := PreparationPhaseScalar.closed_box_outer x.1 box
  have mix := finite_matrix_product (electricMatrix n beta) (actualMixed n beta)
    (electric_smooth n beta time) (actual_mixed_smooth n beta) M electricBudget mixedArray
    (fun m => Nat.cast_nonneg _) (fun m => Nat.cast_nonneg _) x hx
    (electricMatrix_budget n beta time M x box) (actual_mixed_budget n beta time M x box)
  have smooth (i j : Fin 3) : SmoothSymbol (fun y => gaugeMixMatrix n beta y i j*gaugeContractionSymbol i j y) :=
    (matrix_product_smooth _ _ (electric_smooth n beta time) (actual_mixed_smooth n beta) i j).mul
      (gaugeContraction_smooth i j)
  have entry (i j : Fin 3) : FiniteBound (fun y => gaugeMixMatrix n beta y i j*gaugeContractionSymbol i j y) M
      (productArray (productArray electricBudget mixedArray) (productArray gaugeMomentumArray magneticFieldArray)) x :=
    finite_product _ _ (matrix_product_smooth _ _ (electric_smooth n beta time) (actual_mixed_smooth n beta) i j)
      (gaugeContraction_smooth i j) _ _ (productArray_nonnegative _ _ (fun m => Nat.cast_nonneg _) (fun m => Nat.cast_nonneg _))
      M x hx (fun m hm w => rect_entry (mix m hm w) i j) (gaugeContraction_budget i j M x hx closed annulus input)
  have row (i : Fin 3) := finite_sum Finset.univ _ (fun j _ => smooth i j)
    (fun _ => productArray (productArray electricBudget mixedArray) (productArray gaugeMomentumArray magneticFieldArray)) M x hx (fun j _ => entry i j)
  have total := finite_sum Finset.univ _ (fun i _ => ContDiffOn.sum (fun j _ => smooth i j))
    (fun _ m => ∑ j : Fin 3,productArray (productArray electricBudget mixedArray) (productArray gaugeMomentumArray magneticFieldArray) m)
    M x hx (fun i _ => row i)
  rw [gaugeFirst_formula]
  apply finite_neg _ (ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ => smooth i j))) _ M x hx
  intro m hm w
  have h := total m hm w
  exact h.trans_eq (by simp [gaugeFirstArray,Finset.sum_const,nsmul_eq_mul]; ring)


def actualFirstLeaves (j : Fin 13) : Symbol := fun x =>
  originalFirstLeaves (fullCoordinates.symm x.1) (nativeCovector x.2) (Fin.castSucc j)

theorem first_sample_formula (t : Fin 13) (x : Phase) (hx : x∈originalPhysicalPhase) :
    sampleSymbol actualFirstLeaves t x=scalarFirstSymbol N (pointShift t) x+gaugeFirstSymbol N (pointShift t) x := by
  change (∑ j : Fin 13,originalTemporalWeights N (pointShift t) j*
    originalFirstLeaves (fullCoordinates.symm x.1) (nativeCovector x.2) (Fin.castSucc j))=_
  rw [originalFirstTemporalReplay]
  exact (originalMixedHamiltonian_readback N (pointShift t) ⟨_,hx⟩ (nativeCovector x.2)
    (time_positive N (pointShift t) (actual_point_box t)).1.ne'
    (time_positive N (pointShift t) (actual_point_box t)).2.ne').symm

theorem firstSample_smooth (t : Fin 13) : SmoothSymbol (sampleSymbol actualFirstLeaves t) := by
  intro x hx
  have equal : sampleSymbol actualFirstLeaves t=ᶠ[𝓝 x]
      (fun y => scalarFirstSymbol N (pointShift t) y+gaugeFirstSymbol N (pointShift t) y) := by
    filter_upwards [originalPhysicalPhase_open.mem_nhds hx.1.1] with y hy
    exact first_sample_formula t y hy
  exact (((((scalarFirst_smooth N (pointShift t) (actual_point_box t)).add
    (gaugeFirst_smooth N (pointShift t) (actual_point_box t))) x hx).contDiffAt
      (poleDomain_open.mem_nhds hx)).congr_of_eventuallyEq equal).contDiffWithinAt

theorem firstSampleArray_nonnegative (m : ℕ) : 0 ≤ firstSampleArray m := by
  have sw : ∀ m,0 ≤ scalarWArray m := fun m => by unfold scalarWArray; positivity
  have sc : ∀ m,0 ≤ scalarMomentumArray m := productArray_nonnegative _ _ scalarFactor_nonnegative
    (affineArray_nonnegative 188 1 (by norm_num) (by norm_num))
  have gc : ∀ m,0 ≤ gaugeMomentumArray m := productArray_nonnegative _ _ gaugeFactor_nonnegative
    (affineArray_nonnegative 188 1 (by norm_num) (by norm_num))
  exact add_nonneg (mul_nonneg (by norm_num) (productArray_nonnegative _ _
    (productArray_nonnegative _ _ sw (fun m => Nat.cast_nonneg _))
    (productArray_nonnegative _ _ sc UiArray_nonnegative) m))
    (mul_nonneg (by norm_num) (productArray_nonnegative _ _
      (productArray_nonnegative _ _ (fun m => Nat.cast_nonneg _) (fun m => Nat.cast_nonneg _))
      (productArray_nonnegative _ _ gc magneticFieldArray_nonnegative) m))

def firstLeafArray (j : Fin 14) : ArrayBound := Fin.lastCases (fun _ => 0)
  (fun i m => (originalRowFactors i : ℝ)*firstSampleArray m) j

theorem firstLeafArray_nonnegative (j : Fin 14) (m : ℕ) : 0 ≤ firstLeafArray j m := by
  induction j using Fin.lastCases with
  | last => exact le_rfl
  | cast i =>
    simp only [firstLeafArray,Fin.lastCases_castSucc]
    exact mul_nonneg (Nat.cast_nonneg _) (firstSampleArray_nonnegative m)

theorem actual_first_leaf_budget (M : ℕ) (x : Phase) (hx : x∈poleDomain)
    (box : PreparationVacuumCoframeBudget.sourceBox x) (annulus : (∑ i : Fin 100,(x.2 i)^2) ≤ 4)
    (j : Fin 14) : FiniteBound (fun y => originalFirstLeaves (fullCoordinates.symm y.1) (nativeCovector y.2) j)
      M (firstLeafArray j) x := by
  have input := generatedCoefficientInputs x hx box M
  have sample (t : Fin 13) : FiniteBound (sampleSymbol actualFirstLeaves t) M firstSampleArray x := by
    have bound := finite_add _ _ (scalarFirst_smooth N (pointShift t) (actual_point_box t))
      (gaugeFirst_smooth N (pointShift t) (actual_point_box t)) scalarFirstArray gaugeFirstArray M x hx
      (scalarFirst_budget N (pointShift t) (actual_point_box t) M x hx box annulus input)
      (gaugeFirst_budget N (pointShift t) (actual_point_box t) M x hx box annulus input)
    intro m hm w
    have equal : PreparationVacuumCanonicalMoyal.jet m (sampleSymbol actualFirstLeaves t) w x=
        PreparationVacuumCanonicalMoyal.jet m (scalarFirstSymbol N (pointShift t)+gaugeFirstSymbol N (pointShift t)) w x := by
      apply PreparationVacuumCoframeBudget.jet_germ
      filter_upwards [originalPhysicalPhase_open.mem_nhds hx.1.1] with y hy
      exact first_sample_formula t y hy
    rw [equal]
    exact bound m hm w
  induction j using Fin.lastCases with
  | last =>
    have zero : (fun y : Phase => originalFirstLeaves (fullCoordinates.symm y.1) (nativeCovector y.2) (Fin.last 13))=
        (fun _ => 0) := by funext y; rfl
    rw [zero]
    have arr : firstLeafArray (Fin.last 13)=constantArray 0 := by
      change Fin.lastCases (motive:=fun _ : Fin 14 => ArrayBound) (fun _ => 0)
        (fun i m => (originalRowFactors i : ℝ)*firstSampleArray m) (Fin.last 13)=constantArray 0
      rw [Fin.lastCases_last]
      funext m
      simp [constantArray]
    rw [arr]
    exact finite_constant 0 0 (by simp) M x
  | cast i =>
    have arr : firstLeafArray i.castSucc=(fun m => (originalRowFactors i : ℝ)*firstSampleArray m) := by
      funext m
      simp [firstLeafArray]
    rw [arr]
    exact finite_reader_budget actualFirstLeaves firstSample_smooth firstSampleArray
      firstSampleArray_nonnegative M x hx sample i


open PreparationVacuumCoframeBudget

def sigmaColumn : RectSymbol 70 1 := fun x i _ => scalarLinear i x
def sigmaArray : ArrayBound := affineArray 915 1

theorem sigmaColumn_smooth : RectSmooth sigmaColumn := fun i _ => (scalarLinear i).contDiff.contDiffOn

theorem sigmaColumn_budget (M : ℕ) (x : Phase) (box : x.1∈sourceClosedBox) :
    MatrixBound sigmaColumn M sigmaArray x := by
  have total : ∀ m,∀ w : Word m,(∑ i : Fin 70,|PreparationVacuumCanonicalMoyal.jet m (scalarLinear i) w x|) ≤ sigmaArray m := by
    intro m w
    cases m with
    | zero => exact sourceScalar_box_L1 x box
    | succ m => cases m with
      | zero =>
        have one (i : Fin 70) : PreparationVacuumCanonicalMoyal.jet 1 (scalarLinear i) w x=scalarLinear i (PreparationVacuumCanonicalMoyal.slotDirection (w 0)) := linear_jet_one _ _ _
        simp only [one]
        exact sourceScalar_direction_L1 (w 0)
      | succ m =>
        have zero (i : Fin 70) : PreparationVacuumCanonicalMoyal.jet (m+2) (scalarLinear i) w x=0 := linear_jet_higher _ _ _ _
        simp only [zero,abs_zero,Finset.sum_const_zero,sigmaArray,affineArray,le_refl]
  intro m hm w
  exact ⟨fun i => by simpa only [sigmaColumn,Fin.sum_univ_one] using
    (Finset.single_le_sum (fun j _ => abs_nonneg (PreparationVacuumCanonicalMoyal.jet m (scalarLinear j) w x))
      (Finset.mem_univ i)).trans (total m w),fun j => total m w⟩

def sigmaNormSymbol : Symbol := fun x => inner ℝ (sourceScalar x) (sourceScalar x)

theorem sigmaNorm_matrix : sigmaNormSymbol=(fun x => ((sigmaColumn x)ᵀ*sigmaColumn x) 0 0) := by
  funext x
  exact scalar_inner_realified _ _

theorem sigmaNorm_smooth : SmoothSymbol sigmaNormSymbol := by
  rw [sigmaNorm_matrix]
  exact matrix_product_smooth _ _ (fun i j => sigmaColumn_smooth j i) sigmaColumn_smooth 0 0

theorem sigmaNorm_budget (M : ℕ) (x : Phase) (hx : x∈poleDomain) (box : x.1∈sourceClosedBox) :
    FiniteBound sigmaNormSymbol M (powerArray sigmaArray 2) x := by
  rw [sigmaNorm_matrix,powerArray_two]
  have bound := finite_matrix_product _ _ (fun i j => sigmaColumn_smooth j i) sigmaColumn_smooth
    M sigmaArray sigmaArray (affineArray_nonnegative 915 1 (by norm_num) (by norm_num))
    (affineArray_nonnegative 915 1 (by norm_num) (by norm_num)) x hx
    (finite_matrix_transpose _ _ _ _ (sigmaColumn_budget M x box)) (sigmaColumn_budget M x box)
  exact fun m hm w => rect_entry (bound m hm w) 0 0

def volumeBudget : ArrayBound := fun m => volumeArray m

theorem volumeSymbol_smooth : SmoothSymbol sourceVolume := by
  intro x hx
  exact (GaussNativeEnergy.volume_smooth.contDiffAt.comp x
    (fullCoordinates.symm.contDiff.contDiffAt.comp x contDiffAt_fst)).contDiffWithinAt

theorem determinant_budget (n : ℝ) (beta : Fin 3→ℝ) (time : TimeBox n beta)
    (M : ℕ) (x : Phase) (hx : x∈poleDomain) (box : sourceBox x) :
    FiniteBound (fun y => n*sourceVolume y) M (fun m => 2*volumeBudget m) x := by
  have bound := finite_scale n sourceVolume volumeSymbol_smooth volumeBudget M x hx
    (fun m hm w => actual_volume_budget m w x box)
  have nn : |n| ≤ 2 := by
    rw [abs_of_pos (time_positive n beta time).1]
    linarith [time.upper,N_bounds.2]
  exact finite_dominate _ _ _ M x bound (fun m => mul_le_mul_of_nonneg_right nn (Nat.cast_nonneg _))

def scalarClassicalExpression (n : ℝ) : Symbol := fun x =>
  n*sourceVolume x*sigmaNormSymbol x-(1/2 : ℝ)*
    ∑ i : Fin 3,∑ j : Fin 3,actualMetric n 0 x i j*scalarGramSymbol i j x

def scalarClassicalArray : ArrayBound := fun m =>
  productArray (fun k => 2*volumeBudget k) (powerArray sigmaArray 2) m+
    (9/2 : ℝ)*productArray metricArray (powerArray UiArray 2) m

theorem scalarClassical_smooth (n : ℝ) (beta : Fin 3→ℝ) (time : TimeBox n beta) :
    SmoothSymbol (scalarClassicalExpression n) :=
  ((contDiffOn_const.mul volumeSymbol_smooth).mul sigmaNorm_smooth).sub
    (contDiffOn_const.mul (ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
      (actual_metric_smooth n 0 (zeroShift_time n beta time) i j).mul (scalarGram_smooth i j)))))

theorem scalarClassical_budget (n : ℝ) (beta : Fin 3→ℝ) (time : TimeBox n beta)
    (M : ℕ) (x : Phase) (hx : x∈poleDomain) (box : sourceBox x) :
    FiniteBound (scalarClassicalExpression n) M scalarClassicalArray x := by
  have closed := PreparationPhaseScalar.closed_box_outer x.1 box
  have potential := finite_product (fun y => n*sourceVolume y) sigmaNormSymbol
    (contDiffOn_const.mul volumeSymbol_smooth) sigmaNorm_smooth (fun m => 2*volumeBudget m) (powerArray sigmaArray 2)
    (fun m => mul_nonneg (by norm_num) (Nat.cast_nonneg _)) M x hx (determinant_budget n beta time M x hx box)
    (sigmaNorm_budget M x hx closed)
  have smooth (i j : Fin 3) : SmoothSymbol (fun y => actualMetric n 0 y i j*scalarGramSymbol i j y) :=
    (actual_metric_smooth n 0 (zeroShift_time n beta time) i j).mul (scalarGram_smooth i j)
  have term (i j : Fin 3) := finite_product (fun y => actualMetric n 0 y i j) (scalarGramSymbol i j)
    (actual_metric_smooth n 0 (zeroShift_time n beta time) i j) (scalarGram_smooth i j)
    metricArray (powerArray UiArray 2) (fun m => Nat.cast_nonneg _) M x hx
    (fun m hm w => rect_entry (actual_metric_budget n 0 (zeroShift_time n beta time) M x box m hm w) i j)
    (scalarGram_budget i j M x hx closed)
  have row (i : Fin 3) := finite_sum Finset.univ _ (fun j _ => smooth i j)
    (fun _ => productArray metricArray (powerArray UiArray 2)) M x hx (fun j _ => term i j)
  have total := finite_sum Finset.univ _ (fun i _ => ContDiffOn.sum (fun j _ => smooth i j))
    (fun _ m => ∑ j : Fin 3,productArray metricArray (powerArray UiArray 2) m) M x hx (fun i _ => row i)
  have scaled := finite_scale (1/2 : ℝ) _ (ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ => smooth i j)))
    _ M x hx total
  have main := finite_sub _ _ ((contDiffOn_const.mul volumeSymbol_smooth).mul sigmaNorm_smooth)
    (contDiffOn_const.mul (ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ => smooth i j))))
    _ _ M x hx potential scaled
  intro m hm w
  have h := main m hm w
  exact h.trans_eq (by simp [scalarClassicalArray,Finset.sum_const,nsmul_eq_mul]; ring)


private theorem finite_matrix_sub {a b : ℕ} (F G : RectSymbol a b) (fs : RectSmooth F) (gs : RectSmooth G)
    (M : ℕ) (B D : ArrayBound) (x : Phase) (hx : x∈poleDomain)
    (fb : MatrixBound F M B x) (gb : MatrixBound G M D x) :
    MatrixBound (fun y => F y-G y) M (fun m => B m+D m) x := by
  intro m hm w
  have equal (i : Fin a) (j : Fin b) : PreparationVacuumCanonicalMoyal.jet m (fun y => (F y-G y) i j) w x=
      PreparationVacuumCanonicalMoyal.jet m (fun y => F y i j) w x-PreparationVacuumCanonicalMoyal.jet m (fun y => G y i j) w x := by
    have same : (fun y => (F y-G y) i j)=((fun y => F y i j)-(fun y => G y i j)) := rfl
    rw [same]
    unfold PreparationVacuumCanonicalMoyal.jet
    rw [iteratedFDeriv_sub_apply
      (((fs i j x hx).contDiffAt (poleDomain_open.mem_nhds hx)).of_le (by exact_mod_cast (ENat.natCast_lt_top m).le))
      (((gs i j x hx).contDiffAt (poleDomain_open.mem_nhds hx)).of_le (by exact_mod_cast (ENat.natCast_lt_top m).le))]
    rfl
  simp only [equal]
  have triangle (u v : ℝ) : |u-v| ≤ |u|+|v| := by
    simpa only [sub_zero,zero_sub,abs_neg] using (abs_sub_le u (0 : ℝ) v)
  constructor
  · intro i
    exact (Finset.sum_le_sum (fun j _ => triangle _ _)).trans
      ((Finset.sum_add_distrib).trans_le (add_le_add ((fb m hm w).1 i) ((gb m hm w).1 i)))
  · intro j
    exact (Finset.sum_le_sum (fun i _ => triangle _ _)).trans
      ((Finset.sum_add_distrib).trans_le (add_le_add ((fb m hm w).2 j) ((gb m hm w).2 j)))

def magneticSchurMatrix (n : ℝ) (beta : Fin 3→ℝ) : RectSymbol 3 3 := fun x =>
  (actualMixed n beta x)ᵀ*electricMatrix n beta x*actualMixed n beta x-actualMagnetic n beta x

def magneticSchurArray : ArrayBound := fun m =>
  productArray (productArray mixedArray electricBudget) mixedArray m+magneticMetricArray m

theorem magneticSchur_smooth (n : ℝ) (beta : Fin 3→ℝ) (time : TimeBox n beta) :
    RectSmooth (magneticSchurMatrix n beta) := by
  intro i j
  exact (matrix_product_smooth _ _
    (matrix_product_smooth _ _ (fun i j => actual_mixed_smooth n beta j i) (electric_smooth n beta time))
    (actual_mixed_smooth n beta) i j).sub (actual_magnetic_smooth n beta i j)

theorem magneticSchur_budget (n : ℝ) (beta : Fin 3→ℝ) (time : TimeBox n beta)
    (M : ℕ) (x : Phase) (hx : x∈poleDomain) (box : sourceBox x) :
    MatrixBound (magneticSchurMatrix n beta) M magneticSchurArray x := by
  have left := finite_matrix_product (fun y => (actualMixed n beta y)ᵀ) (electricMatrix n beta)
    (fun i j => actual_mixed_smooth n beta j i) (electric_smooth n beta time) M mixedArray electricBudget
    (fun m => Nat.cast_nonneg _) (fun m => Nat.cast_nonneg _) x hx
    (finite_matrix_transpose _ _ _ _ (actual_mixed_budget n beta time M x box)) (electricMatrix_budget n beta time M x box)
  have both := finite_matrix_product _ (actualMixed n beta)
    (matrix_product_smooth _ _ (fun i j => actual_mixed_smooth n beta j i) (electric_smooth n beta time))
    (actual_mixed_smooth n beta) M (productArray mixedArray electricBudget) mixedArray
    (productArray_nonnegative _ _ (fun m => Nat.cast_nonneg _) (fun m => Nat.cast_nonneg _))
    (fun m => Nat.cast_nonneg _) x hx left (actual_mixed_budget n beta time M x box)
  exact finite_matrix_sub _ _ (matrix_product_smooth _ _
    (matrix_product_smooth _ _ (fun i j => actual_mixed_smooth n beta j i) (electric_smooth n beta time))
    (actual_mixed_smooth n beta)) (actual_magnetic_smooth n beta) M _ _ x hx both
    (actual_magnetic_budget n beta time M x box)

def gaugeClassicalExpression (n : ℝ) (beta : Fin 3→ℝ) : Symbol := fun x =>
  (1/2 : ℝ)*∑ i : Fin 3,∑ j : Fin 3,magneticSchurMatrix n beta x i j*magneticGramSymbol i j x

def gaugeClassicalArray : ArrayBound := fun m => (9/2 : ℝ)*productArray magneticSchurArray magneticGramArray m

theorem gaugeClassical_smooth (n : ℝ) (beta : Fin 3→ℝ) (time : TimeBox n beta) :
    SmoothSymbol (gaugeClassicalExpression n beta) :=
  contDiffOn_const.mul (ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
    (magneticSchur_smooth n beta time i j).mul (magneticGram_smooth i j))))

theorem gaugeClassical_budget (n : ℝ) (beta : Fin 3→ℝ) (time : TimeBox n beta)
    (M : ℕ) (x : Phase) (hx : x∈poleDomain) (box : sourceBox x) :
    FiniteBound (gaugeClassicalExpression n beta) M gaugeClassicalArray x := by
  have closed := PreparationPhaseScalar.closed_box_outer x.1 box
  have nonnegative (m : ℕ) : 0 ≤ magneticSchurArray m := add_nonneg
    (productArray_nonnegative _ _ (productArray_nonnegative _ _ (fun m => Nat.cast_nonneg _) (fun m => Nat.cast_nonneg _))
      (fun m => Nat.cast_nonneg _) m) (Nat.cast_nonneg _)
  have smooth (i j : Fin 3) : SmoothSymbol (fun y => magneticSchurMatrix n beta y i j*magneticGramSymbol i j y) :=
    (magneticSchur_smooth n beta time i j).mul (magneticGram_smooth i j)
  have term (i j : Fin 3) := finite_product (fun y => magneticSchurMatrix n beta y i j) (magneticGramSymbol i j)
    (magneticSchur_smooth n beta time i j) (magneticGram_smooth i j) magneticSchurArray magneticGramArray
    nonnegative M x hx (fun m hm w => rect_entry (magneticSchur_budget n beta time M x hx box m hm w) i j)
    (magneticGram_budget i j M x hx closed)
  have row (i : Fin 3) := finite_sum Finset.univ _ (fun j _ => smooth i j)
    (fun _ => productArray magneticSchurArray magneticGramArray) M x hx (fun j _ => term i j)
  have total := finite_sum Finset.univ _ (fun i _ => ContDiffOn.sum (fun j _ => smooth i j))
    (fun _ m => ∑ j : Fin 3,productArray magneticSchurArray magneticGramArray m) M x hx (fun i _ => row i)
  have scaled := finite_scale (1/2 : ℝ) _ (ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ => smooth i j))) _ M x hx total
  intro m hm w
  have h := scaled m hm w
  exact h.trans_eq (by simp [gaugeClassicalArray,Finset.sum_const,nsmul_eq_mul]; ring)


def classicalExpression (n : ℝ) (beta : Fin 3→ℝ) : Symbol := fun x =>
  scalarClassicalExpression n x+gaugeClassicalExpression n beta x+3*n*sourceVolume x

def classicalSampleArray : ArrayBound := fun m => scalarClassicalArray m+gaugeClassicalArray m+6*volumeBudget m

theorem classical_expression_source (n : ℝ) (beta : Fin 3→ℝ) (time : TimeBox n beta)
    (x : Phase) (physical : x∈originalPhysicalPhase) :
    actualTimeClassical n beta (fullCoordinates.symm x.1)=classicalExpression n beta x := by
  have det : (coframe (originalTimeColumn n beta) (fullCoordinates.symm x.1).1).det=n*sourceVolume x := by
    rw [coframe_determinant]
    norm_num [originalTimeColumn,sourceVolume,volume]
  have field : scalarField (fullCoordinates.symm x.1)-vacuum=sourceScalar x := by
    change vacuum+sourceScalar x-vacuum=sourceScalar x
    abel
  have potential : (n/sourceTime 0)*GaussCoframeForm.volumePotential (fullCoordinates.symm x.1)=3*n*sourceVolume x := by
    have nonzero : sourceTime 0≠0 := N_positive.ne'
    unfold GaussCoframeForm.volumePotential sourceVolume
    field_simp
  unfold actualTimeClassical
  rw [det,field,potential]
  simp_rw [scalarSchur_metric_zero n beta (time_positive n beta time).1.ne' x physical]
  rfl

theorem classicalExpression_smooth (n : ℝ) (beta : Fin 3→ℝ) (time : TimeBox n beta) :
    SmoothSymbol (classicalExpression n beta) :=
  ((scalarClassical_smooth n beta time).add (gaugeClassical_smooth n beta time)).add (contDiffOn_const.mul volumeSymbol_smooth)

theorem classicalExpression_budget (n : ℝ) (beta : Fin 3→ℝ) (time : TimeBox n beta)
    (M : ℕ) (x : Phase) (hx : x∈poleDomain) (box : sourceBox x) :
    FiniteBound (classicalExpression n beta) M classicalSampleArray x := by
  have scaled := finite_scale 3 (fun y => n*sourceVolume y) (contDiffOn_const.mul volumeSymbol_smooth)
    (fun m => 2*volumeBudget m) M x hx (determinant_budget n beta time M x hx box)
  have third : FiniteBound (fun y => 3*n*sourceVolume y) M (fun m => 6*volumeBudget m) x := by
    simpa only [abs_of_pos (by norm_num : (0 : ℝ)<3),←mul_assoc,show (3 : ℝ)*2=6 by norm_num] using scaled
  exact finite_add _ _ ((scalarClassical_smooth n beta time).add (gaugeClassical_smooth n beta time))
    (contDiffOn_const.mul volumeSymbol_smooth) _ _ M x hx
    (finite_add _ _ (scalarClassical_smooth n beta time) (gaugeClassical_smooth n beta time) _ _ M x hx
      (scalarClassical_budget n beta time M x hx box) (gaugeClassical_budget n beta time M x hx box)) third

theorem classicalSampleArray_nonnegative (m : ℕ) : 0 ≤ classicalSampleArray m := by
  have volume : ∀ m,0 ≤ volumeBudget m := fun m => Nat.cast_nonneg _
  have metric : ∀ m,0 ≤ metricArray m := fun m => Nat.cast_nonneg _
  have mixed : ∀ m,0 ≤ mixedArray m := fun m => Nat.cast_nonneg _
  have electric : ∀ m,0 ≤ electricBudget m := fun m => Nat.cast_nonneg _
  have schur : ∀ m,0 ≤ magneticSchurArray m := fun m => add_nonneg
    (productArray_nonnegative _ _ (productArray_nonnegative _ _ mixed electric) mixed m) (Nat.cast_nonneg _)
  have gram : ∀ m,0 ≤ magneticGramArray m := productArray_nonnegative _ _
    (productArray_nonnegative _ _ magneticFieldArray_nonnegative (constantArray_nonnegative 3 (by norm_num))) magneticFieldArray_nonnegative
  have scalar : 0 ≤ scalarClassicalArray m := add_nonneg
    (productArray_nonnegative _ _ (fun m => mul_nonneg (by norm_num) (volume m))
      (powerArray_nonnegative _ (affineArray_nonnegative 915 1 (by norm_num) (by norm_num)) 2) m)
    (mul_nonneg (by norm_num) (productArray_nonnegative _ _ metric (powerArray_nonnegative _ UiArray_nonnegative 2) m))
  have gauge : 0 ≤ gaugeClassicalArray m := mul_nonneg (by norm_num) (productArray_nonnegative _ _ schur gram m)
  exact add_nonneg (add_nonneg scalar gauge) (mul_nonneg (by norm_num) (volume m))

def actualClassicalLeaves (j : Fin 13) : Symbol := fun x => originalClassicalLeaves (fullCoordinates.symm x.1) j

theorem classical_sample_formula (t : Fin 13) (x : Phase) (hx : x∈originalPhysicalPhase) :
    sampleSymbol actualClassicalLeaves t x=classicalExpression N (pointShift t) x := by
  have source := actualTimeClassical_extraction N (pointShift t)
    (time_positive N (pointShift t) (actual_point_box t)).1.ne'
    (time_positive N (pointShift t) (actual_point_box t)).2.ne' ⟨_,hx⟩
  exact source.symm.trans (classical_expression_source N (pointShift t) (actual_point_box t) x hx)

theorem classicalSample_smooth (t : Fin 13) : SmoothSymbol (sampleSymbol actualClassicalLeaves t) := by
  intro x hx
  have equal : sampleSymbol actualClassicalLeaves t=ᶠ[𝓝 x]classicalExpression N (pointShift t) := by
    filter_upwards [originalPhysicalPhase_open.mem_nhds hx.1.1] with y hy
    exact classical_sample_formula t y hy
  exact (((classicalExpression_smooth N (pointShift t) (actual_point_box t) x hx).contDiffAt
    (poleDomain_open.mem_nhds hx)).congr_of_eventuallyEq equal).contDiffWithinAt

def classicalLeafArray (j : Fin 13) : ArrayBound := fun m => (originalRowFactors j : ℝ)*classicalSampleArray m

theorem classicalLeafArray_nonnegative (j : Fin 13) (m : ℕ) : 0 ≤ classicalLeafArray j m :=
  mul_nonneg (Nat.cast_nonneg _) (classicalSampleArray_nonnegative m)

theorem actual_classical_leaf_budget (M : ℕ) (x : Phase) (hx : x∈poleDomain)
    (box : sourceBox x) (j : Fin 13) :
    FiniteBound (fun y => originalClassicalLeaves (fullCoordinates.symm y.1) j) M (classicalLeafArray j) x := by
  have samples (t : Fin 13) : FiniteBound (sampleSymbol actualClassicalLeaves t) M classicalSampleArray x := by
    intro m hm w
    have equal : PreparationVacuumCanonicalMoyal.jet m (sampleSymbol actualClassicalLeaves t) w x=
        PreparationVacuumCanonicalMoyal.jet m (classicalExpression N (pointShift t)) w x := by
      apply PreparationVacuumCoframeBudget.jet_germ
      filter_upwards [originalPhysicalPhase_open.mem_nhds hx.1.1] with y hy
      exact classical_sample_formula t y hy
    rw [equal]
    exact classicalExpression_budget N (pointShift t) (actual_point_box t) M x hx box m hm w
  exact finite_reader_budget actualClassicalLeaves classicalSample_smooth classicalSampleArray
    classicalSampleArray_nonnegative M x hx samples j


theorem productArray_scale_right (c : ℝ) (B D : ArrayBound) :
    productArray B (fun m => c*D m)=(fun m => c*productArray B D m) := by
  rw [productArray_comm,productArray_scale_left,productArray_comm D B]

theorem productArray_left_comm (A B D : ArrayBound) :
    productArray A (productArray B D)=productArray B (productArray A D) := by
  rw [←productArray_assoc,productArray_comm A B,productArray_assoc]

theorem productArray_add_left (A B D : ArrayBound) :
    productArray (fun m => A m+B m) D=(fun m => productArray A D m+productArray B D m) := by
  funext m
  simp only [productArray,mul_add,add_mul,Finset.sum_add_distrib]

theorem productArray_constant_right (B : ArrayBound) (c : ℝ) :
    productArray B (constantArray c)=(fun m => c*B m) := by
  have constant : constantArray c=(fun m => c*constantArray 1 m) := by
    funext m
    by_cases h : m=0 <;> simp [constantArray,h]
  rw [constant,productArray_scale_right,productArray_comm,productArray_one]

def originalScalarShiftArray : ArrayBound := fun m => 3*productArray shiftArray UiArray m
def originalGaugeShiftArray : ArrayBound := fun m => 108*productArray mixedArray magneticFieldArray m

def originalScalarFirstArray : ArrayBound := productArray
  (productArray (productArray p94Array scalarFactorArray) scalarWArray) originalScalarShiftArray

def originalGaugeFirstArray : ArrayBound := productArray
  (productArray (productArray p94Array gaugeFactorArray) (fun m => 2*electricBudget m)) originalGaugeShiftArray

def originalScalarClassicalArray : ArrayBound := fun m =>
  (1/2 : ℝ)*productArray scalarWArray (powerArray originalScalarShiftArray 2) m+scalarClassicalArray m

def originalGaugeClassicalArray : ArrayBound := fun m =>
  (1/2 : ℝ)*productArray (fun k => 2*electricBudget k) (powerArray originalGaugeShiftArray 2) m+
    54*productArray magneticMetricArray (powerArray magneticFieldArray 2) m

def gaugeFirstCore : ArrayBound := productArray (productArray electricBudget mixedArray)
  (productArray gaugeMomentumArray magneticFieldArray)

theorem scalar_first_original_array : scalarFirstArray=originalScalarFirstArray := by
  unfold scalarFirstArray originalScalarFirstArray originalScalarShiftArray scalarMomentumArray
  rw [productArray_scale_right]
  simp only [productArray_comm,productArray_left_comm]

theorem gauge_first_original_array : originalGaugeFirstArray=(fun m => 216*gaugeFirstCore m) := by
  unfold originalGaugeFirstArray originalGaugeShiftArray gaugeFirstCore gaugeMomentumArray
  rw [productArray_scale_right,productArray_scale_right,productArray_scale_left]
  simp only [productArray_comm,productArray_left_comm]
  funext m
  ring

theorem original_first_admission (m : ℕ) : firstSampleArray m ≤ originalScalarFirstArray m+originalGaugeFirstArray m := by
  have gp : ∀ m,0 ≤ gaugeMomentumArray m := productArray_nonnegative _ _ gaugeFactor_nonnegative
    (affineArray_nonnegative 188 1 (by norm_num) (by norm_num))
  have core := productArray_nonnegative _ _ (productArray_nonnegative _ _
    (fun m => (Nat.cast_nonneg _ : (0 : ℝ) ≤ electricBudget m))
    (fun m => (Nat.cast_nonneg _ : (0 : ℝ) ≤ mixedArray m)))
    (productArray_nonnegative _ _ gp magneticFieldArray_nonnegative) m
  change 0 ≤ gaugeFirstCore m at core
  rw [firstSampleArray,scalar_first_original_array,gauge_first_original_array]
  change _+9*gaugeFirstCore m ≤ _+216*gaugeFirstCore m
  linarith

def gaugeQuadraticCore : ArrayBound := productArray electricBudget
  (productArray (powerArray mixedArray 2) (powerArray magneticFieldArray 2))
def gaugeMagneticCore : ArrayBound := productArray magneticMetricArray (powerArray magneticFieldArray 2)

theorem magneticGram_original_array : magneticGramArray=(fun m => 3*powerArray magneticFieldArray 2 m) := by
  unfold magneticGramArray
  rw [productArray_constant_right,productArray_scale_left,powerArray_two]

theorem gauge_classical_generated_array : gaugeClassicalArray=(fun m =>
    (27/2 : ℝ)*gaugeQuadraticCore m+(27/2 : ℝ)*gaugeMagneticCore m) := by
  unfold gaugeClassicalArray magneticSchurArray gaugeQuadraticCore gaugeMagneticCore
  rw [magneticGram_original_array,productArray_scale_right,productArray_add_left]
  simp only [powerArray_two,productArray_comm,productArray_left_comm]
  funext m
  ring

theorem gauge_classical_original_array : originalGaugeClassicalArray=(fun m =>
    11664*gaugeQuadraticCore m+54*gaugeMagneticCore m) := by
  unfold originalGaugeClassicalArray originalGaugeShiftArray gaugeQuadraticCore gaugeMagneticCore
  simp only [powerArray_two,productArray_scale_left,productArray_scale_right]
  simp only [productArray_comm,productArray_left_comm]
  funext m
  ring

theorem original_classical_admission (m : ℕ) : classicalSampleArray m ≤
    originalScalarClassicalArray m+originalGaugeClassicalArray m+6*volumeBudget m := by
  have mixed : ∀ m,0 ≤ mixedArray m := fun m => Nat.cast_nonneg _
  have electric : ∀ m,0 ≤ electricBudget m := fun m => Nat.cast_nonneg _
  have shift : ∀ m,0 ≤ originalScalarShiftArray m := fun m => mul_nonneg (by norm_num)
    (productArray_nonnegative _ _ (fun m => Nat.cast_nonneg _) UiArray_nonnegative m)
  have scalarExtra := productArray_nonnegative scalarWArray (powerArray originalScalarShiftArray 2)
    (fun m => by unfold scalarWArray; positivity) (powerArray_nonnegative _ shift 2) m
  have H := productArray_nonnegative _ _ electric (productArray_nonnegative _ _
    (powerArray_nonnegative _ mixed 2) (powerArray_nonnegative _ magneticFieldArray_nonnegative 2)) m
  have J := productArray_nonnegative _ _ (fun m => (Nat.cast_nonneg _ : (0 : ℝ) ≤ magneticMetricArray m))
    (powerArray_nonnegative _ magneticFieldArray_nonnegative 2) m
  rw [classicalSampleArray,gauge_classical_generated_array,gauge_classical_original_array]
  unfold originalScalarClassicalArray
  change 0 ≤ gaugeQuadraticCore m at H
  change 0 ≤ gaugeMagneticCore m at J
  nlinarith

end LowEnergy.PreparationVacuumLowerClassical
