import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationClockBudgetSquare
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationMatrixInverseWords

set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumClockBudget
open PreparationVacuumCentralBudget PreparationVacuumEngineBudget PreparationVacuumCanonicalMoyal
open PreparationVacuumClockSymbol PreparationVacuumClockJacobian PreparationVacuumClockPole
open PreparationVacuumClockGuard PreparationVacuumReciprocalBudget PreparationVacuumEngineSmooth
open PreparationActualFactor PreparationScalarCoordinates PreparationPhaseSource PreparationPhaseBounds
open PreparationVacuumMoyalSymmetry PreparationVacuumMoyalBudget
open PreparationVacuumMatrixBudget PreparationVacuumEnergyTail PreparationVacuumEngineSource
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff GaussNativeEnergy
open scoped BigOperators ContDiff Topology Matrix

private theorem canonical_word {m : ℕ} (w : Word m) :
    PreparationVacuumReciprocalBudget.CanonicalList (List.ofFn (slotDirection∘w)) := by
  intro v hv
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
  exact ⟨w i,rfl⟩

theorem actual_A_inverse_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ) (input : ATInputs (z,WithLp.toLp 2 u) N) :
    FiniteBound (fun y => (actualA y)⁻¹) N (aInverseArray input) (z,WithLp.toLp 2 u) := by
  let M : MatrixSymbol 1 := fun y _ _ => actualA y
  let I : MatrixSymbol 1 := fun y _ _ => (actualA y)⁻¹
  have ms : SmoothMatrix poleDomain M := fun _ _ y hy => (actualA_smooth y hy.1.1).contDiffWithinAt
  have smooth : SmoothSymbol (fun y => (actualA y)⁻¹) := fun y hy =>
    ((actualA_smooth y hy.1.1).inv hy.1.2.1.ne').contDiffWithinAt
  have ins : SmoothMatrix poleDomain I := fun _ _ => smooth
  have identity : ∀ y∈poleDomain,M y*I y=1 := by
    intro y hy
    ext i j
    fin_cases i
    fin_cases j
    simpa [M,I,Matrix.mul_apply] using mul_inv_cancel₀ (show actualA y≠0 from hy.1.2.1.ne')
  have reverse : I (z,WithLp.toLp 2 u)*M (z,WithLp.toLp 2 u)=1 := by
    have hx := sourceUnit_admitted z u zbox ubox unit
    ext i j
    fin_cases i
    fin_cases j
    simpa [M,I,Matrix.mul_apply] using inv_mul_cancel₀ (show actualA (z,WithLp.toLp 2 u)≠0 from hx.1.2.1.ne')
  have base : RowColumnBound (I (z,WithLp.toLp 2 u)) 15 := by
    constructor <;> intro i <;> simpa [I] using actual_A_inverse_zero z u zbox ubox unit
  have bounds : ∀ m ≤ N,∀ w : Word m,
      RowColumnBound (fun i j => jet m (fun y => M y i j) w (z,WithLp.toLp 2 u)) (input.A m) := by
    intro m hm w
    constructor <;> intro i <;> simpa [M] using input.A_bound m hm w
  intro m hm w
  have result := matrix_inverse_list_budget poleDomain_open M I ms ins identity _
    (sourceUnit_admitted z u zbox ubox unit) reverse input.A N 15 (by norm_num)
    input.A_nonnegative base bounds m hm (List.ofFn (slotDirection∘w)) (canonical_word w) List.length_ofFn
  have entry := entry_bound result 0 0
  change |listJet (List.ofFn (slotDirection∘w)) (fun y => (actualA y)⁻¹) (z,WithLp.toLp 2 u)| ≤ _ at entry
  rw [listJet_ofFn poleDomain_open smooth m _ _ (sourceUnit_admitted z u zbox ubox unit)] at entry
  exact entry

theorem actual_ratio_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ) (input : ATInputs (z,WithLp.toLp 2 u) N) :
    FiniteBound actualRatio N (ratioArray input) (z,WithLp.toLp 2 u) := by
  have ts : SmoothSymbol actualT := fun y hy => (actualT_smooth y hy.1.1).contDiffWithinAt
  have ais : SmoothSymbol (fun y => (actualA y)⁻¹) := fun y hy =>
    ((actualA_smooth y hy.1.1).inv hy.1.2.1.ne').contDiffWithinAt
  have hx := sourceUnit_admitted z u zbox ubox unit
  have prod := finite_product actualT (fun y => (actualA y)⁻¹) ts ais input.T (aInverseArray input)
    input.T_nonnegative N _ hx input.T_bound (actual_A_inverse_budget z u zbox ubox unit N input)
  have scaled := finite_scale (1/2 : ℝ) _ (ts.mul ais) _ N _ hx prod
  have same : actualRatio=(fun y => (1/2 : ℝ)*(actualT y*(actualA y)⁻¹)) := by
    funext y
    unfold actualRatio
    ring
  rw [same]
  intro m hm w
  simpa only [ratioArray,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)] using scaled m hm w

def cArray {x : SourcePhase} {N : ℕ} (input : ATInputs x N) : ArrayBound :=
  clockArray (ratioArray input) (inverseClockZero input)
def ciArray {x : SourcePhase} {N : ℕ} (input : ATInputs x N) : ArrayBound :=
  inverseBudget (cArray input) (inverseClockZero input)

theorem cArray_nonnegative {x : SourcePhase} {N : ℕ} (input : ATInputs x N) : ∀ m,0 ≤ cArray input m :=
  clockArray_nonnegative _ _ (ratioArray_nonnegative input) ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _))

theorem actual_C_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ) (input : ATInputs (z,WithLp.toLp 2 u) N) :
    FiniteBound actualC N (cArray input) (z,WithLp.toLp 2 u) :=
  actual_clock_canonical_budget z u zbox ubox unit N input (actual_ratio_budget z u zbox ubox unit N input)

theorem actual_C_inverse_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ) (input : ATInputs (z,WithLp.toLp 2 u) N) :
    FiniteBound (fun y => (actualC y)⁻¹) N (ciArray input) (z,WithLp.toLp 2 u) :=
  primitive_inverse_canonical_budget 0 _ (sourceUnit_admitted z u zbox ubox unit) (cArray input) N
    (inverseClockZero input) ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _))
    (cArray_nonnegative input) (actual_inverseClock_zero z u zbox ubox unit N input)
    (actual_C_budget z u zbox ubox unit N input)

structure QInputs (x : SourcePhase) (N : ℕ) where
  Q : ArrayBound
  nonnegative : ∀ n,0 ≤ Q n
  bounds : ∀ m ≤ N,∀ w : Word m,
    RowColumnBound (fun i j => jet m (fun y => sourceM y i j) w x) (Q m)

theorem actual_Q_inverse_list_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ) (input : QInputs (z,WithLp.toLp 2 u) N)
    (m : ℕ) (hm : m ≤ N) (vs : List Phase)
    (canonical : PreparationVacuumReciprocalBudget.CanonicalList vs) (length : vs.length=m) :
    RowColumnBound (matrixListJet vs (fun y => (sourceM y)⁻¹) (z,WithLp.toLp 2 u))
      (inverseBudget input.Q 45 m) := by
  have hx := sourceUnit_admitted z u zbox ubox unit
  apply matrix_inverse_list_budget poleDomain_open sourceM (fun y => (sourceM y)⁻¹)
    (fun i j y hy => (sourceM_entry_smooth y hy.1.1 i j).contDiffWithinAt)
    (fun i j y hy => (sourceM_inverse_smooth y hy i j).contDiffWithinAt)
    (fun y hy => Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hy.2)) _ hx
    (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hx.2)) input.Q N 45
    (by norm_num) input.nonnegative ?_ input.bounds m hm vs canonical length
  constructor
  · intro i
    simpa [sourceM,actualT,actualS,nativePhase,clockMatrix] using (actual_M_inverse_matrix_budget_j15 z u zbox ubox i).1
  · intro i
    simpa [sourceM,actualT,actualS,nativePhase,clockMatrix] using (actual_M_inverse_matrix_budget_j15 z u zbox ubox i).2

def diagonalSymbol (f : RealSymbol) : MatrixSymbol 4 := fun y => Matrix.diagonal (fun _ => f y)
def blockSymbol : MatrixSymbol 4 := fun y a b =>
  Fin.cases (Fin.cases ((actualT y)⁻¹) (fun _ => 0))
    (fun i => Fin.cases 0 (fun j => (sourceM y)⁻¹ i j)) a b

private theorem listJet_zero (vs : List Phase) : listJet vs (fun _ => (0 : ℝ))=fun _ => 0 := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change (fun x => fderiv ℝ (listJet vs (fun _ => (0 : ℝ))) x v)=fun _ => 0
    rw [ih]
    funext x
    simp

private theorem diagonal_jet (vs : List Phase) (f : RealSymbol) (x : Phase) :
    matrixListJet vs (diagonalSymbol f) x=Matrix.diagonal (fun _ => listJet vs f x) := by
  ext i j
  by_cases eq : i=j
  · subst j; simp [matrixListJet,diagonalSymbol]
  · simp [matrixListJet,diagonalSymbol,eq,listJet_zero]

private theorem diagonal_bound (vs : List Phase) (f : RealSymbol) (x : Phase) (B : ℝ)
    (bound : |listJet vs f x| ≤ B) : RowColumnBound (matrixListJet vs (diagonalSymbol f) x) B := by
  rw [diagonal_jet]
  constructor <;> intro i <;> simpa [Matrix.diagonal_apply,apply_ite,abs_zero,Finset.sum_ite_eq,Finset.sum_ite_eq'] using bound

private theorem block_smooth : SmoothMatrix poleDomain blockSymbol := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun _ => contDiffOn_const) j
    exact fun y hy => ((actualT_smooth y hy.1.1).inv hy.1.2.2.ne').contDiffWithinAt
  · refine Fin.cases contDiffOn_const (fun j => ?_) j
    exact fun y hy => (sourceM_inverse_smooth y hy i j).contDiffWithinAt

private theorem block_bound (vs : List Phase) (x : Phase) (t q : ℝ) (tp : 0 ≤ t) (qp : 0 ≤ q)
    (tb : |listJet vs (fun y => (actualT y)⁻¹) x| ≤ t)
    (qb : RowColumnBound (matrixListJet vs (fun y => (sourceM y)⁻¹) x) q) :
    RowColumnBound (matrixListJet vs blockSymbol x) (t+q) := by
  constructor
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [matrixListJet,blockSymbol,Fin.sum_univ_succ,listJet_zero] using tb.trans (le_add_of_nonneg_right qp)
    · simpa [matrixListJet,blockSymbol,Fin.sum_univ_succ,listJet_zero] using (qb.1 i).trans (le_add_of_nonneg_left tp)
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa [matrixListJet,blockSymbol,Fin.sum_univ_succ,listJet_zero] using tb.trans (le_add_of_nonneg_right qp)
    · simpa [matrixListJet,blockSymbol,Fin.sum_univ_succ,listJet_zero] using (qb.2 j).trans (le_add_of_nonneg_left tp)

private theorem diagonal_block_source (y : Phase) :
    diagonalSymbol (fun y => -actualC y^3) y*blockSymbol y=sourceInverse y := by
  ext i j
  change (Matrix.diagonal (fun _ : Fin 4 => -actualC y^3)*blockSymbol y) i j=_
  rw [Matrix.diagonal_mul]
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [blockSymbol,sourceInverse,div_eq_mul_inv]
    · simp [blockSymbol,sourceInverse]
  · refine Fin.cases ?_ (fun j => ?_) j <;> simp [blockSymbol,sourceInverse]

def jInverseArray {x : SourcePhase} {N : ℕ} (input : ATInputs x N) (q : QInputs x N) : ArrayBound :=
  productArray (powerArray (cArray input) 3) (fun m => inverseBudget input.T 15 m+inverseBudget q.Q 45 m)

theorem actual_J_inverse_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ) (input : ATInputs (z,WithLp.toLp 2 u) N)
    (q : QInputs (z,WithLp.toLp 2 u) N) (m : ℕ) (hm : m ≤ N) (w : Word m) :
    RowColumnBound (fun i j => jet m (fun y => (principalForceJacobian y)⁻¹ i j) w (z,WithLp.toLp 2 u))
      (jInverseArray input q m) := by
  let x : Phase := (z,WithLp.toLp 2 u)
  let vs := List.ofFn (slotDirection∘w)
  have hx := sourceUnit_admitted z u zbox ubox unit
  have cs : SmoothSymbol actualC := fun y hy => (actualC_smooth y hy.1).contDiffWithinAt
  have fs : SmoothSymbol (fun y => -actualC y^3) := (cs.pow 3).neg
  have fb : FiniteBound (fun y => -actualC y^3) N (powerArray (cArray input) 3) x :=
    finite_neg _ (cs.pow 3) _ N x hx
      (finite_power actualC cs (cArray input) (cArray_nonnegative input) N x hx
        (actual_C_budget z u zbox ubox unit N input) 3)
  have ts : SmoothSymbol (fun y => (actualT y)⁻¹) := fun y hy =>
    ((actualT_smooth y hy.1.1).inv hy.1.2.2.ne').contDiffWithinAt
  have tb : FiniteBound (fun y => (actualT y)⁻¹) N (inverseBudget input.T 15) x :=
    actual_T_inverse_budget z u zbox ubox unit input.T N input.T_nonnegative input.T_bound
  have bp : ∀ n,0 ≤ powerArray (cArray input) 3 n := powerArray_nonnegative _ (cArray_nonnegative input) 3
  have tp : ∀ n,0 ≤ inverseBudget input.T 15 n := inverseBudget_nonnegative _ _ (by norm_num) input.T_nonnegative
  have qp : ∀ n,0 ≤ inverseBudget q.Q 45 n := inverseBudget_nonnegative _ _ (by norm_num) q.nonnegative
  have ds : SmoothMatrix poleDomain (diagonalSymbol (fun y => -actualC y^3)) := by
    intro i j
    by_cases h : i=j
    · subst j
      simp only [diagonalSymbol,Matrix.diagonal_apply_eq]
      exact fs
    · simpa [diagonalSymbol,Matrix.diagonal_apply,h] using (contDiffOn_const : SmoothSymbol (fun _ => (0 : ℝ)))
  have bound := matrixListJet_product_bound poleDomain_open (diagonalSymbol (fun y => -actualC y^3))
    blockSymbol ds block_smooth vs x hx (powerArray (cArray input) 3)
    (fun n => inverseBudget input.T 15 n+inverseBudget q.Q 45 n) bp (fun n => add_nonneg (tp n) (qp n))
    (fun s hs => diagonal_bound s.1 _ x _
      (finite_list_bound _ fs _ N x hx fb s.1 (canonicalList_splits (canonical_word w) s hs).1 (by
        have lens := wordSplittings_lengths vs s hs
        simp only [vs,List.length_ofFn] at lens
        omega)))
    (fun s hs => block_bound s.2 x _ _ (tp _) (qp _)
      (finite_list_bound _ ts _ N x hx tb s.2 (canonicalList_splits (canonical_word w) s hs).2 (by
        have lens := wordSplittings_lengths vs s hs
        simp only [vs,List.length_ofFn] at lens
        omega))
      (actual_Q_inverse_list_budget z u zbox ubox unit N q s.2.length (by
        have lens := wordSplittings_lengths vs s hs
        simp only [vs,List.length_ofFn] at lens
        omega) s.2 (canonicalList_splits (canonical_word w) s hs).2 rfl))
  have same : (fun y => diagonalSymbol (fun y => -actualC y^3) y*blockSymbol y)=sourceInverse :=
    funext diagonal_block_source
  rw [same] at bound
  have native : (fun y => (principalForceJacobian y)⁻¹)=ᶠ[𝓝 x]sourceInverse := by
    filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    exact sourceInverse_native y hy.1 hy.2
  have read : matrixListJet vs (fun y => (principalForceJacobian y)⁻¹) x=matrixListJet vs sourceInverse x :=
    matrixListJet_germ native vs
  rw [←read] at bound
  have jets : matrixListJet vs (fun y => (principalForceJacobian y)⁻¹) x=
      (fun i j => jet m (fun y => (principalForceJacobian y)⁻¹ i j) w x) := by
    ext i j
    change listJet (List.ofFn (slotDirection∘w)) _ x=_
    rw [listJet_ofFn poleDomain_open (fun y hy => ?_) m _ x hx]
    · rfl
    · exact ((sourceInverse_smooth y hy i j).congr_of_eventuallyEq
        (by
          filter_upwards [poleDomain_open.mem_nhds hy] with t ht
          exact congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i j) (sourceInverse_native t ht.1 ht.2))).contDiffWithinAt
  rw [jets] at bound
  simpa only [vs,List.length_ofFn,convolution,zero_add,productArray,jInverseArray] using bound

end LowEnergy.PreparationVacuumClockBudget
