import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationMatrixInverseWords
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceChartGuard

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMatrixBudget
open PreparationVacuumCanonicalMoyal PreparationVacuumMoyalSymmetry
open PreparationVacuumClockSymbol PreparationVacuumMoyalBudget PreparationVacuumReciprocalBudget
open scoped BigOperators ContDiff Topology Matrix

theorem determinant_smooth {n : ℕ} {U : Set Phase} (M : MatrixSymbol n)
    (hm : SmoothMatrix U M) : ContDiffOn ℝ ∞ (fun x=>(M x).det) U := by
  simp_rw [Matrix.det_apply']
  apply ContDiffOn.sum
  intro s _
  exact contDiffOn_const.mul (contDiffOn_prod (fun i _=>hm (s i) i))

theorem adjugate_smooth {n : ℕ} {U : Set Phase} (M : MatrixSymbol n)
    (hm : SmoothMatrix U M) (i j : Fin n) : ContDiffOn ℝ ∞ (fun x=>(M x).adjugate i j) U := by
  simp_rw [Matrix.adjugate_apply]
  apply determinant_smooth (fun x=>(M x).updateRow j (Pi.single i (1 : ℝ)))
  intro a b
  by_cases same : a=j
  · subst a
    simp only [Matrix.updateRow_self]
    exact contDiffOn_const
  · simpa only [Matrix.updateRow_ne same] using hm a b

theorem inverse_smooth {n : ℕ} {U : Set Phase} (M : MatrixSymbol n)
    (hm : SmoothMatrix U M) (regular : ∀ x∈U,(M x).det≠0) :
    SmoothMatrix U (fun x=>(M x)⁻¹) := by
  intro i j
  simp_rw [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
  exact ((determinant_smooth M hm).inv regular).mul (adjugate_smooth M hm i j)

theorem matrix_inverse_canonical_budget {n : ℕ} {U : Set Phase} (openU : IsOpen U)
    (M : MatrixSymbol n) (hm : SmoothMatrix U M) (regular : ∀ y∈U,(M y).det≠0)
    (x : Phase) (hx : x∈U) (B : ℕ → ℝ) (K : ℕ) (u0 : ℝ)
    (positiveU : 0≤u0) (nonnegative : ∀ m,0≤B m)
    (base : RowColumnBound ((M x)⁻¹) u0)
    (bounds : ∀ m≤K,∀ w : Word m,
      RowColumnBound (fun i j=>jet m (fun y=>M y i j) w x) (B m))
    (m : ℕ) (finite : m≤K) (w : Word m) :
    RowColumnBound (fun i j=>jet m (fun y=>(M y)⁻¹ i j) w x) (inverseBudget B u0 m) := by
  have identity : ∀ y∈U,M y*(M y)⁻¹=1 := fun y hy=>
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (regular y hy))
  have inverse : (M x)⁻¹*M x=1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (regular x hx))
  have canonical : CanonicalList (List.ofFn (slotDirection∘w)) := by
    intro v hv
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hv
    exact ⟨w i,rfl⟩
  have actual:=matrix_inverse_list_budget openU M (fun y=>(M y)⁻¹) hm
    (inverse_smooth M hm regular) identity x hx inverse B K u0 positiveU nonnegative base bounds
    m finite (List.ofFn (slotDirection∘w)) canonical List.length_ofFn
  have read : matrixListJet (List.ofFn (slotDirection∘w)) (fun y=>(M y)⁻¹) x=
      (fun i j=>jet m (fun y=>(M y)⁻¹ i j) w x) := by
    ext i j
    exact listJet_ofFn openU (inverse_smooth M hm regular i j) m (slotDirection∘w) x hx
  rw [read] at actual
  exact actual

theorem determinant_abs_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : ℝ)
    (_positive : 0≤b) (entries : ∀ i j,|A i j|≤b) :
    |A.det|≤(Nat.factorial n : ℝ)*b^n := by
  rw [Matrix.det_apply']
  calc
    _≤∑ s : Equiv.Perm (Fin n),|(Equiv.Perm.sign s : ℝ)*(∏ i,A (s i) i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _≤∑ _s : Equiv.Perm (Fin n),b^n := by
      apply Finset.sum_le_sum
      intro s _
      rw [abs_mul,abs_unit_intCast,one_mul,Finset.abs_prod]
      calc
        _≤∏ _i : Fin n,b := Finset.prod_le_prod (fun i _=>abs_nonneg _) (fun i _=>entries (s i) i)
        _=b^n:=by simp
    _=(Nat.factorial n : ℝ)*b^n:=by simp [Fintype.card_perm]

theorem cofactor_rowColumn_inverse_bound {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (b j : ℝ) (positiveB : 0≤b) (positiveJ : 0≤j)
    (entries : ∀ i k,|A i k|≤b) (inverseDet : |A.det⁻¹|≤j) :
    RowColumnBound A⁻¹ ((Nat.factorial (n+1) : ℝ)*j*b^n) := by
  have adj (i k : Fin (n+1)) : |A.adjugate i k|≤(Nat.factorial n : ℝ)*b^n := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix,abs_mul,abs_pow]
    simp only [abs_neg,abs_one,one_pow,one_mul]
    exact determinant_abs_bound _ b positiveB (fun a d=>entries _ _)
  have entry (i k : Fin (n+1)) : |A⁻¹ i k|≤j*((Nat.factorial n : ℝ)*b^n) := by
    simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul,abs_mul]
    exact mul_le_mul inverseDet (adj i k) (abs_nonneg _) positiveJ
  constructor
  · intro i
    calc
      _≤∑ _k : Fin (n+1),j*((Nat.factorial n : ℝ)*b^n) :=
        Finset.sum_le_sum (fun k _=>entry i k)
      _=(Nat.factorial (n+1) : ℝ)*j*b^n:=by simp [Nat.factorial_succ]; ring
  · intro k
    calc
      _≤∑ _i : Fin (n+1),j*((Nat.factorial n : ℝ)*b^n) :=
        Finset.sum_le_sum (fun i _=>entry i k)
      _=(Nat.factorial (n+1) : ℝ)*j*b^n:=by simp [Nat.factorial_succ]; ring

open PreparationVacuumSourceChartBudget PreparationScalarCoordinates SourceQuantumScalarChart
open SourceQuantumConfigurationHilbert SourceQuantumResidualGaugeSlice SourceQuantumResidualFlow
open SourceQuantumGaugeSliceCoordinates CanonicalPreparationCutoff

def actualD9 : MatrixSymbol 9 := fun x=>sourceD9 (vacuum+((fullCoordinates.symm x.1).2.1 : Scalar))
def actualM3 : MatrixSymbol 3 := fun x=>
  PreparationVacuumSourceChartBudget.sourceOrbitMinor (fullCoordinates.symm x.1)

private def d9Linear (i j : Fin 9) : Scalar →ₗ[ℝ] ℝ where
  toFun phi:=sourceD9 phi i j
  map_add' phi psi:=congrArg (fun A=>A i j) (sourceD9_add phi psi)
  map_smul' r phi:=by
    simpa only [Matrix.smul_apply,smul_eq_mul,RingHom.id_apply] using
      congrArg (fun A=>A i j) (sourceD9_smul r phi)

private def m3Linear (i j : Fin 3) : Gauge →ₗ[ℝ] ℝ :=
  (LinearMap.proj (![2,1,0] i)).comp (orbitRows.comp (gaugeAction (sourceStabilizer j)))

theorem actualD9_smooth : SmoothMatrix Set.univ actualD9 := by
  intro i j
  have native : ContDiff ℝ ∞ (fun x : Phase=>fullCoordinates.symm x.1) :=
    fullCoordinates.symm.contDiff.comp contDiff_fst
  have sigma : ContDiff ℝ ∞ (fun x : Phase=>((fullCoordinates.symm x.1).2.1 : Scalar)) :=
    scalarSlice.subtypeL.contDiff.comp ((contDiff_fst.comp contDiff_snd).comp native)
  exact ((d9Linear i j).toContinuousLinearMap.contDiff.comp
    (contDiff_const.add sigma)).contDiffOn

theorem actualM3_smooth : SmoothMatrix Set.univ actualM3 := by
  intro i j
  have native : ContDiff ℝ ∞ (fun x : Phase=>fullCoordinates.symm x.1) :=
    fullCoordinates.symm.contDiff.comp contDiff_fst
  have gauge : ContDiff ℝ ∞ (fun x : Phase=>((fullCoordinates.symm x.1).2.2 : Gauge)) :=
    coordinateSlice.subtypeL.contDiff.comp ((contDiff_snd.comp contDiff_snd).comp native)
  exact ((m3Linear i j).toContinuousLinearMap.contDiff.comp gauge).contDiffOn

theorem actual_D9_inverse_budget (x : Phase)
    (box : ∀ i,|x.1 i-flatSource i| ≤ sourceRadius) (B : ℕ → ℝ) (K : ℕ)
    (nonnegative : ∀ m,0≤B m)
    (bounds : ∀ m≤K,∀ w : Word m,
      RowColumnBound (fun i j=>jet m (fun y=>actualD9 y i j) w x) (B m))
    (m : ℕ) (finite : m≤K) (w : Word m) :
    RowColumnBound (fun i j=>jet m (fun y=>(actualD9 y)⁻¹ i j) w x)
      (inverseBudget B ((Nat.factorial 9 : ℝ)*15*(B 0)^8) m) := by
  let U:= {y : Phase | (actualD9 y).det≠0}
  have global:=determinant_smooth actualD9 actualD9_smooth
  have openU : IsOpen U := isOpen_ne.preimage (contDiffOn_univ.mp global).continuous
  have hx : x∈U := by
    have guard:=sourceD9_j15 x.1 box
    change (1/15 : ℝ)≤(actualD9 x).det at guard
    change (actualD9 x).det≠0
    linarith
  have base:=cofactor_rowColumn_inverse_bound (actualD9 x) (B 0) 15 (nonnegative 0)
    (by norm_num) (fun i j=>entry_bound (bounds 0 (by omega) (fun i=>Fin.elim0 i)) i j)
    (sourceD9_inverse_zero x.1 box)
  exact matrix_inverse_canonical_budget openU actualD9
    (fun i j=>(actualD9_smooth i j).mono (Set.subset_univ _)) (fun _ hy=>hy)
    x hx B K _ (by positivity) nonnegative base bounds m finite w

theorem actual_M3_inverse_budget (x : Phase)
    (box : ∀ i,|x.1 i-flatSource i| ≤ sourceRadius) (B : ℕ → ℝ) (K : ℕ)
    (nonnegative : ∀ m,0≤B m)
    (bounds : ∀ m≤K,∀ w : Word m,
      RowColumnBound (fun i j=>jet m (fun y=>actualM3 y i j) w x) (B m))
    (m : ℕ) (finite : m≤K) (w : Word m) :
    RowColumnBound (fun i j=>jet m (fun y=>(actualM3 y)⁻¹ i j) w x)
      (inverseBudget B ((Nat.factorial 3 : ℝ)*15*(B 0)^2) m) := by
  let U:= {y : Phase | (actualM3 y).det≠0}
  have global:=determinant_smooth actualM3 actualM3_smooth
  have openU : IsOpen U := isOpen_ne.preimage (contDiffOn_univ.mp global).continuous
  have hx : x∈U := by
    have guard:=PreparationVacuumSourceChartBudget.sourceOrbitMinor_j15 x.1 box
    change (1/15 : ℝ)≤-(actualM3 x).det at guard
    change (actualM3 x).det≠0
    linarith
  have base:=cofactor_rowColumn_inverse_bound (actualM3 x) (B 0) 15 (nonnegative 0)
    (by norm_num) (fun i j=>entry_bound (bounds 0 (by omega) (fun i=>Fin.elim0 i)) i j)
    (PreparationVacuumSourceChartBudget.sourceOrbitMinor_inverse_zero x.1 box)
  exact matrix_inverse_canonical_budget openU actualM3
    (fun i j=>(actualM3_smooth i j).mono (Set.subset_univ _)) (fun _ hy=>hy)
    x hx B K _ (by positivity) nonnegative base bounds m finite w

end LowEnergy.PreparationVacuumMatrixBudget
