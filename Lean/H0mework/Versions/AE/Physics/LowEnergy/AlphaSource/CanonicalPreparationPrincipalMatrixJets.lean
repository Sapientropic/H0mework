import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationPrincipalMomentumMaps

set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPrincipalBudget
open PreparationVacuumCentralBudget PreparationVacuumClockBudget PreparationVacuumEngineBudget
open PreparationVacuumCanonicalMoyal PreparationVacuumClockSymbol PreparationVacuumEngineSmooth
open PreparationVacuumMoyalSymmetry PreparationVacuumMoyalBudget PreparationVacuumReciprocalBudget
open PreparationActualFactor PreparationScalarCoordinates CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators ContDiff Topology Matrix

abbrev RectSymbol (a b : ℕ) := Phase → Matrix (Fin a) (Fin b) ℝ

def RectBound {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) (B : ℝ) : Prop :=
  (∀ i,∑ j,|M i j| ≤ B) ∧ (∀ j,∑ i,|M i j| ≤ B)
def RectSmooth {a b : ℕ} (M : RectSymbol a b) : Prop := ∀ i j,SmoothSymbol (fun x => M x i j)
def rectJet {a b : ℕ} (vs : List Phase) (M : RectSymbol a b) (x : Phase) : Matrix (Fin a) (Fin b) ℝ :=
  fun i j => listJet vs (fun y => M y i j) x
def MatrixBound {a b : ℕ} (M : RectSymbol a b) (N : ℕ) (B : ArrayBound) (x : Phase) : Prop :=
  ∀ m ≤ N,∀ w : Word m,RectBound (fun i j => jet m (fun y => M y i j) w x) (B m)

theorem rect_trans {a b : ℕ} {M : Matrix (Fin a) (Fin b) ℝ} {B D : ℝ}
    (bound : RectBound M B) (le : B ≤ D) : RectBound M D :=
  ⟨fun i => (bound.1 i).trans le,fun j => (bound.2 j).trans le⟩
theorem rect_entry {a b : ℕ} {M : Matrix (Fin a) (Fin b) ℝ} {B : ℝ}
    (bound : RectBound M B) (i : Fin a) (j : Fin b) : |M i j| ≤ B :=
  (Finset.single_le_sum (fun k _ => abs_nonneg (M i k)) (Finset.mem_univ j)).trans (bound.1 i)

theorem rect_transpose {a b : ℕ} {M : Matrix (Fin a) (Fin b) ℝ} {B : ℝ}
    (bound : RectBound M B) : RectBound Mᵀ B := ⟨bound.2,bound.1⟩

theorem rect_add {a b : ℕ} {M L : Matrix (Fin a) (Fin b) ℝ} {B D : ℝ}
    (h : RectBound M B) (g : RectBound L D) : RectBound (M+L) (B+D) := by
  constructor
  · intro i
    exact (Finset.sum_le_sum (fun j _ => abs_add_le (M i j) (L i j))).trans
      ((Finset.sum_add_distrib).trans_le (add_le_add (h.1 i) (g.1 i)))
  · intro j
    exact (Finset.sum_le_sum (fun i _ => abs_add_le (M i j) (L i j))).trans
      ((Finset.sum_add_distrib).trans_le (add_le_add (h.2 j) (g.2 j)))

private theorem rect_product_row {a b c : ℕ} {M : Matrix (Fin a) (Fin b) ℝ}
    {L : Matrix (Fin b) (Fin c) ℝ} {B D : ℝ} (positive : 0 ≤ D)
    (h : RectBound M B) (g : RectBound L D) (i : Fin a) : (∑ j,|(M*L) i j|) ≤ B*D := by
  calc
    _ ≤ ∑ j,∑ k,|M i k*L k j| := Finset.sum_le_sum (fun j _ => by
      rw [Matrix.mul_apply]; exact Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ k,|M i k| *(∑ j,|L k j|) := by
      simp_rw [abs_mul]
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ ≤ ∑ k,|M i k| *D := Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (g.1 k) (abs_nonneg _))
    _ = (∑ k,|M i k|)*D := by rw [Finset.sum_mul]
    _ ≤ B*D := mul_le_mul_of_nonneg_right (h.1 i) positive

theorem rect_product {a b c : ℕ} {M : Matrix (Fin a) (Fin b) ℝ}
    {L : Matrix (Fin b) (Fin c) ℝ} {B D : ℝ} (bp : 0 ≤ B) (dp : 0 ≤ D)
    (h : RectBound M B) (g : RectBound L D) : RectBound (M*L) (B*D) := by
  refine ⟨rect_product_row dp h g,?_⟩
  intro j
  have reverse := rect_product_row bp (rect_transpose g) (rect_transpose h) j
  rw [←Matrix.transpose_mul] at reverse
  simpa only [Matrix.transpose_apply,mul_comm] using reverse

theorem rect_list_sum {a b : ℕ} (ss : List (Matrix (Fin a) (Fin b) ℝ × ℝ))
    (bounds : ∀ t∈ss,RectBound t.1 t.2) : RectBound ((ss.map Prod.fst).sum) ((ss.map Prod.snd).sum) := by
  induction ss with
  | nil => constructor <;> intro i <;> simp
  | cons t ss ih =>
    simp only [List.map_cons,List.sum_cons]
    exact rect_add (bounds t (by simp)) (ih (fun t ht => bounds t (by simp [ht])))

private theorem rect_sum_apply {a b : ℕ} (ss : List (Matrix (Fin a) (Fin b) ℝ)) (i : Fin a) (j : Fin b) :
    ss.sum i j=(ss.map (fun A => A i j)).sum := by
  induction ss with
  | nil => rfl
  | cons A ss ih => simpa only [List.sum_cons,List.map_cons,Matrix.add_apply] using congrArg (A i j+·) ih

private theorem list_sum_finset_comm {ι κ : Type*} (ss : List ι) (t : Finset κ) (f : ι → κ → ℝ) :
    (ss.map (fun s => ∑ k∈t,f s k)).sum=∑ k∈t,(ss.map (fun s => f s k)).sum := by
  induction ss with
  | nil => simp
  | cons a ss ih => simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib,ih]

theorem rectJet_product {a b c : ℕ} (M : RectSymbol a b) (L : RectSymbol b c)
    (ms : RectSmooth M) (ls : RectSmooth L) (vs : List Phase) (x : Phase) (hx : x∈poleDomain) :
    rectJet vs (fun y => M y*L y) x=
      ((wordSplittings vs).map (fun s => rectJet s.1 M x*rectJet s.2 L x)).sum := by
  ext i j
  unfold rectJet
  simp only [Matrix.mul_apply]
  rw [listJet_sum poleDomain_open Finset.univ (fun k y => M y i k*L y k j)
    (fun k _ => (ms i k).mul (ls k j)) vs hx]
  simp_rw [listJet_leibniz poleDomain_open _ _ (ms i _) (ls _ j) vs hx]
  rw [rect_sum_apply,List.map_map]
  exact (list_sum_finset_comm (wordSplittings vs) Finset.univ
    (fun s k => listJet s.1 (fun y => M y i k) x*listJet s.2 (fun y => L y k j) x)).symm

theorem matrix_list_bound {a b : ℕ} (M : RectSymbol a b) (smooth : RectSmooth M)
    (N : ℕ) (B : ArrayBound) (x : Phase) (hx : x∈poleDomain) (bound : MatrixBound M N B x)
    (vs : List Phase) (canonical : PreparationVacuumReciprocalBudget.CanonicalList vs) (finite : vs.length ≤ N) :
    RectBound (rectJet vs M x) (B vs.length) := by
  let w : Word vs.length := fun i => Classical.choose (canonical (vs.get i) (List.get_mem vs i))
  have generated : List.ofFn (fun i => slotDirection (w i))=vs := by
    have same : (fun i => slotDirection (w i))=(fun i : Fin vs.length => vs.get i) := by
      funext i
      exact (Classical.choose_spec (canonical (vs.get i) (List.get_mem vs i))).symm
    rw [same]
    exact List.ofFn_getElem
  have read : rectJet vs M x=(fun i j => jet vs.length (fun y => M y i j) w x) := by
    ext i j
    change listJet vs _ x=_
    conv_lhs => rw [←generated]
    rw [listJet_ofFn poleDomain_open (smooth i j) vs.length _ x hx]
    rfl
  rw [read]
  exact bound vs.length finite w

theorem finite_matrix_product {a b c : ℕ} (M : RectSymbol a b) (L : RectSymbol b c)
    (ms : RectSmooth M) (ls : RectSmooth L) (N : ℕ) (B D : ArrayBound)
    (bp : ∀ n,0 ≤ B n) (dp : ∀ n,0 ≤ D n) (x : Phase) (hx : x∈poleDomain)
    (mb : MatrixBound M N B x) (lb : MatrixBound L N D x) :
    MatrixBound (fun y => M y*L y) N (productArray B D) x := by
  intro m hm w
  let vs := List.ofFn (slotDirection∘w)
  have canonical : PreparationVacuumReciprocalBudget.CanonicalList vs := by
    intro v hv
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
    exact ⟨w i,rfl⟩
  have bounds : ∀ s∈wordSplittings vs,RectBound (rectJet s.1 M x*rectJet s.2 L x)
      (B s.1.length*D s.2.length) := by
    intro s hs
    have parts := canonicalList_splits canonical s hs
    have lens := wordSplittings_lengths vs s hs
    simp only [vs,List.length_ofFn] at lens
    exact rect_product (bp _) (dp _) (matrix_list_bound M ms N B x hx mb s.1 parts.1 (by omega))
      (matrix_list_bound L ls N D x hx lb s.2 parts.2 (by omega))
  have total := rect_list_sum ((wordSplittings vs).map (fun s =>
    (rectJet s.1 M x*rectJet s.2 L x,B s.1.length*D s.2.length))) (by
      intro t ht
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
      exact bounds s hs)
  simp only [List.map_map] at total
  change RectBound (((wordSplittings vs).map (fun s => rectJet s.1 M x*rectJet s.2 L x)).sum)
    (((wordSplittings vs).map (fun s => B s.1.length*D s.2.length)).sum) at total
  rw [←rectJet_product M L ms ls vs x hx] at total
  have count := split_convolution vs 0 B D
  simp only [zero_add,vs,List.length_ofFn,convolution] at count
  rw [count] at total
  have read : rectJet vs (fun y => M y*L y) x=
      (fun i j => jet m (fun y => (M y*L y) i j) w x) := by
    ext i j
    change listJet (List.ofFn (slotDirection∘w)) _ x=_
    rw [listJet_ofFn poleDomain_open (show SmoothSymbol (fun y => (M y*L y) i j) from by
      simp only [Matrix.mul_apply]
      exact ContDiffOn.sum (fun k _ => (ms i k).mul (ls k j))) m _ x hx]
    rfl
  rw [read] at total
  exact total

theorem matrix_product_smooth {a b c : ℕ} (M : RectSymbol a b) (L : RectSymbol b c)
    (ms : RectSmooth M) (ls : RectSmooth L) : RectSmooth (fun y => M y*L y) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum (fun k _ => (ms i k).mul (ls k j))

theorem finite_matrix_transpose {a b : ℕ} (M : RectSymbol a b) (N : ℕ) (B : ArrayBound)
    (x : Phase) (bound : MatrixBound M N B x) : MatrixBound (fun y => (M y)ᵀ) N B x :=
  fun m hm w => rect_transpose (bound m hm w)

def affineArray (v d : ℝ) : ArrayBound | 0 => v | 1 => d | _ => 0

def originalDArray : ArrayBound := affineArray 98928 108
def originalMArray : ArrayBound := affineArray 14550 10
def originalBArray : ArrayBound := affineArray 32010 22
def originalFArray : ArrayBound := inverseBudget originalDArray ((Nat.factorial 9 : ℝ)*15*98928^8)
def originalUArray : ArrayBound := inverseBudget originalMArray ((Nat.factorial 3 : ℝ)*15*14550^2)
def sectionArray : ArrayBound := productArray originalMArray originalUArray
def wArray (n : ℕ) : ℝ := originalBArray n+productArray originalBArray sectionArray n
def scalarFactorArray (n : ℕ) : ℝ := constantArray 4 n+3*productArray originalFArray wArray n
def gaugeFactorArray (n : ℕ) : ℝ := constantArray 1 n+sectionArray n
def p94Array : ArrayBound := affineArray 188 1
def pqArray : ArrayBound := affineArray 12 1

theorem affineArray_nonnegative (v d : ℝ) (vp : 0 ≤ v) (dp : 0 ≤ d) : ∀ n,0 ≤ affineArray v d n := by
  intro n
  cases n with
  | zero => exact vp
  | succ n => cases n with
    | zero => exact dp
    | succ n => exact le_refl 0

theorem scalarFactor_nonnegative : ∀ n,0 ≤ scalarFactorArray n := by
  have d := affineArray_nonnegative 98928 108 (by norm_num) (by norm_num)
  have m := affineArray_nonnegative 14550 10 (by norm_num) (by norm_num)
  have b := affineArray_nonnegative 32010 22 (by norm_num) (by norm_num)
  have u := inverseBudget_nonnegative originalMArray ((Nat.factorial 3 : ℝ)*15*14550^2) (by positivity) m
  have f := inverseBudget_nonnegative originalDArray ((Nat.factorial 9 : ℝ)*15*98928^8) (by positivity) d
  have sec := productArray_nonnegative originalMArray originalUArray m u
  have ww : ∀ n,0 ≤ wArray n := fun n => add_nonneg (b n)
    (productArray_nonnegative originalBArray sectionArray b sec n)
  intro n
  exact add_nonneg (constantArray_nonnegative 4 (by norm_num) n)
    (mul_nonneg (by norm_num) (productArray_nonnegative originalFArray wArray f ww n))

theorem gaugeFactor_nonnegative : ∀ n,0 ≤ gaugeFactorArray n := by
  have m := affineArray_nonnegative 14550 10 (by norm_num) (by norm_num)
  have u := inverseBudget_nonnegative originalMArray ((Nat.factorial 3 : ℝ)*15*14550^2) (by positivity) m
  intro n
  exact add_nonneg (constantArray_nonnegative 1 (by norm_num) n)
    (productArray_nonnegative originalMArray originalUArray m u n)

def momentumCoordinate (i : Fin 100) : Phase →L[ℝ] ℝ :=
  (PiLp.proj 2 (fun _ : Fin 100 => ℝ) i).comp (ContinuousLinearMap.snd ℝ _ _)

def momentumColumn {a : ℕ} (e : Fin a ↪ Fin 100) : RectSymbol a 1 := fun x i _ => x.2 (e i)

def p94Embedding : Fin 94 ↪ Fin 100 := ⟨Fin.natAdd 6,Fin.natAdd_injective 94 6⟩
def pqEmbedding : Fin 6 ↪ Fin 100 := ⟨Fin.castAdd 94,Fin.castAdd_injective 6 94⟩

private theorem embedded_sum_le {a : ℕ} (e : Fin a ↪ Fin 100) (f : Fin 100 → ℝ)
    (positive : ∀ i,0 ≤ f i) : (∑ i,f (e i)) ≤ ∑ i,f i := by
  rw [←Finset.sum_image]
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => positive i)
  · exact fun i _ j _ h => e.injective h

private theorem linear_higher (f : Phase →L[ℝ] ℝ) (n : ℕ) (w : Word (n+2)) (x : Phase) :
    jet (n+2) f w x=0 := by
  unfold jet
  rw [iteratedFDeriv_succ_apply_right]
  simp only [ContinuousLinearMap.fderiv]
  rw [iteratedFDeriv_const_of_ne (by omega)]
  simp

theorem momentumColumn_smooth {a : ℕ} (e : Fin a ↪ Fin 100) : RectSmooth (momentumColumn e) :=
  fun i _ => (momentumCoordinate (e i)).contDiff.contDiffOn

theorem momentumColumn_budget {a : ℕ} (e : Fin a ↪ Fin 100) (x : Phase)
    (unit : (∑ i : Fin 100,(x.2 i)^2)=1) (N : ℕ) :
    MatrixBound (momentumColumn e) N (affineArray (2*a) 1) x := by
  have entries (i : Fin 100) : |x.2 i| ≤ 2 := by
    have small := Finset.single_le_sum (s:=Finset.univ) (fun j _ => sq_nonneg (x.2 j)) (Finset.mem_univ i)
    rw [unit] at small
    nlinarith [abs_nonneg (x.2 i),sq_abs (x.2 i)]
  have total : ∀ m,∀ w : Word m,
      (∑ i : Fin a,|jet m (fun y => y.2 (e i)) w x|) ≤ affineArray (2*a) 1 m := by
    intro m w
    cases m with
    | zero =>
      simp only [jet,iteratedFDeriv_zero_apply,affineArray]
      calc
        _ ≤ ∑ _i : Fin a,(2 : ℝ) := Finset.sum_le_sum (fun i _ => entries (e i))
        _ = _ := by simp; ring
    | succ m => cases m with
      | zero =>
        have one (i : Fin 100) : jet 1 (fun y => y.2 i) w x=momentumCoordinate i (slotDirection (w 0)) := by
          change jet 1 (momentumCoordinate i) w x=_
          simp [jet,ContinuousLinearMap.fderiv]
        simp_rw [one]
        apply (embedded_sum_le e (fun i => |momentumCoordinate i (slotDirection (w 0))|) (fun i => abs_nonneg _)).trans
        rcases w 0 with ⟨i,b⟩
        cases b <;> simp [momentumCoordinate,slotDirection,pDirection,qDirection,affineArray,apply_ite,abs_zero,abs_one]
      | succ m =>
        have zero (i : Fin a) : jet (m+2) (fun y => y.2 (e i)) w x=0 := linear_higher (momentumCoordinate (e i)) m w x
        simp only [zero,abs_zero,Finset.sum_const_zero,affineArray,le_refl]
  intro m _ w
  constructor
  · intro i
    simpa [momentumColumn] using
      (Finset.single_le_sum (fun j _ => abs_nonneg (jet m (fun y => y.2 (e j)) w x)) (Finset.mem_univ i)).trans (total m w)
  · intro j
    exact total m w

/-- These are the explicit unspent coefficient responsibilities, at the actual inverseL maps. -/
structure CoefficientInputs (x : Phase) (N : ℕ) where
  scalar : MatrixBound (fun y => scalarCoefficients y.1) N scalarFactorArray x
  gauge : MatrixBound (fun y => gaugeCoefficients y.1) N gaugeFactorArray x

def scalarMomentumArray : ArrayBound := productArray scalarFactorArray p94Array
def gaugeMomentumArray : ArrayBound := productArray gaugeFactorArray p94Array

def rawScalarColumn : RectSymbol 70 1 := fun x a _ => rawScalarMomentum a x
def rawGaugeColumn : RectSymbol 36 1 := fun x a _ => rawGaugeMomentum a x

theorem actual_rawScalar_budget (x : Phase) (hx : x∈poleDomain)
    (unit : (∑ i : Fin 100,(x.2 i)^2)=1) (N : ℕ) (input : CoefficientInputs x N) :
    MatrixBound rawScalarColumn N scalarMomentumArray x := by
  have same : rawScalarColumn=(fun y => scalarCoefficients y.1*momentumColumn p94Embedding y) := by
    funext y
    ext a j
    exact actual_rawScalar_momentum_matrix y a
  rw [same]
  exact finite_matrix_product _ _ (fun a k => sourceCoefficient_smooth _ k)
    (momentumColumn_smooth p94Embedding) N scalarFactorArray p94Array scalarFactor_nonnegative
    (affineArray_nonnegative 188 1 (by norm_num) (by norm_num)) x hx input.scalar
    (by simpa only [p94Array,Nat.cast_ofNat,show (2 : ℝ)*94=188 by norm_num] using momentumColumn_budget p94Embedding x unit N)

theorem actual_rawGauge_budget (x : Phase) (hx : x∈poleDomain)
    (unit : (∑ i : Fin 100,(x.2 i)^2)=1) (N : ℕ) (input : CoefficientInputs x N) :
    MatrixBound rawGaugeColumn N gaugeMomentumArray x := by
  have same : rawGaugeColumn=(fun y => gaugeCoefficients y.1*momentumColumn p94Embedding y) := by
    funext y
    ext a j
    exact actual_rawGauge_momentum_matrix y a
  rw [same]
  exact finite_matrix_product _ _ (fun a k => sourceCoefficient_smooth _ k)
    (momentumColumn_smooth p94Embedding) N gaugeFactorArray p94Array gaugeFactor_nonnegative
    (affineArray_nonnegative 188 1 (by norm_num) (by norm_num)) x hx input.gauge
    (by simpa only [p94Array,Nat.cast_ofNat,show (2 : ℝ)*94=188 by norm_num] using momentumColumn_budget p94Embedding x unit N)

end LowEnergy.PreparationVacuumPrincipalBudget
