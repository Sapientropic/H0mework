import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationReciprocalSplittings

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMatrixBudget
open PreparationVacuumCanonicalMoyal PreparationVacuumMoyalSymmetry
open PreparationVacuumClockSymbol PreparationVacuumMoyalBudget PreparationVacuumReciprocalBudget
open scoped BigOperators ContDiff Topology Matrix

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase

abbrev MatrixSymbol (n : ℕ) := Phase → Matrix (Fin n) (Fin n) ℝ

def RowColumnBound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : ℝ) : Prop :=
  (∀ i,∑ j,|A i j|≤b) ∧ (∀ j,∑ i,|A i j|≤b)

theorem entry_bound {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b : ℝ}
    (h : RowColumnBound A b) (i j : Fin n) : |A i j|≤b :=
  (Finset.single_le_sum (fun k _ => abs_nonneg (A i k)) (Finset.mem_univ j)).trans (h.1 i)

theorem rowColumn_trans {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b c : ℝ}
    (h : RowColumnBound A b) (le : b≤c) : RowColumnBound A c :=
  ⟨fun i=>(h.1 i).trans le,fun j=>(h.2 j).trans le⟩

theorem rowColumn_zero (n : ℕ) : RowColumnBound (0 : Matrix (Fin n) (Fin n) ℝ) 0 := by
  constructor <;> intro i <;> simp

theorem rowColumn_neg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b : ℝ}
    (h : RowColumnBound A b) : RowColumnBound (-A) b := by
  simpa only [RowColumnBound,Matrix.neg_apply,abs_neg] using h

theorem rowColumn_transpose {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b : ℝ}
    (h : RowColumnBound A b) : RowColumnBound Aᵀ b := ⟨h.2,h.1⟩

theorem rowColumn_add {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} {b c : ℝ}
    (ha : RowColumnBound A b) (hb : RowColumnBound B c) : RowColumnBound (A+B) (b+c) := by
  constructor
  · intro i
    calc
      _≤∑ j,(|A i j|+|B i j|):=Finset.sum_le_sum (fun j _=>abs_add_le _ _)
      _=(∑ j,|A i j|)+(∑ j,|B i j|):=Finset.sum_add_distrib
      _≤b+c:=add_le_add (ha.1 i) (hb.1 i)
  · intro j
    calc
      _≤∑ i,(|A i j|+|B i j|):=Finset.sum_le_sum (fun i _=>abs_add_le _ _)
      _=(∑ i,|A i j|)+(∑ i,|B i j|):=Finset.sum_add_distrib
      _≤b+c:=add_le_add (ha.2 j) (hb.2 j)

private theorem row_product {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} {b c : ℝ}
    (positive : 0≤c) (ha : RowColumnBound A b) (hb : RowColumnBound B c) (i : Fin n) :
    (∑ j,|(A*B) i j|)≤b*c := by
  calc
    _≤∑ j,∑ k,|A i k*B k j|:=Finset.sum_le_sum (fun j _=>by
      rw [Matrix.mul_apply]
      exact Finset.abs_sum_le_sum_abs _ _)
    _=∑ k,|A i k| * (∑ j,|B k j|):=by
      simp_rw [abs_mul]
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _≤∑ k,|A i k| * c:=Finset.sum_le_sum (fun k _=>
      mul_le_mul_of_nonneg_left (hb.1 k) (abs_nonneg _))
    _=(∑ k,|A i k|)*c:=by rw [Finset.sum_mul]
    _≤b*c:=mul_le_mul_of_nonneg_right (ha.1 i) positive

theorem rowColumn_product {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} {b c : ℝ}
    (positiveB : 0≤b) (positiveC : 0≤c) (ha : RowColumnBound A b)
    (hb : RowColumnBound B c) : RowColumnBound (A*B) (b*c) := by
  refine ⟨row_product positiveC ha hb,?_⟩
  intro j
  have reverse:=row_product positiveB (rowColumn_transpose hb) (rowColumn_transpose ha) j
  rw [←Matrix.transpose_mul] at reverse
  simpa only [Matrix.transpose_apply,mul_comm] using reverse

theorem rowColumn_list_sum {n : ℕ} (ss : List (Matrix (Fin n) (Fin n) ℝ × ℝ))
    (bounds : ∀ t∈ss,RowColumnBound t.1 t.2) :
    RowColumnBound ((ss.map Prod.fst).sum) ((ss.map Prod.snd).sum) := by
  induction ss with
  | nil=>exact rowColumn_zero n
  | cons t ss ih=>
    simp only [List.map_cons,List.sum_cons]
    exact rowColumn_add (bounds t (by simp)) (ih (fun t ht=>bounds t (by simp [ht])))

def matrixListJet {n : ℕ} (vs : List Phase) (M : MatrixSymbol n) (x : Phase) :
    Matrix (Fin n) (Fin n) ℝ := fun i j=>listJet vs (fun y=>M y i j) x

def SmoothMatrix {n : ℕ} (U : Set Phase) (M : MatrixSymbol n) : Prop :=
  ∀ i j,ContDiffOn ℝ ∞ (fun x=>M x i j) U

private theorem matrixListJet_sum {n : ℕ} (ss : List (Matrix (Fin n) (Fin n) ℝ)) (i j : Fin n) :
    ss.sum i j=(ss.map (fun A=>A i j)).sum := by
  induction ss with
  | nil=>rfl
  | cons A ss ih=>simpa only [List.sum_cons,List.map_cons,Matrix.add_apply] using congrArg (A i j+·) ih

private theorem list_sum_finset_comm {ι κ : Type*} (ss : List ι) (t : Finset κ) (f : ι → κ → ℝ) :
    (ss.map (fun s=>∑ k∈t,f s k)).sum=∑ k∈t,(ss.map (fun s=>f s k)).sum := by
  induction ss with
  | nil=>simp
  | cons a ss ih=>simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib,ih]

theorem matrixListJet_product {n : ℕ} {U : Set Phase} (openU : IsOpen U)
    (M N : MatrixSymbol n) (hm : SmoothMatrix U M) (hn : SmoothMatrix U N)
    (vs : List Phase) (x : Phase) (hx : x∈U) :
    matrixListJet vs (fun y=>M y*N y) x=
      ((wordSplittings vs).map (fun s=>matrixListJet s.1 M x*matrixListJet s.2 N x)).sum := by
  ext i j
  unfold matrixListJet
  simp only [Matrix.mul_apply]
  rw [listJet_sum openU Finset.univ (fun k y=>M y i k*N y k j)
    (fun k _=>(hm i k).mul (hn k j)) vs hx]
  simp_rw [listJet_leibniz openU _ _ (hm i _) (hn _ j) vs hx]
  rw [matrixListJet_sum,List.map_map]
  change (∑ k : Fin n,((wordSplittings vs).map (fun s=>
    listJet s.1 (fun y=>M y i k) x*listJet s.2 (fun y=>N y k j) x)).sum)=
    ((wordSplittings vs).map (fun s=>∑ k : Fin n,
      listJet s.1 (fun y=>M y i k) x*listJet s.2 (fun y=>N y k j) x)).sum
  exact (list_sum_finset_comm (wordSplittings vs) Finset.univ
    (fun s k=>listJet s.1 (fun y=>M y i k) x*listJet s.2 (fun y=>N y k j) x)).symm

theorem matrixListJet_product_bound {n : ℕ} {U : Set Phase} (openU : IsOpen U)
    (M N : MatrixSymbol n) (hm : SmoothMatrix U M) (hn : SmoothMatrix U N)
    (vs : List Phase) (x : Phase) (hx : x∈U) (B D : ℕ → ℝ)
    (nonnegativeB : ∀ m,0≤B m) (nonnegativeD : ∀ m,0≤D m)
    (left : ∀ s∈wordSplittings vs,RowColumnBound (matrixListJet s.1 M x) (B s.1.length))
    (right : ∀ s∈wordSplittings vs,RowColumnBound (matrixListJet s.2 N x) (D s.2.length)) :
    RowColumnBound (matrixListJet vs (fun y=>M y*N y) x) (convolution vs.length 0 B D) := by
  rw [matrixListJet_product openU M N hm hn vs x hx]
  have bound:=rowColumn_list_sum
    ((wordSplittings vs).map (fun s=>(matrixListJet s.1 M x*matrixListJet s.2 N x,
      B s.1.length*D s.2.length))) (by
        intro t ht
        obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
        exact rowColumn_product (nonnegativeB _) (nonnegativeD _) (left s hs) (right s hs))
  simp only [List.map_map] at bound
  change RowColumnBound
    ((wordSplittings vs).map (fun s=>matrixListJet s.1 M x*matrixListJet s.2 N x)).sum
    ((wordSplittings vs).map (fun s=>B s.1.length*D s.2.length)).sum at bound
  have counted : ((wordSplittings vs).map (fun s=>B s.1.length*D s.2.length)).sum=
      convolution vs.length 0 B D := by
    simpa only [zero_add] using split_convolution vs 0 B D
  rw [counted] at bound
  exact bound

end LowEnergy.PreparationVacuumMatrixBudget
