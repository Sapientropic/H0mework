import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationMatrixRowColumn

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMatrixBudget
open PreparationVacuumCanonicalMoyal PreparationVacuumMoyalSymmetry
open PreparationVacuumClockSymbol PreparationVacuumMoyalBudget PreparationVacuumReciprocalBudget
open scoped BigOperators ContDiff Topology Matrix

private theorem listJet_const (vs : List Phase) (c : ℝ) :
    listJet vs (fun _ : Phase=>c)=(fun _=>if vs=[] then c else 0) := by
  induction vs with
  | nil=>rfl
  | cons v vs ih=>
    change (fun x=>fderiv ℝ (listJet vs (fun _ : Phase=>c)) x v)=_
    rw [ih]
    simp only [List.cons_ne_nil,if_false,fderiv_const_apply,zero_apply]

theorem matrixListJet_germ {n : ℕ} {M N : MatrixSymbol n} {x : Phase}
    (same : M=ᶠ[𝓝 x] N) (vs : List Phase) : matrixListJet vs M x=matrixListJet vs N x := by
  ext i j
  exact (listJet_germ (same.mono (fun _ h=>congrArg (fun A=>A i j) h)) vs).eq_of_nhds

theorem matrixListJet_constant {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (v : Phase) (vs : List Phase) (x : Phase) : matrixListJet (v::vs) (fun _=>A) x=0 := by
  ext i j
  exact congrFun (listJet_const (v::vs) (A i j)) x

theorem matrix_inverse_word_recursion {n : ℕ} {U : Set Phase} (openU : IsOpen U)
    (M N : MatrixSymbol n) (hm : SmoothMatrix U M) (hn : SmoothMatrix U N)
    (identity : ∀ y∈U,M y*N y=1) (x : Phase) (hx : x∈U)
    (inverse : N x*M x=1) (v : Phase) (vs : List Phase) :
    matrixListJet (v::vs) N x= -N x*
      (((wordSplittings (v::vs)).tail).map
        (fun s=>matrixListJet s.1 M x*matrixListJet s.2 N x)).sum := by
  have germ : (fun y=>M y*N y)=ᶠ[𝓝 x] (fun _=>1) := by
    filter_upwards [openU.mem_nhds hx] with y hy
    exact identity y hy
  have zero:=matrixListJet_germ germ (v::vs)
  rw [matrixListJet_constant] at zero
  have product:=matrixListJet_product openU M N hm hn (v::vs) x hx
  rw [wordSplittings_head,List.map_cons,List.sum_cons] at product
  have equation : M x*matrixListJet (v::vs) N x+
      (((wordSplittings (v::vs)).tail).map
        (fun s=>matrixListJet s.1 M x*matrixListJet s.2 N x)).sum=0 :=
    product.symm.trans zero
  have multiplied:=congrArg (fun A=>N x*A) equation
  rw [mul_add,←mul_assoc,inverse,one_mul,mul_zero] at multiplied
  have isolated:=eq_neg_of_add_eq_zero_left multiplied
  simpa only [neg_mul] using isolated

private theorem matrixCanonical_to_list {n : ℕ} {U : Set Phase} (openU : IsOpen U)
    (M : MatrixSymbol n) (hm : SmoothMatrix U M) (x : Phase) (hx : x∈U)
    (B : ℕ → ℝ) (N : ℕ)
    (bounds : ∀ m≤N,∀ w : Word m,
      RowColumnBound (fun i j=>jet m (fun y=>M y i j) w x) (B m))
    (vs : List Phase) (canonical : CanonicalList vs) (finite : vs.length≤N) :
    RowColumnBound (matrixListJet vs M x) (B vs.length) := by
  let w : Word vs.length:=fun i=>Classical.choose
    (canonical (vs.get i) (List.get_mem vs i))
  have generated : List.ofFn (fun i=>slotDirection (w i))=vs := by
    have same : (fun i=>slotDirection (w i))=(fun i : Fin vs.length=>vs.get i) := by
      funext i
      exact (Classical.choose_spec (canonical (vs.get i) (List.get_mem vs i))).symm
    rw [same]
    exact List.ofFn_getElem
  have readback : matrixListJet vs M x=(fun i j=>jet vs.length (fun y=>M y i j) w x) := by
    ext i j
    unfold matrixListJet
    exact (congrArg (fun ws=>listJet ws (fun y=>M y i j) x) generated.symm).trans
      (listJet_ofFn openU (hm i j) vs.length (fun i=>slotDirection (w i)) x hx)
  rw [readback]
  exact bounds vs.length finite w

theorem matrix_inverse_list_budget {n : ℕ} {U : Set Phase} (openU : IsOpen U)
    (M N : MatrixSymbol n) (hm : SmoothMatrix U M) (hn : SmoothMatrix U N)
    (identity : ∀ y∈U,M y*N y=1) (x : Phase) (hx : x∈U) (inverse : N x*M x=1)
    (B : ℕ → ℝ) (K : ℕ) (u0 : ℝ) (positiveU : 0≤u0) (nonnegative : ∀ m,0≤B m)
    (base : RowColumnBound (N x) u0)
    (bounds : ∀ m≤K,∀ w : Word m,
      RowColumnBound (fun i j=>jet m (fun y=>M y i j) w x) (B m)) :
    ∀ m≤K,∀ vs : List Phase,CanonicalList vs → vs.length=m →
      RowColumnBound (matrixListJet vs N x) (inverseBudget B u0 m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih=>
    intro finite vs canonical length
    cases vs with
    | nil=>
      have zero : m=0:=length.symm
      subst m
      exact base
    | cons v vs=>
      have count : m=vs.length+1:=by simpa using length.symm
      subst m
      rw [matrix_inverse_word_recursion openU M N hm hn identity x hx inverse v vs]
      have terms : ∀ s∈(wordSplittings (v::vs)).tail,
          RowColumnBound (matrixListJet s.1 M x*matrixListJet s.2 N x)
            (B s.1.length*inverseBudget B u0 s.2.length) := by
        intro s hs
        have member:=List.mem_of_mem_tail hs
        have parts:=canonicalList_splits canonical s member
        have lengths:=wordSplittings_lengths (v::vs) s member
        simp only [List.length_cons] at lengths
        have left:=matrixCanonical_to_list openU M hm x hx B K bounds s.1 parts.1 (by omega)
        have short:=tail_split_short v vs s hs
        have right:=ih s.2.length short (by omega) s.2 parts.2 rfl
        exact rowColumn_product (nonnegative _) (inverseBudget_nonnegative B u0 positiveU nonnegative _)
          left right
      have total:=rowColumn_list_sum (((wordSplittings (v::vs)).tail).map
        (fun s=>(matrixListJet s.1 M x*matrixListJet s.2 N x,
          B s.1.length*inverseBudget B u0 s.2.length))) (by
            intro t ht
            obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
            exact terms s hs)
      simp only [List.map_map] at total
      change RowColumnBound (((wordSplittings (v::vs)).tail).map
        (fun s=>matrixListJet s.1 M x*matrixListJet s.2 N x)).sum
        (((wordSplittings (v::vs)).tail).map
          (fun s=>B s.1.length*inverseBudget B u0 s.2.length)).sum at total
      rw [tail_split_convolution] at total
      have sumPositive : 0≤∑ r : Fin (vs.length+1),
          ((vs.length+1).choose (r.val+1) : ℝ)*B (r.val+1)*inverseBudget B u0 (vs.length-r.val) := by
        apply Finset.sum_nonneg
        intro r _
        exact mul_nonneg (mul_nonneg (by positivity) (nonnegative _))
          (inverseBudget_nonnegative B u0 positiveU nonnegative _)
      rw [List.length_cons,inverseBudget_succ]
      exact rowColumn_product positiveU sumPositive (rowColumn_neg base) total

end LowEnergy.PreparationVacuumMatrixBudget
