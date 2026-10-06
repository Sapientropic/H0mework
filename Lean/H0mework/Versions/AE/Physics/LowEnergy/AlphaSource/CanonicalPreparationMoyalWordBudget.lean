import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationClockInverseJets
import Mathlib.Algebra.Order.BigOperators.Group.List

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMoyalBudget
open PreparationVacuumCanonicalMoyal PreparationVacuumMoyalSymmetry PreparationVacuumClockSymbol
open scoped BigOperators ContDiff Topology

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev Symbol := PreparationVacuumCanonicalMoyal.Symbol

def convolution (m r : ℕ) (B D : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Finset.range (m+1),(m.choose a : ℝ)*B (r+a)*D (r+(m-a))

private theorem counted_sum (ss : List Split) (H : ℕ → ℝ) (k : ℕ) :
    (ss.map (fun s => if s.1.length=k then H k else 0)).sum=
      (ss.countP (fun s => s.1.length==k) : ℝ)*H k := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    by_cases same : s.1.length=k
    · simp [List.sum_cons,ih,same,Nat.cast_add,add_mul]
      ring
    · simp [List.sum_cons,ih,same]

private theorem list_sum_partition (ss : List Split) (H : ℕ → ℝ) (m : ℕ)
    (range : ∀ s∈ss,s.1.length≤ m) :
    (ss.map (fun s => H s.1.length)).sum=
      ∑ k ∈ Finset.range (m+1),(ss.countP (fun s => s.1.length==k) : ℝ)*H k := by
  have partition : (ss.map (fun s => H s.1.length)).sum=
      ∑ k ∈ Finset.range (m+1),(ss.map (fun s => if s.1.length=k then H k else 0)).sum := by
    induction ss with
    | nil => simp
    | cons s ss ih =>
      have hs := range s (by simp)
      have ht : ∀ t∈ss,t.1.length≤ m := fun t ht => range t (by simp [ht])
      simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib]
      rw [ih ht]
      have single : (∑ k ∈ Finset.range (m+1),if s.1.length=k then H k else 0)=H s.1.length := by
        rw [Finset.sum_ite_eq]
        exact if_pos (Finset.mem_range.mpr (by omega))
      rw [single]
  rw [partition]
  exact Finset.sum_congr rfl (fun k _ => counted_sum ss H k)

theorem split_convolution (vs : List Phase) (r : ℕ) (B D : ℕ → ℝ) :
    ((wordSplittings vs).map (fun s => B (r+s.1.length)*D (r+s.2.length))).sum=
      convolution vs.length r B D := by
  have lengths := wordSplittings_lengths vs
  have replacement : ((wordSplittings vs).map (fun s => B (r+s.1.length)*D (r+s.2.length))).sum=
      ((wordSplittings vs).map (fun s => B (r+s.1.length)*D (r+(vs.length-s.1.length)))).sum := by
    congr 1
    apply List.map_congr_left
    intro s hs
    have h := lengths s hs
    have right : s.2.length=vs.length-s.1.length := by omega
    rw [right]
  rw [replacement]
  rw [list_sum_partition (wordSplittings vs) (fun a => B (r+a)*D (r+(vs.length-a)))
    vs.length (fun s hs => by have h := lengths s hs; omega)]
  simp only [wordSplittings_left_count,convolution,mul_assoc]

theorem listJet_germ {f g : Symbol} {x : Phase} (same : f=ᶠ[𝓝 x] g) (vs : List Phase) :
    listJet vs f=ᶠ[𝓝 x] listJet vs g := by
  induction vs with
  | nil => exact same
  | cons v vs ih =>
    have derivative : fderiv ℝ (listJet vs f)=ᶠ[𝓝 x] fderiv ℝ (listJet vs g) := ih.fderiv
    filter_upwards [derivative] with y hy
    exact congrArg (fun L : Phase →L[ℝ] ℝ => L v) hy

theorem listJet_add {U : Set Phase} (openU : IsOpen U) (f g : Symbol)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) (vs : List Phase) :
    Set.EqOn (listJet vs (fun x => f x+g x)) (fun x => listJet vs f x+listJet vs g x) U := by
  induction vs with
  | nil => intro x _; rfl
  | cons v vs ih =>
    intro x hx
    have germ : listJet vs (fun y => f y+g y)=ᶠ[𝓝 x] (fun y => listJet vs f y+listJet vs g y) := by
      filter_upwards [openU.mem_nhds hx] with y hy
      exact ih hy
    have hfx := listJet_smooth vs ((hf x hx).contDiffAt (openU.mem_nhds hx))
    have hgx := listJet_smooth vs ((hg x hx).contDiffAt (openU.mem_nhds hx))
    change fderiv ℝ (listJet vs (fun y => f y+g y)) x v=_
    rw [germ.fderiv_eq,fderiv_fun_add (hfx.differentiableAt (by simp)) (hgx.differentiableAt (by simp)),add_apply]
    rfl

theorem listJet_scale {U : Set Phase} (openU : IsOpen U) (c : ℝ) (f : Symbol)
    (hf : ContDiffOn ℝ ∞ f U) (vs : List Phase) :
    Set.EqOn (listJet vs (fun x => c*f x)) (fun x => c*listJet vs f x) U := by
  induction vs with
  | nil => intro x _; rfl
  | cons v vs ih =>
    intro x hx
    have germ : listJet vs (fun y => c*f y)=ᶠ[𝓝 x] (fun y => c*listJet vs f y) := by
      filter_upwards [openU.mem_nhds hx] with y hy
      exact ih hy
    change fderiv ℝ (listJet vs (fun y => c*f y)) x v=_
    rw [germ.fderiv_eq,fderiv_const_mul ((listJet_smooth vs
      ((hf x hx).contDiffAt (openU.mem_nhds hx))).differentiableAt (by simp)) c,smul_apply,smul_eq_mul]
    rfl

theorem listJet_sum {U : Set Phase} (openU : IsOpen U) {ι : Type} (s : Finset ι) (f : ι → Symbol)
    (hf : ∀ i∈s,ContDiffOn ℝ ∞ (f i) U) (vs : List Phase) :
    Set.EqOn (listJet vs (fun x => ∑ i∈s,f i x)) (fun x => ∑ i∈s,listJet vs (f i) x) U := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro x hx
    simp only [Finset.sum_empty]
    have zero : listJet vs (fun _ : Phase => (0 : ℝ))=(fun _ => 0) := by
      induction vs with
      | nil => rfl
      | cons v vs ih =>
        change (fun y => fderiv ℝ (listJet vs (fun _ => (0 : ℝ))) y v)=_
        rw [ih]
        simp [fderiv_const_apply]
    exact congrFun zero x
  | @insert i s hi ih =>
    have hs : ∀ j∈s,ContDiffOn ℝ ∞ (f j) U := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have sumSmooth : ContDiffOn ℝ ∞ (fun x => ∑ j∈s,f j x) U :=
      ContDiffOn.sum (fun j hj => hs j hj)
    intro x hx
    simp only [Finset.sum_insert hi]
    rw [listJet_add openU (f i) _ (hf i (Finset.mem_insert_self _ _)) sumSmooth vs hx]
    change listJet vs (f i) x+listJet vs (fun y => ∑ j∈s,f j y) x=_
    rw [ih hs hx]

theorem listJet_append (left right : List Phase) (f : Symbol) :
    listJet left (listJet right f)=listJet (left++right) f := by
  simp only [listJet,List.foldr_append]

private theorem abs_list_sum_le (ss : List Split) (F : Split → ℝ) :
    |(ss.map F).sum|≤(ss.map (fun s => |F s|)).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih => simpa only [List.map_cons,List.sum_cons] using (abs_add_le _ _).trans (add_le_add le_rfl ih)

theorem listJet_product_bound {U : Set Phase} (openU : IsOpen U) (f g : Symbol)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (vs : List Phase) (x : Phase) (hx : x∈U) (r : ℕ) (B D : ℕ → ℝ)
    (nonnegB : ∀ n,0≤ B n)
    (left : ∀ s∈wordSplittings vs,|listJet s.1 f x|≤ B (r+s.1.length))
    (right : ∀ s∈wordSplittings vs,|listJet s.2 g x|≤ D (r+s.2.length)) :
    |listJet vs (fun y => f y*g y) x|≤ convolution vs.length r B D := by
  rw [listJet_leibniz openU f g hf hg vs hx]
  change |((wordSplittings vs).map (splitValue f g x)).sum|≤convolution vs.length r B D
  have terms : ∀ s∈wordSplittings vs,|splitValue f g x s|≤ B (r+s.1.length)*D (r+s.2.length) := by
    intro s hs
    rw [splitValue,abs_mul]
    exact mul_le_mul (left s hs) (right s hs) (abs_nonneg _) (nonnegB _)
  calc
    _≤((wordSplittings vs).map (fun s => |splitValue f g x s|)).sum := abs_list_sum_le _ _
    ((wordSplittings vs).map (fun s => |splitValue f g x s|)).sum≤
        ((wordSplittings vs).map (fun s => B (r+s.1.length)*D (r+s.2.length))).sum := by
      have generic (ss : List Split)
          (terms : ∀ s∈ss,|splitValue f g x s|≤B (r+s.1.length)*D (r+s.2.length)) :
          (ss.map (fun s => |splitValue f g x s|)).sum≤
            (ss.map (fun s => B (r+s.1.length)*D (r+s.2.length))).sum := by
        induction ss with
        | nil => simp
        | cons s ss ih =>
          simp only [List.map_cons,List.sum_cons]
          exact add_le_add (terms s (by simp)) (ih (fun t ht => terms t (by simp [ht])))
      exact generic _ terms
    _=convolution vs.length r B D := split_convolution vs r B D

end LowEnergy.PreparationVacuumMoyalBudget
