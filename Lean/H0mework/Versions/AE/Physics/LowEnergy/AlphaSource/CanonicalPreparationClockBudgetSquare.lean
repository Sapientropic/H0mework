import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationClockBudgetZeros

set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumClockBudget
open PreparationVacuumCentralBudget PreparationVacuumEngineBudget PreparationVacuumCanonicalMoyal
open PreparationVacuumClockSymbol PreparationVacuumClockJacobian PreparationVacuumClockPole
open PreparationVacuumReciprocalBudget PreparationVacuumMoyalSymmetry PreparationVacuumMoyalBudget
open PreparationActualFactor PreparationVacuumEngineSmooth CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators ContDiff Topology

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase

def properSplits (vs : List Phase) : List Split :=
  (wordSplittings vs).tail.filter (fun s => !s.2.isEmpty)

theorem splits_right_empty (vs : List Phase) :
    (wordSplittings vs).filter (fun s => s.2.isEmpty)=[(vs,[])] := by
  induction vs with
  | nil => simp [wordSplittings]
  | cons v vs ih =>
    simp only [wordSplittings_cons,List.filter_append,List.filter_map,Function.comp_def]
    simp [ih]

theorem tail_right_empty (v : Phase) (vs : List Phase) :
    ((wordSplittings (v::vs)).tail).filter (fun s => s.2.isEmpty)=[(v::vs,[])] := by
  have read := splits_right_empty (v::vs)
  rw [wordSplittings_head] at read
  simpa using read

private theorem sum_partition (ss : List Split) (p : Split → Bool) (F : Split → ℝ) :
    (ss.map F).sum=((ss.filter p).map F).sum+((ss.filter (fun s => !p s)).map F).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    cases h : p s <;> simp [h,ih] <;> ring

theorem proper_short (v : Phase) (vs : List Phase) (s : Split) (member : s∈properSplits (v::vs)) :
    s.1.length<vs.length+1 ∧ s.2.length<vs.length+1 := by
  have selected := List.mem_filter.mp member
  have actualMember := List.mem_of_mem_tail selected.1
  have lengths := wordSplittings_lengths (v::vs) s actualMember
  have left := tail_split_nonempty v vs s selected.1
  have right : s.2.length≠0 := by
    have := selected.2
    cases h : s.2 <;> simp_all
  simp only [List.length_cons] at lengths
  omega

theorem proper_convolution (v : Phase) (vs : List Phase) (B D : ℕ → ℝ) :
    ((properSplits (v::vs)).map (fun s => B s.1.length*D s.2.length)).sum=
      ∑ r : Fin vs.length,((vs.length+1).choose (r.val+1) : ℝ)*B (r.val+1)*D (vs.length-r.val) := by
  let D0 : ℕ → ℝ := fun n => if n=0 then 0 else D n
  have replacement (ss : List Split) :
      ((ss.filter (fun s => !s.2.isEmpty)).map (fun s => B s.1.length*D s.2.length)).sum=
        (ss.map (fun s => B s.1.length*D0 s.2.length)).sum := by
    induction ss with
    | nil => simp
    | cons s ss ih => cases h : s.2 <;> simp [h,D0,ih]
  rw [properSplits,replacement,tail_split_convolution]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last,Nat.sub_self,D0,if_true,mul_zero,add_zero]
  apply Finset.sum_congr rfl
  intro r _
  rw [if_neg (by have := r.isLt; omega)]

/-- Both endpoint splits are the actual full jet, with every proper split strictly shorter. -/
theorem clock_square_word (v : Phase) (vs : List Phase) (x : Phase) (hx : x∈poleDomain) :
    listJet (v::vs) actualC x=(actualC x)⁻¹/2*
      (listJet (v::vs) actualRatio x-((properSplits (v::vs)).map (splitValue actualC actualC x)).sum) := by
  have smooth : ContDiffOn ℝ ∞ actualC poleDomain := fun y hy => (actualC_smooth y hy.1).contDiffWithinAt
  have germ : (fun y => actualC y*actualC y)=ᶠ[𝓝 x] actualRatio := by
    filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    rw [←pow_two,actualRatio_square y hy]
  have read := (PreparationVacuumMoyalBudget.listJet_germ germ (v::vs)).eq_of_nhds
  have leibniz := listJet_leibniz poleDomain_open actualC actualC smooth smooth (v::vs) hx
  change listJet (v::vs) (fun y => actualC y*actualC y) x=
    ((wordSplittings (v::vs)).map (splitValue actualC actualC x)).sum at leibniz
  rw [read,wordSplittings_head,List.map_cons,List.sum_cons] at leibniz
  have split := sum_partition (wordSplittings (v::vs)).tail (fun s => s.2.isEmpty) (splitValue actualC actualC x)
  rw [tail_right_empty,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,add_zero] at split
  rw [split] at leibniz
  change listJet (v::vs) actualRatio x=actualC x*listJet (v::vs) actualC x+
    (listJet (v::vs) actualC x*actualC x+((properSplits (v::vs)).map (splitValue actualC actualC x)).sum) at leibniz
  have nonzero : actualC x≠0 := (C_positive hx.1).ne'
  field_simp [nonzero]
  nlinarith [leibniz]

abbrev ClockBudgetAt (n : ℕ) := Fin (n+1) → ℝ

def nextClockBudget (R : ArrayBound) (u0 : ℝ) {n : ℕ} (previous : ClockBudgetAt n) : ClockBudgetAt (n+1) :=
  fun j => if h : j.val<n+1 then previous ⟨j.val,h⟩ else
    u0*(1/2 : ℝ)*(R (n+1)+∑ r : Fin n,((n+1).choose (r.val+1) : ℝ)*
      previous ⟨r.val+1,by have := r.isLt; omega⟩*previous ⟨n-r.val,by omega⟩)

def clockTable (R : ArrayBound) (u0 : ℝ) (n : ℕ) : ClockBudgetAt n :=
  Nat.rec (motive:=ClockBudgetAt) (fun _ => max 1 (R 0)) (fun _ previous => nextClockBudget R u0 previous) n

def clockArray (R : ArrayBound) (u0 : ℝ) (n : ℕ) : ℝ := clockTable R u0 n (Fin.last n)

theorem clockTable_preserves (R : ArrayBound) (u0 : ℝ) (n : ℕ) (j : Fin (n+1)) :
    clockTable R u0 (n+1) (Fin.castSucc j)=clockTable R u0 n j := by
  simp only [clockTable,nextClockBudget,Fin.val_castSucc,j.isLt,dif_pos]

theorem clockTable_previous (R : ArrayBound) (u0 : ℝ) (small big : ℕ) (paid : small ≤ big) (j : Fin (small+1)) :
    clockTable R u0 big (Fin.castLE (by omega) j)=clockTable R u0 small j := by
  induction big,paid using Nat.le_induction with
  | base => rfl
  | succ big paid ih =>
    have index : (Fin.castLE (by omega) j : Fin (big+2))=Fin.castSucc (Fin.castLE (by omega) j : Fin (big+1)) := rfl
    rw [index,clockTable_preserves,ih]

theorem clockTable_readback (R : ArrayBound) (u0 : ℝ) (n : ℕ) (j : Fin (n+1)) :
    clockTable R u0 n j=clockArray R u0 j.val := by
  have read := clockTable_previous R u0 j.val n (by have := j.isLt; omega) (Fin.last j.val)
  have same : (Fin.castLE (by have := j.isLt; omega) (Fin.last j.val) : Fin (n+1))=j := by apply Fin.ext; rfl
  rw [same] at read
  exact read

theorem clockArray_zero (R : ArrayBound) (u0 : ℝ) : clockArray R u0 0=max 1 (R 0) := rfl

theorem clockArray_succ (R : ArrayBound) (u0 : ℝ) (n : ℕ) :
    clockArray R u0 (n+1)=u0*(1/2 : ℝ)*(R (n+1)+∑ r : Fin n,((n+1).choose (r.val+1) : ℝ)*
      clockArray R u0 (r.val+1)*clockArray R u0 (n-r.val)) := by
  rw [show clockArray R u0 (n+1)=nextClockBudget R u0 (clockTable R u0 n) (Fin.last (n+1)) from rfl]
  simp only [nextClockBudget,Fin.val_last,lt_self_iff_false,dite_false]
  congr 2
  apply Finset.sum_congr rfl
  intro r _
  rw [clockTable_readback,clockTable_readback]

theorem clockArray_nonnegative (R : ArrayBound) (u0 : ℝ) (positive : ∀ n,0 ≤ R n) (zero : 0 ≤ u0) (n : ℕ) :
    0 ≤ clockArray R u0 n := by
  have table : ∀ n (j : Fin (n+1)),0 ≤ clockTable R u0 n j := by
    intro n
    induction n with
    | zero => intro j; exact (show (0 : ℝ) ≤ 1 by norm_num).trans (le_max_left _ _)
    | succ n ih =>
      intro j
      change 0 ≤ nextClockBudget R u0 (clockTable R u0 n) j
      unfold nextClockBudget
      split_ifs
      · exact ih _
      · exact mul_nonneg (mul_nonneg zero (by norm_num)) (add_nonneg (positive _)
          (Finset.sum_nonneg (fun r _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ih _)) (ih _))))
  exact table n (Fin.last n)

theorem finite_list_bound (f : RealSymbol) (smooth : SmoothSymbol f) (B : ArrayBound)
    (N : ℕ) (x : Phase) (hx : x∈poleDomain) (bounds : FiniteBound f N B x)
    (vs : List Phase) (canonical : PreparationVacuumReciprocalBudget.CanonicalList vs) (finite : vs.length ≤ N) :
    |listJet vs f x| ≤ B vs.length := by
  let w : Word vs.length := fun i => Classical.choose (canonical (vs.get i) (List.get_mem vs i))
  have generated : List.ofFn (fun i => slotDirection (w i))=vs := by
    have same : (fun i => slotDirection (w i))=(fun i : Fin vs.length => vs.get i) := by
      funext i
      exact (Classical.choose_spec (canonical (vs.get i) (List.get_mem vs i))).symm
    rw [same]
    exact List.ofFn_getElem
  rw [←generated,listJet_ofFn poleDomain_open smooth vs.length (fun i => slotDirection (w i)) x hx]
  simpa only [jet,List.length_ofFn] using bounds vs.length finite w

private theorem abs_sum_bound (ss : List Split) (F G : Split → ℝ) (bound : ∀ s∈ss,|F s| ≤ G s) :
    |(ss.map F).sum| ≤ (ss.map G).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add (bound s (by simp)) (ih (fun t ht => bound t (by simp [ht]))))

/-- Strong induction closes each actual C jet using only ratio jets and shorter generated C jets. -/
theorem actual_clock_list_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ) (input : ATInputs (z,WithLp.toLp 2 u) N)
    (ratioBound : FiniteBound actualRatio N (ratioArray input) (z,WithLp.toLp 2 u)) :
    ∀ n,n ≤ N → ∀ vs : List Phase,PreparationVacuumReciprocalBudget.CanonicalList vs → vs.length=n →
      |listJet vs actualC (z,WithLp.toLp 2 u)| ≤ clockArray (ratioArray input) (inverseClockZero input) n := by
  let x : Phase := (z,WithLp.toLp 2 u)
  have hx := sourceUnit_admitted z u zbox ubox unit
  have initial := actual_inverseClock_zero z u zbox ubox unit N input
  have nonnegative : ∀ n,0 ≤ clockArray (ratioArray input) (inverseClockZero input) n :=
    clockArray_nonnegative _ _ (ratioArray_nonnegative input) ((show (0 : ℝ) ≤ 1 by norm_num).trans (le_max_left _ _))
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn vs canonical length
    cases vs with
    | nil =>
      have h0 : n=0 := length.symm
      subst n
      simpa [listJet,clockArray_zero,clockZero] using actual_clock_zero z u zbox ubox unit N input
    | cons v vs =>
      have count : n=vs.length+1 := by simpa using length.symm
      subst n
      have R := finite_list_bound actualRatio actualRatio_smooth (ratioArray input) N x hx ratioBound
        (v::vs) canonical (by simpa using hn)
      have terms : ∀ s∈properSplits (v::vs),|splitValue actualC actualC x s| ≤
          clockArray (ratioArray input) (inverseClockZero input) s.1.length*
          clockArray (ratioArray input) (inverseClockZero input) s.2.length := by
        intro s hs
        have member := List.mem_of_mem_tail (List.mem_filter.mp hs).1
        have parts := canonicalList_splits canonical s member
        have lengths := proper_short v vs s hs
        have left := ih s.1.length lengths.1 (by omega) s.1 parts.1 rfl
        have right := ih s.2.length lengths.2 (by omega) s.2 parts.2 rfl
        rw [splitValue,abs_mul]
        exact mul_le_mul left right (abs_nonneg _) (nonnegative _)
      have proper := abs_sum_bound _ _ _ terms
      rw [clock_square_word v vs _ hx,abs_mul,abs_div,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),List.length_cons,clockArray_succ]
      have numerator := (abs_sub _ _).trans (add_le_add R proper)
      have outer : |(actualC x)⁻¹|/2 ≤ inverseClockZero input*(1/2 : ℝ) := by
        simpa [div_eq_mul_inv,mul_comm,x] using div_le_div_of_nonneg_right initial (by norm_num : (0 : ℝ) ≤ 2)
      have result := mul_le_mul outer numerator (abs_nonneg _) (by
        exact mul_nonneg ((show (0 : ℝ) ≤ 1 by norm_num).trans (le_max_left _ _)) (by norm_num))
      exact result.trans_eq (by rw [proper_convolution,List.length_cons])

theorem actual_clock_canonical_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ) (input : ATInputs (z,WithLp.toLp 2 u) N)
    (ratioBound : FiniteBound actualRatio N (ratioArray input) (z,WithLp.toLp 2 u)) :
    FiniteBound actualC N (clockArray (ratioArray input) (inverseClockZero input)) (z,WithLp.toLp 2 u) := by
  intro m hm w
  have hx := sourceUnit_admitted z u zbox ubox unit
  have canonical : PreparationVacuumReciprocalBudget.CanonicalList (List.ofFn (slotDirection∘w)) := by
    intro v hv
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
    exact ⟨w i,rfl⟩
  have result := actual_clock_list_budget z u zbox ubox unit N input ratioBound m hm
    (List.ofFn (slotDirection∘w)) canonical (List.length_ofFn)
  rw [listJet_ofFn poleDomain_open (fun y hy => (actualC_smooth y hy.1).contDiffWithinAt) m _ _ hx] at result
  exact result

end LowEnergy.PreparationVacuumClockBudget
