import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineActualBudget

set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCentralBudget
open PreparationVacuumEngineBudget PreparationVacuumCanonicalMoyal PreparationVacuumClockSymbol
open PreparationVacuumEngineSmooth PreparationVacuumMoyalBudget PreparationVacuumEngineSource
open scoped BigOperators ContDiff Topology

abbrev ArrayBound := ℕ → ℝ

def FiniteBound (f : RealSymbol) (N : ℕ) (B : ArrayBound) (x : SourcePhase) : Prop :=
  ∀ n,n ≤ N → ∀ w : Word n,|jet n f w x| ≤ B n

def constantArray (c : ℝ) (n : ℕ) : ℝ := if n=0 then c else 0

def productArray (B D : ArrayBound) (n : ℕ) : ℝ :=
  ∑ k∈Finset.range (n+1),(n.choose k : ℝ)*B k*D (n-k)

def powerArray (B : ArrayBound) (k : ℕ) : ArrayBound :=
  Nat.rec (constantArray 1) (fun _ previous => productArray previous B) k

def foldArray {ι : Type} (B : ι → ArrayBound) (xs : List ι) (initial : ArrayBound) : ArrayBound :=
  xs.foldl (fun previous i => productArray previous (B i)) initial

def foldValue {ι : Type} (f : ι → RealSymbol) (xs : List ι) (initial : RealSymbol) : RealSymbol :=
  xs.foldl (fun previous i => previous*f i) initial

theorem constantArray_nonnegative (c : ℝ) (positive : 0 ≤ c) (n : ℕ) : 0 ≤ constantArray c n := by
  unfold constantArray
  split_ifs <;> positivity

theorem productArray_nonnegative (B D : ArrayBound) (positiveB : ∀ n,0 ≤ B n) (positiveD : ∀ n,0 ≤ D n)
    (n : ℕ) : 0 ≤ productArray B D n := by
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (positiveB _)) (positiveD _)

theorem powerArray_nonnegative (B : ArrayBound) (positive : ∀ n,0 ≤ B n) (k n : ℕ) :
    0 ≤ powerArray B k n := by
  induction k generalizing n with
  | zero => exact constantArray_nonnegative 1 (by norm_num) n
  | succ k ih => exact productArray_nonnegative _ B ih positive n

theorem finite_constant (c a : ℝ) (estimate : |c| ≤ a) (N : ℕ) (x : SourcePhase) :
    FiniteBound (fun _ => c) N (constantArray a) x := by
  intro n _ w
  cases n with
  | zero => simpa [jet,constantArray] using estimate
  | succ n => simp [jet,constantArray,iteratedFDeriv_succ_const]

theorem finite_product (f g : RealSymbol) (fs : SmoothSymbol f) (gs : SmoothSymbol g)
    (B D : ArrayBound) (positiveB : ∀ n,0 ≤ B n) (N : ℕ) (x : SourcePhase) (hx : x∈poleDomain)
    (left : FiniteBound f N B x) (right : FiniteBound g N D x) :
    FiniteBound (f*g) N (productArray B D) x := by
  intro m hm w
  have result := scalarJordan_canonical_budget poleDomain_open 0 m f g fs gs w x hx B D positiveB
    (fun n hn v => left n (by omega) v) (fun n hn v => right n (by omega) v)
  simpa only [scalarJordan_zero,moyalScale,pow_zero,Nat.factorial_zero,Nat.cast_one,
    div_one,mul_one,one_mul,convolution,zero_add,productArray] using result

theorem finite_add (f g : RealSymbol) (fs : SmoothSymbol f) (gs : SmoothSymbol g)
    (B D : ArrayBound) (N : ℕ) (x : SourcePhase) (hx : x∈poleDomain)
    (left : FiniteBound f N B x) (right : FiniteBound g N D x) :
    FiniteBound (f+g) N (fun n => B n+D n) x := by
  intro m hm w
  have read : jet m (f+g) w x=jet m f w x+jet m g w x := by
    unfold jet
    rw [iteratedFDeriv_add_apply
      (((fs x hx).contDiffAt (poleDomain_open.mem_nhds hx)).of_le (by exact_mod_cast (ENat.natCast_lt_top m).le))
      (((gs x hx).contDiffAt (poleDomain_open.mem_nhds hx)).of_le (by exact_mod_cast (ENat.natCast_lt_top m).le))]
    rfl
  rw [read]
  exact (abs_add_le _ _).trans (add_le_add (left m hm w) (right m hm w))

theorem finite_neg (f : RealSymbol) (fs : SmoothSymbol f) (B : ArrayBound) (N : ℕ)
    (x : SourcePhase) (hx : x∈poleDomain) (bound : FiniteBound f N B x) : FiniteBound (-f) N B x := by
  intro m hm w
  have same : -f=(fun y => (-1 : ℝ)*f y) := by funext y; simp
  rw [same,PreparationVacuumEngineBudget.jet_scale _ f fs m w x hx,abs_mul]
  simpa using bound m hm w

theorem finite_sub (f g : RealSymbol) (fs : SmoothSymbol f) (gs : SmoothSymbol g)
    (B D : ArrayBound) (N : ℕ) (x : SourcePhase) (hx : x∈poleDomain)
    (left : FiniteBound f N B x) (right : FiniteBound g N D x) :
    FiniteBound (f-g) N (fun n => B n+D n) x := by
  rw [sub_eq_add_neg]
  exact finite_add f (-g) fs gs.neg B D N x hx left (finite_neg g gs D N x hx right)

theorem finite_dominate (f : RealSymbol) (B D : ArrayBound) (N : ℕ) (x : SourcePhase)
    (bound : FiniteBound f N B x) (larger : ∀ n,B n ≤ D n) : FiniteBound f N D x :=
  fun n hn w => (bound n hn w).trans (larger n)

theorem finite_scale (c : ℝ) (f : RealSymbol) (fs : SmoothSymbol f) (B : ArrayBound) (N : ℕ)
    (x : SourcePhase) (hx : x∈poleDomain) (bound : FiniteBound f N B x) :
    FiniteBound (fun y => c*f y) N (fun n => |c| *B n) x := by
  intro m hm w
  rw [PreparationVacuumEngineBudget.jet_scale c f fs m w x hx,abs_mul]
  exact mul_le_mul_of_nonneg_left (bound m hm w) (abs_nonneg c)

theorem finite_sum {ι : Type} (s : Finset ι) (f : ι → RealSymbol)
    (smooth : ∀ i∈s,SmoothSymbol (f i)) (B : ι → ArrayBound) (N : ℕ)
    (x : SourcePhase) (hx : x∈poleDomain) (bounds : ∀ i∈s,FiniteBound (f i) N (B i) x) :
    FiniteBound (fun y => ∑ i∈s,f i y) N (fun n => ∑ i∈s,B i n) x := by
  intro m hm w
  rw [jet_sum poleDomain_open s f smooth m w x hx]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i hi => bounds i hi m hm w))

theorem finite_common_product (B : ArrayBound) (positive : ∀ n,0 ≤ B n) (N : ℕ)
    (x : SourcePhase) (hx : x∈poleDomain) (k : ℕ) (f : Fin k → RealSymbol)
    (smooth : ∀ i,SmoothSymbol (f i)) (bounds : ∀ i,FiniteBound (f i) N B x) :
    FiniteBound (fun y => ∏ i,f i y) N (powerArray B k) x := by
  induction k with
  | zero => simpa [powerArray] using finite_constant 1 1 (by norm_num) N x
  | succ k ih =>
    have previous := ih (fun i => f (Fin.castSucc i)) (fun i => smooth (Fin.castSucc i))
      (fun i => bounds (Fin.castSucc i))
    have startSmooth : SmoothSymbol (fun y => ∏ i : Fin k,f (Fin.castSucc i) y) :=
      contDiffOn_prod (fun i _ => smooth _)
    have result := finite_product _ _ startSmooth (smooth (Fin.last k)) _ B
      (powerArray_nonnegative B positive k) N x hx previous (bounds (Fin.last k))
    simpa only [powerArray,Nat.rec_add_one,Fin.prod_univ_castSucc] using! result

theorem finite_power (f : RealSymbol) (smooth : SmoothSymbol f) (B : ArrayBound)
    (positive : ∀ n,0 ≤ B n) (N : ℕ) (x : SourcePhase) (hx : x∈poleDomain)
    (bound : FiniteBound f N B x) (k : ℕ) : FiniteBound (f^k) N (powerArray B k) x := by
  induction k with
  | zero => exact finite_constant 1 1 (by norm_num) N x
  | succ k ih =>
    rw [pow_succ]
    exact finite_product _ f (smooth.pow k) smooth _ B (powerArray_nonnegative B positive k) N x hx ih bound

theorem foldArray_nonnegative {ι : Type} (B : ι → ArrayBound) (positive : ∀ i n,0 ≤ B i n)
    (xs : List ι) (initial : ArrayBound) (start : ∀ n,0 ≤ initial n) : ∀ n,0 ≤ foldArray B xs initial n := by
  induction xs generalizing initial with
  | nil => exact start
  | cons i xs ih => exact ih (productArray initial (B i)) (productArray_nonnegative initial (B i) start (positive i))

theorem foldValue_smooth {ι : Type} (f : ι → RealSymbol) (smooth : ∀ i,SmoothSymbol (f i))
    (xs : List ι) (initial : RealSymbol) (start : SmoothSymbol initial) : SmoothSymbol (foldValue f xs initial) := by
  induction xs generalizing initial with
  | nil => exact start
  | cons i xs ih => exact ih (initial*f i) (start.mul (smooth i))

theorem foldValue_native {ι : Type} (f : ι → RealSymbol) (xs : List ι) (initial : RealSymbol)
    (x : SourcePhase) : foldValue f xs initial x=initial x*(xs.map (fun i => f i x)).prod := by
  induction xs generalizing initial with
  | nil => simp [foldValue]
  | cons i xs ih =>
    change foldValue f xs (initial*f i) x=_
    rw [ih]
    simp only [Pi.mul_apply,List.map_cons,List.prod_cons,mul_assoc]

theorem finite_fold {ι : Type} (f : ι → RealSymbol) (smooth : ∀ i,SmoothSymbol (f i))
    (B : ι → ArrayBound) (positive : ∀ i n,0 ≤ B i n) (N : ℕ) (x : SourcePhase) (hx : x∈poleDomain)
    (bounds : ∀ i,FiniteBound (f i) N (B i) x) (xs : List ι)
    (initial : RealSymbol) (startSmooth : SmoothSymbol initial) (startArray : ArrayBound)
    (startNonnegative : ∀ n,0 ≤ startArray n) (start : FiniteBound initial N startArray x) :
    FiniteBound (foldValue f xs initial) N (foldArray B xs startArray) x := by
  induction xs generalizing initial startArray with
  | nil => exact start
  | cons i xs ih =>
    exact ih (initial*f i) (startSmooth.mul (smooth i)) (productArray startArray (B i))
      (productArray_nonnegative startArray (B i) startNonnegative (positive i))
      (finite_product initial (f i) startSmooth (smooth i) startArray (B i) startNonnegative N x hx start (bounds i))

end LowEnergy.PreparationVacuumCentralBudget
