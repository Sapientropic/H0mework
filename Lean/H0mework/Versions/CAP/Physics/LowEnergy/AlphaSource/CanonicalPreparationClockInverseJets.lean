import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationClockRadial

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumClockSymbol
open PreparationActualFactor PreparationVacuumClockJacobian PreparationVacuumClockPole
open PreparationVacuumCanonicalMoyal PreparationVacuumMoyalSymmetry
open scoped BigOperators ContDiff Topology

abbrev Symbol := PreparationVacuumCanonicalMoyal.Symbol
abbrev Split := List Phase × List Phase

def wordSplittings (vs : List Phase) : List Split :=
  vs.foldr (fun v ss => ss.map (fun s => (s.1,v::s.2)) ++ ss.map (fun s => (v::s.1,s.2))) [([],[])]

def splitValue (f g : Symbol) (x : Phase) (s : Split) : ℝ := listJet s.1 f x*listJet s.2 g x

theorem wordSplittings_nil : wordSplittings []=[([],[])] := rfl
theorem wordSplittings_cons (v : Phase) (vs : List Phase) :
    wordSplittings (v::vs)=(wordSplittings vs).map (fun s => (s.1,v::s.2)) ++
      (wordSplittings vs).map (fun s => (v::s.1,s.2)) := rfl

theorem wordSplittings_head (vs : List Phase) :
    wordSplittings vs=([],vs)::(wordSplittings vs).tail := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [wordSplittings_cons,ih]
    simp only [List.map_cons,List.cons_append,List.tail_cons]

theorem wordSplittings_left_count (vs : List Phase) (k : ℕ) :
    ((wordSplittings vs).countP (fun s => s.1.length==k))=vs.length.choose k := by
  induction vs generalizing k with
  | nil => cases k <;> simp [wordSplittings]
  | cons v vs ih =>
    cases k with
    | zero => simpa [wordSplittings_cons,Function.comp_def] using ih 0
    | succ k =>
      simp only [wordSplittings_cons,List.countP_append,List.countP_map,Function.comp_def,List.length_cons]
      have step : (fun s : Split => s.1.length+1==k+1)=(fun s : Split => s.1.length==k) := by
        funext s; simp
      rw [step,ih,ih,Nat.choose_succ_succ]
      simp only [Nat.succ_eq_add_one]
      omega

theorem wordSplittings_lengths (vs : List Phase) (s : Split) (member : s∈wordSplittings vs) :
    s.1.length+s.2.length=vs.length := by
  induction vs generalizing s with
  | nil => simp [wordSplittings] at member; subst s; rfl
  | cons v vs ih =>
    rw [wordSplittings_cons,List.mem_append] at member
    rcases member with member|member
    · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp member
      have lengths := ih t ht
      simp only [List.length_cons]
      omega
    · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp member
      have lengths := ih t ht
      simp only [List.length_cons]
      omega

theorem wordSplittings_tail_count (v : Phase) (vs : List Phase) (k : ℕ) :
    (((wordSplittings (v::vs)).tail).countP (fun s => s.1.length==k+1))=
      (vs.length+1).choose (k+1) := by
  have count := wordSplittings_left_count (v::vs) (k+1)
  rw [wordSplittings_head] at count
  simpa using count

private theorem sum_derivative (ss : List Split) (f g : Symbol) (x v : Phase)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    fderiv ℝ (fun y => (ss.map (splitValue f g y)).sum) x v=
      (ss.map (fun s => splitValue f g x (s.1,v::s.2)+splitValue f g x (v::s.1,s.2))).sum := by
  induction ss with
  | nil => simp [fderiv_const_apply]
  | cons s ss ih =>
    have tail : ContDiffAt ℝ ∞ (fun y => (ss.map (splitValue f g y)).sum) x := by
      clear ih
      induction ss with
      | nil => exact contDiffAt_const
      | cons t ts ht =>
        simpa only [List.map_cons,List.sum_cons,splitValue] using!
          ((listJet_smooth t.1 hf).mul (listJet_smooth t.2 hg)).add ht
    simp only [List.map_cons,List.sum_cons]
    simp only [splitValue] at ih ⊢
    rw [fderiv_fun_add (((listJet_smooth s.1 hf).mul (listJet_smooth s.2 hg)).differentiableAt (by simp))
        (tail.differentiableAt (by simp)),add_apply,ih]
    rw [fderiv_fun_mul ((listJet_smooth s.1 hf).differentiableAt (by simp)) ((listJet_smooth s.2 hg).differentiableAt (by simp))]
    simp only [add_apply,smul_apply,smul_eq_mul,listJet,List.foldr_cons]
    ring

theorem listJet_leibniz {U : Set Phase} (openU : IsOpen U) (f g : Symbol)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) (vs : List Phase) :
    Set.EqOn (listJet vs (fun x => f x*g x))
      (fun x => ((wordSplittings vs).map (splitValue f g x)).sum) U := by
  induction vs with
  | nil => intro x _; simp [wordSplittings,listJet,splitValue]
  | cons v vs ih =>
    intro x hx
    have germ : listJet vs (fun y => f y*g y)=ᶠ[𝓝 x]
        (fun y => ((wordSplittings vs).map (splitValue f g y)).sum) := by
      filter_upwards [openU.mem_nhds hx] with y hy
      exact ih hy
    change fderiv ℝ (listJet vs (fun y => f y*g y)) x v=_
    rw [germ.fderiv_eq,sum_derivative _ f g x v
      ((hf x hx).contDiffAt (openU.mem_nhds hx)) ((hg x hx).contDiffAt (openU.mem_nhds hx))]
    simp only [wordSplittings_cons,List.map_append,List.sum_append,List.map_map]
    exact List.sum_map_add

private theorem listJet_germ {f g : Symbol} {x : Phase} (same : f=ᶠ[𝓝 x] g) (vs : List Phase) :
    listJet vs f=ᶠ[𝓝 x] listJet vs g := by
  induction vs with
  | nil => exact same
  | cons v vs ih =>
    have dgerm : fderiv ℝ (listJet vs f)=ᶠ[𝓝 x] fderiv ℝ (listJet vs g) := ih.fderiv
    filter_upwards [dgerm] with y hy
    exact congrArg (fun L : Phase →L[ℝ] ℝ => L v) hy

private theorem listJet_const_nonempty (v : Phase) (vs : List Phase) (c : ℝ) :
    listJet (v::vs) (fun _ => c)=fun _ => 0 := by
  induction vs generalizing v with
  | nil => funext x; simp [listJet,fderiv_const_apply]
  | cons w vs ih =>
    change (fun x => fderiv ℝ (listJet (w::vs) (fun _ => c)) x v)=_
    rw [ih w]
    funext x; simp [fderiv_const_apply]

/-- Exact reciprocal recurrence. The sum removes the unique empty-left split. -/
theorem reciprocal_word_recursion {U : Set Phase} (openU : IsOpen U) (f : Symbol)
    (hf : ContDiffOn ℝ ∞ f U) (hne : ∀ x∈U,f x≠0) (v : Phase) (vs : List Phase)
    (x : Phase) (hx : x∈U) :
    listJet (v::vs) (fun y => (f y)⁻¹) x=
      -(f x)⁻¹ * (((wordSplittings (v::vs)).tail).map
        (splitValue f (fun y => (f y)⁻¹) x)).sum := by
  have hi : ContDiffOn ℝ ∞ (fun y => (f y)⁻¹) U := fun y hy => (hf y hy).inv (hne y hy)
  have germ : (fun y => f y*(f y)⁻¹)=ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [openU.mem_nhds hx] with y hy
    exact mul_inv_cancel₀ (hne y hy)
  have zeroJet : listJet (v::vs) (fun y => f y*(f y)⁻¹) x=0 := by
    rw [(listJet_germ germ (v::vs)).eq_of_nhds,listJet_const_nonempty]
  have convolution := listJet_leibniz openU f (fun y => (f y)⁻¹) hf hi (v::vs) hx
  change listJet (v::vs) (fun y => f y*(f y)⁻¹) x=
    ((wordSplittings (v::vs)).map (splitValue f (fun y => (f y)⁻¹) x)).sum at convolution
  rw [wordSplittings_head,List.map_cons,List.sum_cons] at convolution
  change _=f x*listJet (v::vs) (fun y => (f y)⁻¹) x+_ at convolution
  rw [zeroJet] at convolution
  calc
    _=(f x)⁻¹*(f x*listJet (v::vs) (fun y => (f y)⁻¹) x) := by
      rw [←mul_assoc,inv_mul_cancel₀ (hne x hx),one_mul]
    _=(f x)⁻¹*(-(((wordSplittings (v::vs)).tail).map
        (splitValue f (fun y => (f y)⁻¹) x)).sum) := by
      rw [eq_neg_of_add_eq_zero_left convolution.symm]
    _=_ := by ring

def primitivePole (j : Fin 3) : Symbol := Fin.cases actualC (fun k => Fin.cases actualT (fun _ => sourceDet) k) j

theorem primitivePole_smooth (j : Fin 3) (x : Phase) (hx : x∈poleDomain) :
    ContDiffAt ℝ ∞ (primitivePole j) x := by
  fin_cases j
  · exact actualC_smooth x hx.1
  · exact actualT_smooth x hx.1.1
  · exact sourceDet_smooth x hx.1.1

theorem primitivePole_nonzero (j : Fin 3) (x : Phase) (hx : x∈poleDomain) : primitivePole j x≠0 := by
  fin_cases j
  · exact (C_positive hx.1).ne'
  · exact hx.1.2.2.ne'
  · exact hx.2

theorem source_reciprocal_word (j : Fin 3) (v : Phase) (vs : List Phase) (x : Phase) (hx : x∈poleDomain) :
    listJet (v::vs) (fun y => (primitivePole j y)⁻¹) x=
      -(primitivePole j x)⁻¹ * (((wordSplittings (v::vs)).tail).map
        (splitValue (primitivePole j) (fun y => (primitivePole j y)⁻¹) x)).sum :=
  reciprocal_word_recursion poleDomain_open (primitivePole j)
    (fun y hy => (primitivePole_smooth j y hy).contDiffWithinAt) (primitivePole_nonzero j) v vs x hx

theorem source_reciprocal_canonical (j : Fin 3) (r : ℕ) (w : Word (r+1)) (x : Phase) (hx : x∈poleDomain) :
    jet (r+1) (fun y => (primitivePole j y)⁻¹) w x=
      -(primitivePole j x)⁻¹ * (((wordSplittings (List.ofFn (slotDirection∘w))).tail).map
        (splitValue (primitivePole j) (fun y => (primitivePole j y)⁻¹) x)).sum := by
  have hi : ContDiffOn ℝ ∞ (fun y => (primitivePole j y)⁻¹) poleDomain :=
    fun y hy => ((primitivePole_smooth j y hy).inv (primitivePole_nonzero j y hy)).contDiffWithinAt
  change iteratedFDeriv ℝ (r+1) (fun y => (primitivePole j y)⁻¹) x (slotDirection∘w)=_
  rw [←listJet_ofFn poleDomain_open hi (r+1) (slotDirection∘w) x hx]
  have recurrence := source_reciprocal_word j (slotDirection (w 0))
    (List.ofFn (fun i : Fin r => slotDirection (w i.succ))) x hx
  simpa only [List.ofFn_succ,Function.comp_apply] using recurrence

private theorem abs_sum_map_le (ss : List Split) (f g : Symbol) (x : Phase) :
    |(ss.map (splitValue f g x)).sum|≤(ss.map (fun s => |splitValue f g x s|)).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add le_rfl ih)

theorem source_reciprocal_majorant (j : Fin 3) (r : ℕ) (w : Word (r+1)) (x : Phase) (hx : x∈poleDomain) :
    |jet (r+1) (fun y => (primitivePole j y)⁻¹) w x|≤
      |(primitivePole j x)⁻¹| * (((wordSplittings (List.ofFn (slotDirection∘w))).tail).map
        (fun s => |listJet s.1 (primitivePole j) x| * |listJet s.2 (fun y => (primitivePole j y)⁻¹) x|)).sum := by
  rw [source_reciprocal_canonical j r w x hx,abs_mul,abs_neg]
  have estimate := mul_le_mul_of_nonneg_left
    (abs_sum_map_le ((wordSplittings (List.ofFn (slotDirection∘w))).tail)
      (primitivePole j) (fun y => (primitivePole j y)⁻¹) x) (abs_nonneg ((primitivePole j x)⁻¹))
  simpa only [splitValue,abs_mul] using estimate

theorem actual_engine_inverse_jets (r : ℕ) (w : Word r) (x : Phase) (hx : x∈poleDomain) (a b : Fin 4) :
    jet r (fun y => (PreparationVacuumEngineSource.principalForceJacobian y)⁻¹ a b) w x=
      jet r (fun y => sourceInverse y a b) w x := by
  have germ : (fun y => (PreparationVacuumEngineSource.principalForceJacobian y)⁻¹ a b)=ᶠ[𝓝 x]
      (fun y => sourceInverse y a b) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    rw [sourceInverse_native y hy.1 hy.2]
  exact congrArg (fun D => D (slotDirection∘w)) (germ.iteratedFDeriv ℝ r).eq_of_nhds

end LowEnergy.PreparationVacuumClockSymbol
