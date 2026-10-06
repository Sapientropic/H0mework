import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationMoyalCanonicalBudget

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumArenaBudget
open PreparationVacuumCanonicalMoyal PreparationVacuumMoyalSymmetry PreparationVacuumClockSymbol
open PreparationVacuumMoyalBudget
open scoped BigOperators ContDiff Topology

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev ComplexSymbol := Phase → ℂ

def complexListJet (vs : List Phase) (f : ComplexSymbol) : ComplexSymbol :=
  vs.foldr (fun v g x=>fderiv ℝ g x v) f

theorem complexListJet_smooth (vs : List Phase) {f : ComplexSymbol} {x : Phase}
    (smooth : ContDiffAt ℝ ∞ f x) : ContDiffAt ℝ ∞ (complexListJet vs f) x := by
  induction vs with
  | nil=>exact smooth
  | cons v vs ih=>exact (ih.fderiv_right (by simp)).clm_apply contDiffAt_const

theorem complexListJet_germ {f g : ComplexSymbol} {x : Phase}
    (same : f=ᶠ[𝓝 x] g) (vs : List Phase) : complexListJet vs f=ᶠ[𝓝 x] complexListJet vs g := by
  induction vs with
  | nil=>exact same
  | cons v vs ih=>
    have derivative : fderiv ℝ (complexListJet vs f)=ᶠ[𝓝 x] fderiv ℝ (complexListJet vs g):=ih.fderiv
    filter_upwards [derivative] with y hy
    exact congrArg (fun L : Phase →L[ℝ] ℂ=>L v) hy

theorem complexListJet_ofFn {U : Set Phase} (openU : IsOpen U) {f : ComplexSymbol}
    (smooth : ContDiffOn ℝ ∞ f U) (r : ℕ) (v : Fin r → Phase) (x : Phase) (hx : x∈U) :
    complexListJet (List.ofFn v) f x=iteratedFDeriv ℝ r f x v := by
  induction r generalizing x with
  | zero=>simp [complexListJet]
  | succ r ih=>
    rw [List.ofFn_succ]
    change fderiv ℝ (complexListJet (List.ofFn (Fin.tail v)) f) x (v 0)=_
    have germ : complexListJet (List.ofFn (Fin.tail v)) f=ᶠ[𝓝 x]
        (fun y=>iteratedFDeriv ℝ r f y (Fin.tail v)) := by
      filter_upwards [openU.mem_nhds hx] with y hy
      exact ih (Fin.tail v) y hy
    rw [germ.fderiv_eq]
    have hf : ContDiffAt ℝ ∞ f x:=(smooth x hx).contDiffAt (openU.mem_nhds hx)
    have derivative : DifferentiableAt ℝ (iteratedFDeriv ℝ r f) x:=
      hf.differentiableAt_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top r)
    exact derivative.iteratedFDeriv_succ_apply_left'.symm

def complexSplitValue (f g : ComplexSymbol) (x : Phase) (s : Split) : ℂ :=
  complexListJet s.1 f x*complexListJet s.2 g x

private theorem complex_sum_derivative (ss : List Split) (f g : ComplexSymbol) (x v : Phase)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    fderiv ℝ (fun y=>(ss.map (complexSplitValue f g y)).sum) x v=
      (ss.map (fun s=>complexSplitValue f g x (s.1,v::s.2)+
        complexSplitValue f g x (v::s.1,s.2))).sum := by
  induction ss with
  | nil=>simp [fderiv_const_apply]
  | cons s ss ih=>
    have tail : ContDiffAt ℝ ∞ (fun y=>(ss.map (complexSplitValue f g y)).sum) x := by
      clear ih
      induction ss with
      | nil=>exact contDiffAt_const
      | cons t ts ht=>
        simpa only [List.map_cons,List.sum_cons,complexSplitValue] using!
          ((complexListJet_smooth t.1 hf).mul (complexListJet_smooth t.2 hg)).add ht
    simp only [List.map_cons,List.sum_cons]
    simp only [complexSplitValue] at ih ⊢
    rw [fderiv_fun_add (((complexListJet_smooth s.1 hf).mul
      (complexListJet_smooth s.2 hg)).differentiableAt (by simp))
      (tail.differentiableAt (by simp)),add_apply,ih]
    rw [fderiv_fun_mul ((complexListJet_smooth s.1 hf).differentiableAt (by simp))
      ((complexListJet_smooth s.2 hg).differentiableAt (by simp))]
    simp only [add_apply,smul_apply,smul_eq_mul,complexListJet,List.foldr_cons]
    ring

theorem complexListJet_leibniz {U : Set Phase} (openU : IsOpen U) (f g : ComplexSymbol)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) (vs : List Phase) :
    Set.EqOn (complexListJet vs (fun x=>f x*g x))
      (fun x=>((wordSplittings vs).map (complexSplitValue f g x)).sum) U := by
  induction vs with
  | nil=>intro x _;simp [wordSplittings,complexListJet,complexSplitValue]
  | cons v vs ih=>
    intro x hx
    have germ : complexListJet vs (fun y=>f y*g y)=ᶠ[𝓝 x]
        (fun y=>((wordSplittings vs).map (complexSplitValue f g y)).sum) := by
      filter_upwards [openU.mem_nhds hx] with y hy
      exact ih hy
    change fderiv ℝ (complexListJet vs (fun y=>f y*g y)) x v=_
    rw [germ.fderiv_eq,complex_sum_derivative _ _ _ _ _
      ((hf x hx).contDiffAt (openU.mem_nhds hx)) ((hg x hx).contDiffAt (openU.mem_nhds hx))]
    simp only [wordSplittings_cons,List.map_append,List.sum_append,List.map_map,
      Function.comp_def,List.sum_map_add]

private theorem complex_norm_sum_bound (ss : List Split) (F : Split → ℂ) (B : Split → ℝ)
    (bounds : ∀ s∈ss,‖F s‖≤B s) : ‖(ss.map F).sum‖≤(ss.map B).sum := by
  induction ss with
  | nil=>simp
  | cons s ss ih=>
    simp only [List.map_cons,List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add (bounds s (by simp))
      (ih (fun t ht=>bounds t (by simp [ht]))))

theorem complexListJet_product_bound {U : Set Phase} (openU : IsOpen U) (f g : ComplexSymbol)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) (vs : List Phase)
    (x : Phase) (hx : x∈U) (r : ℕ) (B D : ℕ → ℝ) (nonnegative : ∀ n,0≤B n)
    (left : ∀ s∈wordSplittings vs,‖complexListJet s.1 f x‖≤B (r+s.1.length))
    (right : ∀ s∈wordSplittings vs,‖complexListJet s.2 g x‖≤D (r+s.2.length)) :
    ‖complexListJet vs (fun y=>f y*g y) x‖≤convolution vs.length r B D := by
  rw [complexListJet_leibniz openU f g hf hg vs hx]
  have bound:=complex_norm_sum_bound (wordSplittings vs) (complexSplitValue f g x)
    (fun s=>B (r+s.1.length)*D (r+s.2.length)) (by
      intro s hs
      rw [complexSplitValue,norm_mul]
      exact mul_le_mul (left s hs) (right s hs) (norm_nonneg _) (nonnegative _))
  rw [split_convolution] at bound
  exact bound

end LowEnergy.PreparationVacuumArenaBudget
