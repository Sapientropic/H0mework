import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationArenaComplexJets

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumArenaBudget
open PreparationVacuumCanonicalMoyal PreparationVacuumMoyalSymmetry PreparationVacuumClockSymbol
open PreparationVacuumMoyalBudget
open scoped BigOperators ContDiff Topology

theorem complexListJet_append (left right : List Phase) (f : ComplexSymbol) :
    complexListJet left (complexListJet right f)=complexListJet (left++right) f := by
  simp only [complexListJet,List.foldr_append]

theorem complexListJet_add {U : Set Phase} (openU : IsOpen U) (f g : ComplexSymbol)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) (vs : List Phase) :
    Set.EqOn (complexListJet vs (fun x=>f x+g x))
      (fun x=>complexListJet vs f x+complexListJet vs g x) U := by
  induction vs with
  | nil=>intro x _;rfl
  | cons v vs ih=>
    intro x hx
    have germ : complexListJet vs (fun y=>f y+g y)=ᶠ[𝓝 x]
        (fun y=>complexListJet vs f y+complexListJet vs g y) := by
      filter_upwards [openU.mem_nhds hx] with y hy
      exact ih hy
    have fx:=complexListJet_smooth vs ((hf x hx).contDiffAt (openU.mem_nhds hx))
    have gx:=complexListJet_smooth vs ((hg x hx).contDiffAt (openU.mem_nhds hx))
    change fderiv ℝ (complexListJet vs (fun y=>f y+g y)) x v=_
    rw [germ.fderiv_eq,fderiv_fun_add (fx.differentiableAt (by simp))
      (gx.differentiableAt (by simp)),add_apply]
    rfl

theorem complexListJet_scale {U : Set Phase} (openU : IsOpen U) (c : ℂ) (f : ComplexSymbol)
    (hf : ContDiffOn ℝ ∞ f U) (vs : List Phase) :
    Set.EqOn (complexListJet vs (fun x=>c*f x)) (fun x=>c*complexListJet vs f x) U := by
  induction vs with
  | nil=>intro x _;rfl
  | cons v vs ih=>
    intro x hx
    have germ : complexListJet vs (fun y=>c*f y)=ᶠ[𝓝 x]
        (fun y=>c*complexListJet vs f y) := by
      filter_upwards [openU.mem_nhds hx] with y hy
      exact ih hy
    change fderiv ℝ (complexListJet vs (fun y=>c*f y)) x v=_
    rw [germ.fderiv_eq,fderiv_const_mul ((complexListJet_smooth vs
      ((hf x hx).contDiffAt (openU.mem_nhds hx))).differentiableAt (by simp)) c,
      smul_apply,smul_eq_mul]
    rfl

theorem complexListJet_sum {U : Set Phase} (openU : IsOpen U) {ι : Type*}
    (s : Finset ι) (f : ι → ComplexSymbol) (hf : ∀ i∈s,ContDiffOn ℝ ∞ (f i) U)
    (vs : List Phase) : Set.EqOn (complexListJet vs (fun x=>∑ i∈s,f i x))
      (fun x=>∑ i∈s,complexListJet vs (f i) x) U := by
  classical
  induction s using Finset.induction_on with
  | empty=>
    intro x hx
    simp only [Finset.sum_empty]
    have zero : complexListJet vs (fun _ : Phase=>(0 : ℂ))=(fun _=>0) := by
      induction vs with
      | nil=>rfl
      | cons v vs ih=>
        change (fun y=>fderiv ℝ (complexListJet vs (fun _=>(0 : ℂ))) y v)=_
        rw [ih]
        simp [fderiv_const_apply]
    exact congrFun zero x
  | @insert i s hi ih=>
    have hs : ∀ j∈s,ContDiffOn ℝ ∞ (f j) U:=fun j hj=>hf j (Finset.mem_insert_of_mem hj)
    intro x hx
    simp only [Finset.sum_insert hi]
    rw [complexListJet_add openU (f i) _ (hf i (Finset.mem_insert_self _ _))
      (ContDiffOn.sum (fun j hj=>hs j hj)) vs hx]
    change complexListJet vs (f i) x+complexListJet vs (fun y=>∑ j∈s,f j y) x=_
    rw [ih hs hx]

def complexContraction (r : ℕ) (f g : ComplexSymbol) : ComplexSymbol := fun x=>
  ∑ w : Word r,(wordSign w : ℂ)*complexListJet (List.ofFn (slotDirection∘w)) f x*
    complexListJet (List.ofFn (slotDirection∘wordSwap r w)) g x

def complexCoefficient (r : ℕ) (f g : ComplexSymbol) : ComplexSymbol := fun x=>
  (Complex.I/2)^r/(r.factorial : ℂ)*complexContraction r f g x

theorem complexContraction_smooth {U : Set Phase} (openU : IsOpen U) (r : ℕ)
    (f g : ComplexSymbol) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (complexContraction r f g) U := by
  intro x hx
  have fx:=(hf x hx).contDiffAt (openU.mem_nhds hx)
  have gx:=(hg x hx).contDiffAt (openU.mem_nhds hx)
  exact (ContDiffAt.sum (fun w _=>(contDiffAt_const.mul
    (complexListJet_smooth _ fx)).mul (complexListJet_smooth _ gx))).contDiffWithinAt

def ComplexJetBound (f : ComplexSymbol) (N : ℕ) (B : ℕ → ℝ) (x : Phase) : Prop :=
  ∀ m≤N,∀ w : Word m,‖iteratedFDeriv ℝ m f x (slotDirection∘w)‖≤B m

theorem complex_canonical_list_bound {U : Set Phase} (openU : IsOpen U)
    (f : ComplexSymbol) (hf : ContDiffOn ℝ ∞ f U) (N : ℕ) (B : ℕ → ℝ)
    (x : Phase) (hx : x∈U) (bound : ComplexJetBound f N B x)
    (vs : List Phase) (canonical : PreparationVacuumMoyalBudget.CanonicalList vs)
    (order : vs.length≤N) : ‖complexListJet vs f x‖≤B vs.length := by
  obtain ⟨ss,rfl⟩:=canonical
  have read:=complexListJet_ofFn openU hf ss.length (slotDirection∘ss.get) x hx
  rw [←List.map_ofFn,List.ofFn_get] at read
  simpa only [List.length_map] using read ▸ bound ss.length
    (by simpa only [List.length_map] using order) ss.get

theorem wordSign_norm {r : ℕ} (w : Word r) : ‖(wordSign w : ℂ)‖=1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,wordSign,Finset.abs_prod]
  have term (i : Fin r) : |slotSign (w i)|=1 := by
    unfold slotSign
    split_ifs <;> norm_num
  simp_rw [term]
  simp

theorem complex_coefficient_list_budget {U : Set Phase} (openU : IsOpen U)
    (r : ℕ) (f g : ComplexSymbol) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (vs : List Phase) (canonical : PreparationVacuumMoyalBudget.CanonicalList vs)
    (x : Phase) (hx : x∈U) (B D : ℕ → ℝ) (nonnegativeB : ∀ m,0≤B m)
    (_nonnegativeD : ∀ m,0≤D m)
    (left : ComplexJetBound f (r+vs.length) B x)
    (right : ComplexJetBound g (r+vs.length) D x) :
    ‖complexListJet vs (complexCoefficient r f g) x‖≤
      moyalScale r*convolution vs.length r B D := by
  let atom : Word r → ComplexSymbol:=fun w y=>
    complexListJet (List.ofFn (slotDirection∘w)) f y*
      complexListJet (List.ofFn (slotDirection∘wordSwap r w)) g y
  have fs (w : Word r) : ContDiffOn ℝ ∞
      (complexListJet (List.ofFn (slotDirection∘w)) f) U :=
    fun y hy=>(complexListJet_smooth _ ((hf y hy).contDiffAt (openU.mem_nhds hy))).contDiffWithinAt
  have gs (w : Word r) : ContDiffOn ℝ ∞
      (complexListJet (List.ofFn (slotDirection∘wordSwap r w)) g) U :=
    fun y hy=>(complexListJet_smooth _ ((hg y hy).contDiffAt (openU.mem_nhds hy))).contDiffWithinAt
  have atomBound (w : Word r) : ‖complexListJet vs (atom w) x‖≤convolution vs.length r B D := by
    apply complexListJet_product_bound openU _ _ (fs w) (gs w) vs x hx r B D nonnegativeB
    · intro s hs
      rw [complexListJet_append]
      have length:=wordSplittings_lengths vs s hs
      have bound:=complex_canonical_list_bound openU f hf (r+vs.length) B x hx left
        (s.1++List.ofFn (slotDirection∘w))
        ((split_canonical vs canonical s hs).1.append (canonical_ofFn w))
        (by simp only [List.length_append,List.length_ofFn];omega)
      simpa only [List.length_append,List.length_ofFn,Nat.add_comm] using bound
    · intro s hs
      rw [complexListJet_append]
      have length:=wordSplittings_lengths vs s hs
      have bound:=complex_canonical_list_bound openU g hg (r+vs.length) D x hx right
        (s.2++List.ofFn (slotDirection∘wordSwap r w))
        ((split_canonical vs canonical s hs).2.append (canonical_ofFn (wordSwap r w)))
        (by simp only [List.length_append,List.length_ofFn];omega)
      simpa only [List.length_append,List.length_ofFn,Nat.add_comm] using bound
  have contractionBound : ‖complexListJet vs (complexContraction r f g) x‖≤
      (200 : ℝ)^r*convolution vs.length r B D := by
    have rows : complexContraction r f g=(fun y=>∑ w : Word r,(wordSign w : ℂ)*atom w y) := by
      funext y
      unfold complexContraction atom
      simp_rw [mul_assoc]
    rw [rows]
    rw [complexListJet_sum openU Finset.univ (fun w y=>(wordSign w : ℂ)*atom w y)
      (fun w _=>contDiffOn_const.mul ((fs w).mul (gs w))) vs hx]
    have scaled (w : Word r) :
        complexListJet vs (fun y=>(wordSign w : ℂ)*atom w y) x=
          (wordSign w : ℂ)*complexListJet vs (atom w) x :=
      complexListJet_scale openU (wordSign w : ℂ) (atom w) ((fs w).mul (gs w)) vs hx
    simp_rw [scaled]
    calc
      _≤∑ w : Word r,‖(wordSign w : ℂ)*complexListJet vs (atom w) x‖ := norm_sum_le _ _
      _≤∑ _w : Word r,convolution vs.length r B D := by
        apply Finset.sum_le_sum
        intro w _
        rw [norm_mul,wordSign_norm,one_mul]
        exact atomBound w
      _=(200 : ℝ)^r*convolution vs.length r B D := by
        simp [Word]
  unfold complexCoefficient
  rw [complexListJet_scale openU _ _ (complexContraction_smooth openU r f g hf hg) vs hx,norm_mul]
  have prefactor : ‖(Complex.I/2)^r/(r.factorial : ℂ)‖=(1/2 : ℝ)^r/(r.factorial : ℝ) := by
    simp [norm_pow]
  rw [prefactor]
  have scaled:=mul_le_mul_of_nonneg_left contractionBound
    (by positivity : 0≤(1/2 : ℝ)^r/(r.factorial : ℝ))
  have factor : ((1/2 : ℝ)^r/(r.factorial : ℝ))*(200 : ℝ)^r=moyalScale r := by
    rw [moyalScale,div_mul_eq_mul_div,←mul_pow]
    norm_num
  simpa only [←mul_assoc,factor] using scaled

end LowEnergy.PreparationVacuumArenaBudget
