import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationMoyalWordBudget

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMoyalBudget
open PreparationVacuumCanonicalMoyal PreparationVacuumMoyalSymmetry PreparationVacuumClockSymbol
open PreparationVacuumEngineSource
open scoped BigOperators ContDiff Topology

def CanonicalList (vs : List Phase) : Prop := ∃ ss : List Slot,vs=ss.map slotDirection

def LeafJetBound (f : Symbol) (N : ℕ) (B : ℕ → ℝ) (x : Phase) : Prop :=
  ∀ n, n≤ N → ∀ w : Word n,|jet n f w x|≤ B n

def listContraction (r : ℕ) (f g : Symbol) : Symbol := fun x =>
  ∑ w : Word r,wordSign w*listJet (List.ofFn (slotDirection∘w)) f x*
    listJet (List.ofFn (slotDirection∘wordSwap r w)) g x

def jordanWeight (r : ℕ) : ℝ :=
  ((Complex.I/2)^r/(r.factorial : ℂ)).re*((1+(-1 : ℝ)^r)/2)

def moyalScale (r : ℕ) : ℝ := (100 : ℝ)^r/(r.factorial : ℝ)

theorem CanonicalList.append {left right : List Phase} (hl : CanonicalList left) (hr : CanonicalList right) :
    CanonicalList (left++right) := by
  obtain ⟨ls,rfl⟩ := hl
  obtain ⟨rs,rfl⟩ := hr
  exact ⟨ls++rs,List.map_append.symm⟩

theorem split_canonical (vs : List Phase) (canonical : CanonicalList vs) (s : Split)
    (member : s∈wordSplittings vs) : CanonicalList s.1 ∧ CanonicalList s.2 := by
  obtain ⟨ss,rfl⟩ := canonical
  induction ss generalizing s with
  | nil =>
    simp [wordSplittings] at member
    subst s
    exact ⟨⟨[],rfl⟩,⟨[],rfl⟩⟩
  | cons t ts ih =>
    rw [List.map_cons,wordSplittings_cons,List.mem_append] at member
    rcases member with member|member
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp member
      have parts := ih p hp
      obtain ⟨rs,hrs⟩ := parts.2
      exact ⟨parts.1,⟨t::rs,by simp only [List.map_cons,←hrs]⟩⟩
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp member
      have parts := ih p hp
      obtain ⟨ls,hls⟩ := parts.1
      exact ⟨⟨t::ls,by simp only [List.map_cons,←hls]⟩,parts.2⟩

theorem canonical_ofFn {r : ℕ} (w : Word r) : CanonicalList (List.ofFn (slotDirection∘w)) :=
  ⟨List.ofFn w,List.map_ofFn.symm⟩

theorem canonical_list_bound {U : Set Phase} (openU : IsOpen U) (f : Symbol)
    (hf : ContDiffOn ℝ ∞ f U) (B : ℕ → ℝ) (x : Phase) (hx : x∈U)
    (N : ℕ) (bound : LeafJetBound f N B x) (vs : List Phase) (canonical : CanonicalList vs)
    (order : vs.length≤ N) :
    |listJet vs f x|≤ B vs.length := by
  obtain ⟨ss,rfl⟩ := canonical
  have replay := listJet_ofFn openU hf ss.length (slotDirection∘ss.get) x hx
  rw [←List.map_ofFn,List.ofFn_get] at replay
  simpa only [List.length_map] using replay ▸ bound ss.length (by simpa only [List.length_map] using order) ss.get

theorem listContraction_smooth {U : Set Phase} (openU : IsOpen U) (r : ℕ) (f g : Symbol)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (listContraction r f g) U := by
  intro x hx
  have fx := (hf x hx).contDiffAt (openU.mem_nhds hx)
  have gx := (hg x hx).contDiffAt (openU.mem_nhds hx)
  apply ContDiffAt.contDiffWithinAt
  exact ContDiffAt.sum (fun w _ =>
    (contDiffAt_const.mul (listJet_smooth _ fx)).mul (listJet_smooth _ gx))

theorem contraction_list {U : Set Phase} (openU : IsOpen U) (r : ℕ) (f g : Symbol)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    Set.EqOn (contraction r f g) (listContraction r f g) U := by
  intro x hx
  unfold contraction listContraction
  apply Finset.sum_congr rfl
  intro w _
  rw [show jet r f w x=listJet (List.ofFn (slotDirection∘w)) f x from
      (listJet_ofFn openU hf r (slotDirection∘w) x hx).symm,
    show jet r g (wordSwap r w) x=listJet (List.ofFn (slotDirection∘wordSwap r w)) g x from
      (listJet_ofFn openU hg r (slotDirection∘wordSwap r w) x hx).symm]

theorem scalarJordan_weight (r : ℕ) (f g : Symbol) :
    scalarJordan r f g=fun x => jordanWeight r*contraction r f g x := by
  funext x
  simp only [scalarJordan,jordan,coefficient]
  rw [contraction_swap r f g x]
  simp only [Complex.ofReal_mul,Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.div_ofNat_re,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,jordanWeight]
  ring

theorem jordanWeight_bound (r : ℕ) : |jordanWeight r|≤(1/2 : ℝ)^r/(r.factorial : ℝ) := by
  have prefactor := Complex.abs_re_le_norm ((Complex.I/2)^r/(r.factorial : ℂ))
  have normfactor : ‖(Complex.I/2)^r/(r.factorial : ℂ)‖=(1/2 : ℝ)^r/(r.factorial : ℝ) := by
    simp [norm_pow]
  rw [normfactor] at prefactor
  have parity : |(1+(-1 : ℝ)^r)/2|≤1 := by
    rw [abs_div]
    norm_num
    have triangle := abs_add_le (1 : ℝ) ((-1 : ℝ)^r)
    simp only [abs_one,abs_pow,abs_neg,one_pow] at triangle
    linarith
  rw [jordanWeight,abs_mul]
  exact (mul_le_mul prefactor parity (abs_nonneg _) (by positivity)).trans_eq (mul_one _)

theorem original_word_count (r : ℕ) : Fintype.card (Word r)=200^r := by
  simp [Word]

theorem contraction_word_budget {U : Set Phase} (openU : IsOpen U) (r m : ℕ) (f g : Symbol)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) (v : Word m)
    (x : Phase) (hx : x∈U) (B D : ℕ → ℝ)
    (nonnegativeB : ∀ n,0≤ B n)
    (boundF : LeafJetBound f (r+m) B x) (boundG : LeafJetBound g (r+m) D x) :
    |listJet (List.ofFn (slotDirection∘v)) (listContraction r f g) x|≤
      (200 : ℝ)^r*convolution m r B D := by
  let vs := List.ofFn (slotDirection∘v)
  let fw := fun w : Word r => listJet (List.ofFn (slotDirection∘w)) f
  let gw := fun w : Word r => listJet (List.ofFn (slotDirection∘wordSwap r w)) g
  have fs (w : Word r) : ContDiffOn ℝ ∞ (fw w) U := fun y hy =>
    (listJet_smooth _ ((hf y hy).contDiffAt (openU.mem_nhds hy))).contDiffWithinAt
  have gs (w : Word r) : ContDiffOn ℝ ∞ (gw w) U := fun y hy =>
    (listJet_smooth _ ((hg y hy).contDiffAt (openU.mem_nhds hy))).contDiffWithinAt
  have signSmooth (w : Word r) : ContDiffOn ℝ ∞ (fun y => wordSign w*(fw w y*gw w y)) U :=
    contDiffOn_const.mul ((fs w).mul (gs w))
  have term (w : Word r) : |listJet vs (fun y => wordSign w*(fw w y*gw w y)) x|≤ convolution m r B D := by
    rw [listJet_scale openU _ _ ((fs w).mul (gs w)) vs hx,abs_mul]
    have sign : |wordSign w|=1 := by
      simp only [wordSign,Finset.abs_prod]
      have each (i : Fin r) : |slotSign (w i)|=1 := by
        cases h : (w i).2 <;> simp [slotSign,h]
      simp [each]
    rw [sign,one_mul]
    have prod := listJet_product_bound openU (fw w) (gw w) (fs w) (gs w) vs x hx r B D nonnegativeB
    have len : vs.length=m := List.length_ofFn
    rw [len] at prod
    apply prod
    · intro s hs
      dsimp only [fw]
      rw [listJet_append]
      have canonical := (split_canonical vs (canonical_ofFn v) s hs).1.append (canonical_ofFn w)
      have estimate := canonical_list_bound openU f hf B x hx (r+m) boundF _ canonical (by
        have count := wordSplittings_lengths vs s hs
        simp only [List.length_append,List.length_ofFn]
        change s.1.length+r≤ r+m
        dsimp [vs] at count
        simp only [List.length_ofFn] at count
        omega)
      simpa only [List.length_append,List.length_ofFn,Nat.add_comm] using estimate
    · intro s hs
      dsimp only [gw]
      rw [listJet_append]
      have canonical := (split_canonical vs (canonical_ofFn v) s hs).2.append (canonical_ofFn (wordSwap r w))
      have estimate := canonical_list_bound openU g hg D x hx (r+m) boundG _ canonical (by
        have count := wordSplittings_lengths vs s hs
        simp only [List.length_append,List.length_ofFn]
        change s.2.length+r≤ r+m
        dsimp [vs] at count
        simp only [List.length_ofFn] at count
        omega)
      simpa only [List.length_append,List.length_ofFn,Nat.add_comm] using estimate
  have source : listContraction r f g=fun y => ∑ w : Word r,wordSign w*(fw w y*gw w y) := by
    funext y
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [source,listJet_sum openU Finset.univ _ (fun w _ => signSmooth w) vs hx]
  calc
    _≤∑ w : Word r,|listJet vs (fun y => wordSign w*(fw w y*gw w y)) x| := Finset.abs_sum_le_sum_abs _ _
    _≤∑ _w : Word r,convolution m r B D := Finset.sum_le_sum (fun w _ => term w)
    _=(200 : ℝ)^r*convolution m r B D := by simp

theorem scalarJordan_canonical_budget {U : Set Phase} (openU : IsOpen U) (r m : ℕ) (f g : Symbol)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) (v : Word m)
    (x : Phase) (hx : x∈U) (B D : ℕ → ℝ)
    (nonnegativeB : ∀ n,0≤ B n)
    (boundF : LeafJetBound f (r+m) B x) (boundG : LeafJetBound g (r+m) D x) :
    |jet m (scalarJordan r f g) v x|≤ moyalScale r*convolution m r B D := by
  have smooth := listContraction_smooth openU r f g hf hg
  have germ : scalarJordan r f g=ᶠ[𝓝 x] (fun y => jordanWeight r*listContraction r f g y) := by
    filter_upwards [openU.mem_nhds hx] with y hy
    rw [scalarJordan_weight]
    change jordanWeight r*contraction r f g y=_
    rw [contraction_list openU r f g hf hg hy]
  have derivative := (germ.iteratedFDeriv ℝ m).eq_of_nhds
  have smoothScaled : ContDiffOn ℝ ∞ (fun y => jordanWeight r*listContraction r f g y) U :=
    contDiffOn_const.mul smooth
  change |iteratedFDeriv ℝ m (scalarJordan r f g) x (slotDirection∘v)|≤_
  rw [derivative,←listJet_ofFn openU smoothScaled m (slotDirection∘v) x hx,
    listJet_scale openU _ _ smooth (List.ofFn (slotDirection∘v)) hx,abs_mul]
  have product := mul_le_mul (jordanWeight_bound r)
    (contraction_word_budget openU r m f g hf hg v x hx B D nonnegativeB boundF boundG)
    (abs_nonneg _) (by positivity : 0≤(1/2 : ℝ)^r/(r.factorial : ℝ))
  have constant : ((1/2 : ℝ)^r/(r.factorial : ℝ))*(200 : ℝ)^r=moyalScale r := by
    rw [←mul_div_right_comm,←mul_pow]
    norm_num [moyalScale]
  simpa only [←mul_assoc,constant] using product

theorem scalarJordan_smooth {U : Set Phase} (openU : IsOpen U) (r : ℕ) (f g : Symbol)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (scalarJordan r f g) U := by
  intro x hx
  have smooth : ContDiffAt ℝ ∞ (fun y => jordanWeight r*listContraction r f g y) x :=
    contDiffAt_const.mul ((listContraction_smooth openU r f g hf hg x hx).contDiffAt (openU.mem_nhds hx))
  apply ContDiffAt.contDiffWithinAt
  apply smooth.congr_of_eventuallyEq
  filter_upwards [openU.mem_nhds hx] with y hy
  rw [scalarJordan_weight]
  change jordanWeight r*contraction r f g y=_
  rw [contraction_list openU r f g hf hg hy]

theorem jet_sum {U : Set Phase} (openU : IsOpen U) {ι : Type} (s : Finset ι) (f : ι → Symbol)
    (hf : ∀ i∈s,ContDiffOn ℝ ∞ (f i) U) (m : ℕ) (v : Word m) (x : Phase) (hx : x∈U) :
    jet m (fun y => ∑ i∈s,f i y) v x=∑ i∈s,jet m (f i) v x := by
  unfold jet
  rw [iteratedFDeriv_fun_sum_apply (fun i hi => ((hf i hi x hx).contDiffAt (openU.mem_nhds hx)).of_le
    (by exact_mod_cast (ENat.natCast_lt_top m).le))]
  simp only [sum_apply]

end LowEnergy.PreparationVacuumMoyalBudget
