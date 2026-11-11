import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.Incidence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial
open Complex Filter MeasureTheory Set
open scoped BigOperators Topology InnerProductSpace
open private cell_star cell_mul cell_on sum_on star_on from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.Incidence

def reciprocalCell (l u x : ℝ) : ℂ := (x:ℂ)⁻¹*cell l u x

def logWindow (L l u : ℝ) : ℝ := if l≤min u L then Real.log (min u L/l) else 0

private theorem reciprocal_indicator (l u x : ℝ) :
    reciprocalCell l u x=(Ico l u).indicator (fun y:ℝ=>(y:ℂ)⁻¹) x := by
  by_cases h:x∈Ico l u <;> simp [reciprocalCell,cell,h]

private theorem reciprocal_on (L l u : ℝ) (hl:0<l) :
    IntegrableOn (reciprocalCell l u) (Ico 0 L) := by
  have continuous : ContinuousOn (fun x:ℝ=>(x:ℂ)⁻¹) (Icc l u) :=
    continuous_ofReal.continuousOn.inv₀ (fun x hx => Complex.ofReal_ne_zero.mpr (hl.trans_le hx.1).ne')
  have whole : Integrable (reciprocalCell l u) := by
    change Integrable (fun x => reciprocalCell l u x)
    simp_rw [reciprocal_indicator]
    exact (integrable_indicator_iff measurableSet_Ico).mpr
      (continuous.integrableOn_Icc.mono_set Ico_subset_Icc_self)
  exact whole.integrableOn

/-- The actual mixed cell integrates to its interval log ratio, with the empty branch retained. -/
theorem reciprocal_integral (L l u : ℝ) (hl:0<l) :
    (∫ x:ℝ in Ico 0 L,reciprocalCell l u x)=(logWindow L l u:ℂ) := by
  simp_rw [reciprocal_indicator]
  rw [integral_indicator measurableSet_Ico,Measure.restrict_restrict measurableSet_Ico,Ico_inter_Ico,
    max_eq_left hl.le]
  by_cases h:l≤min u L
  · rw [logWindow,if_pos h,integral_Ico_eq_integral_Ioc,←intervalIntegral.integral_of_le h]
    simp_rw [←Complex.ofReal_inv]
    rw [intervalIntegral.integral_ofReal,integral_inv_of_pos hl (hl.trans_le h)]
  · have empty:Ico l (min u L)=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact h (hx.1.trans hx.2.le)
    rw [empty,logWindow,if_neg h]
    simp

private theorem reciprocal_pair (l u a b x : ℝ) :
    star (reciprocalCell l u x)*cell a b x=reciprocalCell (max l a) (min u b) x := by
  calc
    _ = (x:ℂ)⁻¹*(cell l u x*cell a b x) := by
      have real : star (x:ℂ)=(x:ℂ) := Complex.conj_ofReal x
      simp only [reciprocalCell,star_mul,star_inv₀,real,cell_star]
      ring
    _ = _ := by rw [cell_mul];rfl

private theorem reciprocal_star (l u x : ℝ) : star (reciprocalCell l u x)=reciprocalCell l u x := by
  have real : star (x:ℂ)=(x:ℂ) := Complex.conj_ofReal x
  simp only [reciprocalCell,star_mul,star_inv₀,real,cell_star]
  ring

private theorem weighted_pair (l u a b x : ℝ) (z z' : ℂ) :
    star (z*reciprocalCell l u x)*(z'*cell a b x)=
      (star z*z')*reciprocalCell (max l a) (min u b) x := by
  rw [←reciprocal_pair]
  rw [star_mul]
  ring

private theorem reciprocal_pair_on (L l u a b : ℝ) (hl:0<l) (z z':ℂ) :
    IntegrableOn (fun x => star (z*reciprocalCell l u x)*(z'*cell a b x)) (Ico 0 L) := by
  simp_rw [weighted_pair]
  exact (reciprocal_on L _ _ (hl.trans_le (le_max_left l a))).const_mul _

private theorem reciprocal_pair_integral (L l u a b : ℝ) (hl:0<l) (z z':ℂ) :
    (∫ x:ℝ in Ico 0 L,star (z*reciprocalCell l u x)*(z'*cell a b x))=
      star z*z'*(logWindow L (max l a) (min u b):ℂ) := by
  simp_rw [weighted_pair]
  rw [integral_const_mul,reciprocal_integral L _ _ (hl.trans_le (le_max_left l a))]

def reciprocalStock {ι : Type*} (s:Finset ι) (a:ι→ℂ) (l u:ι→ℝ) (mu:ℂ) (x:ℝ) : ℂ :=
  (∑ i∈s,a i*reciprocalCell (l i) (u i) x)-mu

def mixedIncidence {ι κ : Type*} (L:ℝ) (s:Finset ι) (t:Finset κ)
    (a:ι→ℂ) (l u:ι→ℝ) (mu:ℂ) (b:κ→ℂ) (v w:κ→ℝ) (nu:ℂ) : ℂ :=
  (∑ i∈s,∑ j∈t,star (a i)*b j*(logWindow L (max (l i) (v j)) (min (u i) (w j)):ℂ))-
  (∑ i∈s,star (a i)*nu*(logWindow L (l i) (u i):ℂ))-
  (∑ j∈t,star mu*b j*(windowLength L (v j) (w j):ℂ))+
  star mu*nu*(spanLength 0 L:ℂ)

/-- Both ordinary crossing terms are computed on the same finite window as the mixed integer incidence. -/
theorem mixed_stock_incidence {ι κ : Type*} (L:ℝ) (s:Finset ι) (t:Finset κ)
    (a:ι→ℂ) (l u:ι→ℝ) (positive:∀i∈s,0<l i) (mu:ℂ)
    (b:κ→ℂ) (v w:κ→ℝ) (nu:ℂ) :
    (∫ x:ℝ in Ico 0 L,star (reciprocalStock s a l u mu x)*stock t b v w nu x)=
      mixedIncidence L s t a l u mu b v w nu := by
  classical
  let left:=fun x => ∑i∈s,a i*reciprocalCell (l i) (u i) x
  let right:=fun x => ∑j∈t,b j*cell (v j) (w j) x
  have leftInt:IntegrableOn left (Ico 0 L) :=
    integrable_finsetSum s (fun i hi=>(reciprocal_on L (l i) (u i) (positive i hi)).const_mul _)
  have pairOn (i:ι) (hi:i∈s) :
      IntegrableOn (fun x => ∑j∈t,star (a i*reciprocalCell (l i) (u i) x)*(b j*cell (v j) (w j) x)) (Ico 0 L) :=
    integrable_finsetSum t (fun j _=>reciprocal_pair_on L (l i) (u i) (v j) (w j) (positive i hi) (a i) (b j))
  have doubleOn:IntegrableOn (fun x => star (left x)*right x) (Ico 0 L) := by
    dsimp only [left,right]
    simp_rw [star_sum,Finset.sum_mul,Finset.mul_sum]
    exact integrable_finsetSum s pairOn
  have leftOn:IntegrableOn (fun x => star (left x)*nu) (Ico 0 L) := (star_on leftInt).mul_const nu
  have rightOn:IntegrableOn (fun x => star mu*right x) (Ico 0 L) := (sum_on L t b v w).const_mul _
  have point (x:ℝ) : star (reciprocalStock s a l u mu x)*stock t b v w nu x=
      star (left x)*right x-star (left x)*nu-star mu*right x+star mu*nu := by
    simp only [reciprocalStock,stock,left,right,star_sub];ring
  simp_rw [point]
  have allIntegral:=integral_add ((doubleOn.sub leftOn).sub rightOn)
    (integrableOn_const (C:=star mu*nu) (by rw [Real.volume_Ico];exact ENNReal.ofReal_ne_top))
  have secondIntegral:=integral_sub (doubleOn.sub leftOn) rightOn
  have firstIntegral:=integral_sub doubleOn leftOn
  simp only [Pi.sub_apply] at allIntegral secondIntegral firstIntegral
  rw [allIntegral,secondIntegral,firstIntegral]
  have both:(∫ x:ℝ in Ico 0 L,star (left x)*right x)=
      ∑i∈s,∑j∈t,star (a i)*b j*(logWindow L (max (l i) (v j)) (min (u i) (w j)):ℂ) := by
    dsimp only [left,right]
    simp_rw [star_sum,Finset.sum_mul,Finset.mul_sum]
    rw [integral_finsetSum s pairOn]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum t (fun j _=>reciprocal_pair_on L _ _ _ _ (positive i hi) _ _)]
    exact Finset.sum_congr rfl (fun j _=>reciprocal_pair_integral L _ _ _ _ (positive i hi) _ _)
  have lc:(∫ x:ℝ in Ico 0 L,star (left x)*nu)=∑i∈s,star (a i)*nu*(logWindow L (l i) (u i):ℂ) := by
    dsimp only [left]
    simp_rw [star_sum,Finset.sum_mul]
    rw [integral_finsetSum s (fun i hi=>(star_on ((reciprocal_on L _ _ (positive i hi)).const_mul (a i))).mul_const nu)]
    apply Finset.sum_congr rfl
    intro i hi
    have point' (x:ℝ):star (a i*reciprocalCell (l i) (u i) x)*nu=(star (a i)*nu)*reciprocalCell (l i) (u i) x := by
      rw [star_mul,reciprocal_star];ring
    simp_rw [point']
    rw [integral_const_mul,reciprocal_integral L _ _ (positive i hi)]
  have rc:(∫ x:ℝ in Ico 0 L,star mu*right x)=∑j∈t,star mu*b j*(windowLength L (v j) (w j):ℂ) := by
    dsimp only [right]
    simp_rw [Finset.mul_sum,←mul_assoc]
    rw [integral_finsetSum t (fun j _=>(cell_on L (v j) (w j)).const_mul _)]
    simp_rw [integral_const_mul,cell_integral]
  rw [both,lc,rc,setIntegral_const]
  unfold mixedIncidence
  simp only [Measure.real,Real.volume_Ico,ENNReal.toReal_ofReal',spanLength,sub_zero,Complex.real_smul]
  congr 1
  ring

/-- Endpoint conventions are transported a.e.; no endpoint or interval mass is dropped from the bill. -/
theorem reciprocal_window (l u L:ℝ) (hl:0<l) (hu:0<u) :
    burnolReciprocalStepWaveRaw l u =ᵐ[volume.restrict (Ico 0 L)]
      reciprocalStock (Finset.Icc 1 ⌈u*L⌉₊) (fun _=>1)
        (fun n:ℕ=>(n:ℝ)/u) (fun n:ℕ=>(n:ℝ)/l) (u-l) := by
  have endpoints:∀ᵐ x : ℝ ∂volume,∀n:ℕ,x≠(n:ℝ)/u ∧ x≠(n:ℝ)/l :=
    ae_all_iff.mpr (fun n=>(volume.ae_ne ((n:ℝ)/u)).and (volume.ae_ne ((n:ℝ)/l)))
  filter_upwards [ae_restrict_mem measurableSet_Ico,ae_restrict_of_ae (volume.ae_ne (0:ℝ)),
    ae_restrict_of_ae endpoints] with x hx nonzero ends
  have hxpos:0<x:=lt_of_le_of_ne hx.1 (Ne.symm nonzero)
  have subset:burnolReciprocalStepChannels l u x⊆Finset.Icc 1 ⌈u*L⌉₊ := by
    intro n hn
    have bounds:=Finset.mem_Ico.mp hn
    have first:0<n := lt_of_lt_of_le (Nat.ceil_pos.mpr (by rw [abs_of_pos hxpos];positivity)) bounds.1
    have second:n≤⌈u*L⌉₊ := bounds.2.le.trans (Nat.ceil_mono (by rw [abs_of_pos hxpos];nlinarith [hx.2]))
    exact Finset.mem_Icc.mpr ⟨first,second⟩
  have incident (n:ℕ) : n∈burnolReciprocalStepChannels l u x ↔ x∈Ico ((n:ℝ)/u) ((n:ℝ)/l) := by
    simp only [burnolReciprocalStepChannels,Finset.mem_Ico,Nat.ceil_le,Nat.lt_ceil,abs_of_pos hxpos,mem_Ico]
    constructor
    · intro h
      have lower:(n:ℝ)/u<x := (div_lt_iff₀ hu).mpr (by nlinarith [h.2])
      have upper:x≤(n:ℝ)/l := (le_div_iff₀ hl).mpr (by nlinarith [h.1])
      exact ⟨lower.le,lt_of_le_of_ne upper (ends n).2⟩
    · intro h
      have lower:(n:ℝ)/u<x:=lt_of_le_of_ne h.1 (Ne.symm (ends n).1)
      have a:= (div_lt_iff₀ hu).mp lower
      have b:= (lt_div_iff₀ hl).mp h.2
      exact ⟨by nlinarith,by nlinarith⟩
  rw [burnolReciprocalStepWave_coSum l u x hl,
    burnolReciprocalStep_forward_count l u x hl nonzero,abs_of_pos hxpos]
  unfold reciprocalStock
  rw [←nsmul_eq_mul,←Finset.sum_const]
  congr 1
  calc
    _ = ∑n∈burnolReciprocalStepChannels l u x,1*reciprocalCell ((n:ℝ)/u) ((n:ℝ)/l) x := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [reciprocalCell,cell,indicator_of_mem ((incident n).mp hn),mul_one,one_mul]
    _ = _ := Finset.sum_subset subset (by
      intro n _ outside
      rw [reciprocalCell,cell,indicator_of_notMem (fun h=>outside ((incident n).mpr h)),mul_zero,mul_zero])

theorem mixed_window_incidence (l u a b L:ℝ) (hl:0<l) (hu:0<u) (ha:0<a) (hb:0<b) :
    (∫ x:ℝ in Ico 0 L,star (burnolReciprocalStepWaveRaw l u x)*burnolHarmonicStepWaveRaw a b x)=
      mixedIncidence L (Finset.Icc 1 ⌈u*L⌉₊) (Finset.Icc 1 ⌊L/a⌋₊)
        (fun _=>1) (fun n:ℕ=>(n:ℝ)/u) (fun n:ℕ=>(n:ℝ)/l) (u-l)
        (fun n:ℕ=>(n:ℂ)⁻¹) (fun n=>(n:ℝ)*a) (fun n=>(n:ℝ)*b) (Real.log (b/a)) := by
  rw [←mixed_stock_incidence L _ _ _ _ _ (by intro n hn;exact div_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1)) hu)]
  apply integral_congr_ae
  filter_upwards [reciprocal_window l u L hl hu,ae_restrict_mem measurableSet_Ico] with x source hx
  rw [source,harmonic_window a b L ha hb x hx]

end CountedPaInitial
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
