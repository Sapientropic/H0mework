import H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitShell.HarmonicCount
import Mathlib.MeasureTheory.Integral.Bochner.Set
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

/-- A channel cell carries its actual endpoints before any Pa observation. -/
def cell (lower upper : ℝ) (x : ℝ) : ℂ := (Ico lower upper).indicator (fun _=>1) x

def spanLength (lower upper : ℝ) : ℝ := max (upper-lower) 0

def windowLength (L lower upper : ℝ) : ℝ := spanLength (max lower 0) (min upper L)

def overlapLength (L l u a b : ℝ) : ℝ :=
  windowLength L (max l a) (min u b)

private theorem cell_star (l u x : ℝ) : star (cell l u x)=cell l u x := by
  by_cases h:x∈Ico l u <;> simp [cell,h]

private theorem cell_mul (l u a b x : ℝ) :
    cell l u x*cell a b x=cell (max l a) (min u b) x := by
  change ((Ico l u).indicator (fun _=>1) x)*((Ico a b).indicator (fun _=>1) x)=_
  have together : x∈Ico (max l a) (min u b) ↔ x∈Ico l u ∧ x∈Ico a b := by
    rw [←Ico_inter_Ico];rfl
  by_cases hl:x∈Ico l u <;> by_cases ha:x∈Ico a b <;> simp [cell,together,hl,ha]

private theorem cell_integrable (l u : ℝ) : Integrable (cell l u) :=
  (integrable_indicator_iff measurableSet_Ico).mpr (integrableOn_const (by rw [Real.volume_Ico];exact ENNReal.ofReal_ne_top))

private theorem cell_on (L l u : ℝ) : IntegrableOn (cell l u) (Ico 0 L) :=
  (cell_integrable l u).integrableOn

private theorem cell_pair_on (L l u a b : ℝ) :
    IntegrableOn (fun x => star (cell l u x)*cell a b x) (Ico 0 L) := by
  simp only [cell_star,cell_mul]
  exact cell_on L _ _

/-- The arithmetic overlap length includes empty and reversed intervals. -/
theorem cell_integral (L l u : ℝ) :
    (∫ x : ℝ in Ico 0 L,cell l u x)=(windowLength L l u:ℂ) := by
  unfold cell
  rw [integral_indicator measurableSet_Ico,Measure.restrict_restrict measurableSet_Ico,
    Ico_inter_Ico,setIntegral_const]
  simp only [Measure.real,Real.volume_Ico,ENNReal.toReal_ofReal',windowLength,spanLength]
  rw [Complex.real_smul]
  simp only [mul_one]

theorem cell_pair_integral (L l u a b : ℝ) :
    (∫ x : ℝ in Ico 0 L,star (cell l u x)*cell a b x)=(overlapLength L l u a b:ℂ) := by
  simp only [cell_star,cell_mul]
  exact cell_integral L _ _

def stock {ι : Type*} (s : Finset ι) (coefficient : ι→ℂ) (lower upper : ι→ℝ)
    (mean : ℂ) (x : ℝ) : ℂ :=
  (∑ i∈s,coefficient i*cell (lower i) (upper i) x)-mean

/-- Four rows are kept together: double incidence, both mean crossings and constant mass. -/
def incidence {ι κ : Type*} (L : ℝ) (s : Finset ι) (t : Finset κ)
    (a : ι→ℂ) (l u : ι→ℝ) (mu : ℂ) (b : κ→ℂ) (v w : κ→ℝ) (nu : ℂ) : ℂ :=
  (∑ i∈s,∑ j∈t,star (a i)*b j*(overlapLength L (l i) (u i) (v j) (w j):ℂ))-
  (∑ i∈s,star (a i)*nu*(windowLength L (l i) (u i):ℂ))-
  (∑ j∈t,star mu*b j*(windowLength L (v j) (w j):ℂ))+
  star mu*nu*(spanLength 0 L:ℂ)

private theorem single_pair_integral (L l u a b : ℝ) (z z' : ℂ) :
    (∫ x : ℝ in Ico 0 L,star (z*cell l u x)*(z'*cell a b x))=
      star z*z'*(overlapLength L l u a b:ℂ) := by
  have point (x:ℝ) : star (z*cell l u x)*(z'*cell a b x)=
      (star z*z')*(star (cell l u x)*cell a b x) := by rw [star_mul];ring
  simp_rw [point]
  rw [integral_const_mul,cell_pair_integral]

private theorem single_pair_on (L l u a b : ℝ) (z z' : ℂ) :
    IntegrableOn (fun x => star (z*cell l u x)*(z'*cell a b x)) (Ico 0 L) := by
  have point : (fun x => star (z*cell l u x)*(z'*cell a b x))=
      (fun x => (star z*z')*(star (cell l u x)*cell a b x)) := by
    funext x;rw [star_mul];ring
  rw [point]
  exact (cell_pair_on L l u a b).const_mul _

private theorem sum_on {ι : Type*} (L : ℝ) (s : Finset ι) (a : ι→ℂ) (l u : ι→ℝ) :
    IntegrableOn (fun x => ∑i∈s,a i*cell (l i) (u i) x) (Ico 0 L) :=
  integrable_finsetSum s (fun i _=>(cell_on L (l i) (u i)).const_mul (a i))

private theorem star_on {f : ℝ→ℂ} {L : ℝ}
    (h : IntegrableOn f (Ico 0 L)) : IntegrableOn (fun x => star (f x)) (Ico 0 L) :=
  (Complex.conjCLE : ℂ→L[ℝ]ℂ).integrable_comp h

theorem stock_incidence {ι κ : Type*} (L : ℝ) (s : Finset ι) (t : Finset κ)
    (a : ι→ℂ) (l u : ι→ℝ) (mu : ℂ) (b : κ→ℂ) (v w : κ→ℝ) (nu : ℂ) :
    (∫ x : ℝ in Ico 0 L,star (stock s a l u mu x)*stock t b v w nu x)=
      incidence L s t a l u mu b v w nu := by
  classical
  let left:=fun x => ∑i∈s,a i*cell (l i) (u i) x
  let right:=fun x => ∑j∈t,b j*cell (v j) (w j) x
  have pairOn (i:ι) (hi:i∈s) :
      IntegrableOn (fun x => ∑j∈t,star (a i*cell (l i) (u i) x)*(b j*cell (v j) (w j) x)) (Ico 0 L) :=
    integrable_finsetSum t (fun j _=>single_pair_on L (l i) (u i) (v j) (w j) (a i) (b j))
  have doubleOn : IntegrableOn (fun x => star (left x)*right x) (Ico 0 L) := by
    dsimp only [left,right]
    simp_rw [star_sum,Finset.sum_mul,Finset.mul_sum]
    exact integrable_finsetSum s pairOn
  have leftOn : IntegrableOn (fun x => star (left x)*nu) (Ico 0 L) := (star_on (sum_on L s a l u)).mul_const nu
  have rightOn : IntegrableOn (fun x => star mu*right x) (Ico 0 L) := (sum_on L t b v w).const_mul _
  have point (x:ℝ) : star (stock s a l u mu x)*stock t b v w nu x=
      star (left x)*right x-star (left x)*nu-star mu*right x+star mu*nu := by
    simp only [stock,left,right,star_sub];ring
  simp_rw [point]
  have allIntegral := integral_add ((doubleOn.sub leftOn).sub rightOn)
    (integrableOn_const (C:=star mu*nu) (by rw [Real.volume_Ico];exact ENNReal.ofReal_ne_top))
  have secondIntegral := integral_sub (doubleOn.sub leftOn) rightOn
  have firstIntegral := integral_sub doubleOn leftOn
  simp only [Pi.sub_apply] at allIntegral secondIntegral firstIntegral
  rw [allIntegral,secondIntegral,firstIntegral]
  have both : (∫ x : ℝ in Ico 0 L,star (left x)*right x)=
      ∑i∈s,∑j∈t,star (a i)*b j*(overlapLength L (l i) (u i) (v j) (w j):ℂ) := by
    dsimp only [left,right]
    simp_rw [star_sum,Finset.sum_mul,Finset.mul_sum]
    rw [integral_finsetSum s pairOn]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum t (fun j _=>single_pair_on L (l i) (u i) (v j) (w j) (a i) (b j))]
    exact Finset.sum_congr rfl (fun j _=>single_pair_integral L _ _ _ _ _ _)
  have lc : (∫ x : ℝ in Ico 0 L,star (left x)*nu)=
      ∑i∈s,star (a i)*nu*(windowLength L (l i) (u i):ℂ) := by
    dsimp only [left]
    simp_rw [star_sum,Finset.sum_mul]
    rw [integral_finsetSum s (fun i _=>(star_on ((cell_on L (l i) (u i)).const_mul (a i))).mul_const nu)]
    apply Finset.sum_congr rfl
    intro i _
    have point' (x:ℝ) : star (a i*cell (l i) (u i) x)*nu=(star (a i)*nu)*cell (l i) (u i) x := by
      rw [star_mul,cell_star];ring
    simp_rw [point']
    rw [integral_const_mul,cell_integral]
  have rc : (∫ x : ℝ in Ico 0 L,star mu*right x)=
      ∑j∈t,star mu*b j*(windowLength L (v j) (w j):ℂ) := by
    dsimp only [right]
    simp_rw [Finset.mul_sum,←mul_assoc]
    rw [integral_finsetSum t (fun j _=>(cell_on L (v j) (w j)).const_mul _)]
    simp_rw [integral_const_mul,cell_integral]
  rw [both,lc,rc,setIntegral_const]
  unfold incidence
  simp only [Measure.real,Real.volume_Ico,ENNReal.toReal_ofReal',spanLength,sub_zero,Complex.real_smul]
  congr 1
  ring

/-- The original harmonic interval source supplies every finite cell, with its logarithmic mean. -/
theorem harmonic_window (l u L : ℝ) (hl : 0<l) (hu : 0<u) (x : ℝ)
    (hx : x∈Ico 0 L) :
    burnolHarmonicStepWaveRaw l u x=
      stock (Finset.Icc 1 ⌊L/l⌋₊) (fun n:ℕ=>(n:ℂ)⁻¹)
        (fun n=>(n:ℝ)*l) (fun n=>(n:ℝ)*u) (Real.log (u/l)) x := by
  classical
  have sub : burnolHarmonicStepChannels l u x ⊆ Finset.Icc 1 ⌊L/l⌋₊ := by
    intro n hn
    have bounds:=Finset.mem_Ioc.mp hn
    have positive:1≤n := by omega
    have upper : n≤⌊L/l⌋₊ := bounds.2.trans (Nat.floor_mono (by
      rw [abs_of_nonneg hx.1];exact div_le_div_of_nonneg_right hx.2.le hl.le))
    exact Finset.mem_Icc.mpr ⟨positive,upper⟩
  have incident (n:ℕ) (positive:0<n) :
      n∈burnolHarmonicStepChannels l u x ↔ x∈Ico ((n:ℝ)*l) ((n:ℝ)*u) := by
    simp only [burnolHarmonicStepChannels,Finset.mem_Ioc,Nat.floor_lt' positive.ne',
      Nat.le_floor_iff' positive.ne',abs_of_nonneg hx.1,mem_Ico,
      div_lt_iff₀ hu,le_div_iff₀ hl]
    constructor <;> intro h <;> constructor <;> nlinarith [h.1,h.2]
  unfold burnolHarmonicStepWaveRaw stock
  congr 1
  calc
    _ = ∑n∈burnolHarmonicStepChannels l u x,(n:ℂ)⁻¹*cell ((n:ℝ)*l) ((n:ℝ)*u) x := by
      apply Finset.sum_congr rfl
      intro n hn
      have positive:0<n := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1
      rw [cell,indicator_of_mem ((incident n positive).mp hn),mul_one]
    _ = _ := Finset.sum_subset sub (by
      intro n hn outside
      have positive:0<n := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1
      rw [cell,indicator_of_notMem (fun h=>outside ((incident n positive).mpr h)),mul_zero])

theorem harmonic_window_incidence (l u a b L : ℝ) (hl:0<l) (hu:0<u) (ha:0<a) (hb:0<b) :
    (∫ x : ℝ in Ico 0 L,star (burnolHarmonicStepWaveRaw l u x)*burnolHarmonicStepWaveRaw a b x)=
      incidence L (Finset.Icc 1 ⌊L/l⌋₊) (Finset.Icc 1 ⌊L/a⌋₊)
        (fun n:ℕ=>(n:ℂ)⁻¹) (fun n=>(n:ℝ)*l) (fun n=>(n:ℝ)*u) (Real.log (u/l))
        (fun n:ℕ=>(n:ℂ)⁻¹) (fun n=>(n:ℝ)*a) (fun n=>(n:ℝ)*b) (Real.log (b/a)) := by
  rw [←stock_incidence]
  apply setIntegral_congr_fun measurableSet_Ico
  intro x hx
  dsimp only
  rw [harmonic_window l u L hl hu x hx,harmonic_window a b L ha hb x hx]

end CountedPaInitial
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
