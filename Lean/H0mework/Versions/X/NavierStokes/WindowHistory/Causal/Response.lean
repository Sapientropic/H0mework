import H0mework.Versions.X.NavierStokes.WindowHistory.Causal.Flow

set_option autoImplicit false
open scoped Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCausalResponse
open Set MeasureTheory
open NativeWindowHistoryPropagator
noncomputable section

section Generated
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def block (A : ℝ → E →L[ℝ] E) (f : ℝ → E) (t : ℝ) : E × ℝ →L[ℝ] E × ℝ :=
  (ContinuousLinearMap.inl ℝ E ℝ).comp
    ((A t).comp (ContinuousLinearMap.fst ℝ E ℝ)+
      (ContinuousLinearMap.snd ℝ E ℝ).smulRight (f t))

omit [CompleteSpace E] in
theorem block_apply (A : ℝ → E →L[ℝ] E) (f : ℝ → E) (t : ℝ) (x : E × ℝ) :
    block A f t x=(A t x.1+x.2 • f t,0) := rfl

omit [CompleteSpace E] in
theorem block_continuous (A : ℝ → E →L[ℝ] E) (Ac : Continuous A)
    (f : ℝ → E) (fc : Continuous f) : Continuous (block A f) :=
  Continuous.clm_comp continuous_const ((Ac.clm_comp continuous_const).add
    (((ContinuousLinearMap.smulRightL ℝ (E × ℝ) E) (ContinuousLinearMap.snd ℝ E ℝ)).continuous.comp fc))

def lifted (A : ℝ → E →L[ℝ] E) (Ac : Continuous A) (f : ℝ → E) (fc : Continuous f)
    (a B : ℝ) (aB : a≤B) (t : ℝ) : E × ℝ :=
  matrix (block A f) (block_continuous A Ac f fc) a B aB t (0,1)

theorem lifted_initial (A : ℝ → E →L[ℝ] E) (Ac : Continuous A) (f : ℝ → E) (fc : Continuous f)
    (a B : ℝ) (aB : a≤B) : lifted A Ac f fc a B aB a=(0,1) := by
  unfold lifted
  rw [matrix_initial]
  rfl

theorem lifted_derivative (A : ℝ → E →L[ℝ] E) (Ac : Continuous A) (f : ℝ → E) (fc : Continuous f)
    (a B : ℝ) (aB : a≤B) (t : ℝ) (inside : t∈Icc a B) :
    HasDerivWithinAt (lifted A Ac f fc a B aB)
      (block A f t (lifted A Ac f fc a B aB t)) (Icc a B) t :=
  applied_derivative _ _ a B aB (0,1) t inside

theorem lifted_clock (A : ℝ → E →L[ℝ] E) (Ac : Continuous A) (f : ℝ → E) (fc : Continuous f)
    (a B : ℝ) (aB : a≤B) (t : ℝ) (inside : t∈Icc a B) :
    (lifted A Ac f fc a B aB t).2=1 := by
  let z := fun s => (lifted A Ac f fc a B aB s).2
  have dz (s : ℝ) (hs : s∈Icc a B) : HasDerivWithinAt z 0 (Icc a B) s := by
    exact (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt.comp_hasDerivWithinAt s
      (lifted_derivative A Ac f fc a B aB s hs)
  have zc : ContinuousOn z (Icc a t) := fun s hs =>
    ((dz s ⟨hs.1,hs.2.trans inside.2⟩).mono (Icc_subset_Icc le_rfl inside.2)).continuousWithinAt
  have written := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le inside.1 zc
    (fun s hs => (dz s ⟨hs.1.le,hs.2.le.trans inside.2⟩).hasDerivAt
      (Icc_mem_nhds hs.1 (hs.2.trans_le inside.2))) (intervalIntegrable_const (c := (0 : ℝ)))
  have initial : z a=1 := congrArg Prod.snd (lifted_initial A Ac f fc a B aB)
  rw [intervalIntegral.integral_zero,initial] at written
  exact sub_eq_zero.mp written.symm

def response (A : ℝ → E →L[ℝ] E) (Ac : Continuous A) (f : ℝ → E) (fc : Continuous f)
    (a B : ℝ) (aB : a≤B) (t : ℝ) : E := (lifted A Ac f fc a B aB t).1

theorem response_initial (A : ℝ → E →L[ℝ] E) (Ac : Continuous A) (f : ℝ → E) (fc : Continuous f)
    (a B : ℝ) (aB : a≤B) : response A Ac f fc a B aB a=0 :=
  congrArg Prod.fst (lifted_initial A Ac f fc a B aB)

theorem response_derivative (A : ℝ → E →L[ℝ] E) (Ac : Continuous A) (f : ℝ → E) (fc : Continuous f)
    (a B : ℝ) (aB : a≤B) (t : ℝ) (inside : t∈Icc a B) :
    HasDerivWithinAt (response A Ac f fc a B aB)
      (A t (response A Ac f fc a B aB t)+f t) (Icc a B) t := by
  have actual := (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt.comp_hasDerivWithinAt t
    (lifted_derivative A Ac f fc a B aB t inside)
  change HasDerivWithinAt (response A Ac f fc a B aB)
    (A t (response A Ac f fc a B aB t)+(lifted A Ac f fc a B aB t).2 • f t) (Icc a B) t at actual
  simpa only [lifted_clock A Ac f fc a B aB t inside,one_smul] using actual

theorem response_continuous (A : ℝ → E →L[ℝ] E) (Ac : Continuous A) (f : ℝ → E) (fc : Continuous f)
    (a B : ℝ) (aB : a≤B) : ContinuousOn (response A Ac f fc a B aB) (Icc a B) :=
  fun t ht => (response_derivative A Ac f fc a B aB t ht).continuousWithinAt
end Generated

section Energy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem response_energy (A : ℝ → E →L[ℝ] E) (Ac : Continuous A) (f : ℝ → E) (fc : Continuous f)
    (a B : ℝ) (aB : a≤B) (b : ℝ) (inside : b∈Icc a B) :
    (∫ t in a..b,inner ℝ (f t) (response A Ac f fc a B aB t))=
      ‖response A Ac f fc a B aB b‖^2/2-
        ∫ t in a..b,inner ℝ (response A Ac f fc a B aB t) (A t (response A Ac f fc a B aB t)) := by
  let r := response A Ac f fc a B aB
  have rc : ContinuousOn r (Icc a b) :=
    (response_continuous A Ac f fc a B aB).mono (Icc_subset_Icc le_rfl inside.2)
  have work := (fc.continuousOn.inner (𝕜 := ℝ) rc).intervalIntegrable_of_Icc (μ := volume) inside.1
  have diss := (rc.inner (𝕜 := ℝ) (Ac.continuousOn.clm_apply rc)).intervalIntegrable_of_Icc (μ := volume) inside.1
  have energy (t : ℝ) (ht : t∈Ioo a b) :
      HasDerivAt (fun s => ‖r s‖^2) (2*inner ℝ (r t) (A t (r t))+2*inner ℝ (f t) (r t)) t := by
    have actual := (response_derivative A Ac f fc a B aB t ⟨ht.1.le,ht.2.le.trans inside.2⟩).hasDerivAt
      (Icc_mem_nhds ht.1 (ht.2.trans_le inside.2))
    convert actual.norm_sq using 1
    rw [inner_add_right,real_inner_comm (f t) (r t)]
    ring
  have written := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le inside.1 (rc.norm.pow 2)
    energy ((diss.const_mul 2).add (work.const_mul 2))
  rw [intervalIntegral.integral_add (diss.const_mul 2) (work.const_mul 2),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at written
  have initial : r a=0 := response_initial A Ac f fc a B aB
  simp only [Pi.pow_apply] at written
  rw [initial,norm_zero,zero_pow (by decide),sub_zero] at written
  linarith only [written]

theorem response_passive (A : ℝ → E →L[ℝ] E) (Ac : Continuous A)
    (dissipative : ∀ t u,inner ℝ u (A t u)≤0) (f : ℝ → E) (fc : Continuous f)
    (a B : ℝ) (aB : a≤B) (b : ℝ) (inside : b∈Icc a B) :
    0≤∫ t in a..b,inner ℝ (f t) (response A Ac f fc a B aB t) := by
  rw [response_energy A Ac f fc a B aB b inside]
  have nonpositive : (∫ t in a..b,inner ℝ (response A Ac f fc a B aB t)
      (A t (response A Ac f fc a B aB t)))≤0 := by
    have paid := intervalIntegral.integral_nonneg_of_forall (μ := volume) inside.1
      (fun t => neg_nonneg.mpr (dissipative t (response A Ac f fc a B aB t)))
    rw [intervalIntegral.integral_neg] at paid
    exact neg_nonneg.mp paid
  exact sub_nonneg.mpr (nonpositive.trans (div_nonneg (sq_nonneg _) (by norm_num)))
end Energy
end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCausalResponse
