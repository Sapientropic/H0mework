import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedIRAnalytic

set_option autoImplicit false
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedIRReturn
open CanonicalGradedSpatialSource GaussCoreHilbert
open ActualDressedStaticPole ActualDressedFullCoulomb ActualDressedSylvester ActualDressedObservedPolePrice
open Set Filter
open scoped Topology BigOperators Matrix.Norms.Elementwise
attribute [local irreducible] dressedStaticPoleOrder dressedStaticPoleRegular dressedStaticPolarization observedStaticSourcePrice

private theorem analytic_order_from_real_price {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ→E) (hf : AnalyticAt ℂ f 0) (k : ℕ) (K : ℝ)
    (bound : ∀ᶠs : ℝ in nhdsWithin 0 (Ioi (0:ℝ)),‖f (s:ℂ)‖ ≤ s^k*K) :
    (k:ℕ∞) ≤ analyticOrderAt f 0 := by
  by_cases zero : ∀ᶠz : ℂ in 𝓝 0,f z=0
  · rw [analyticOrderAt_eq_top.mpr zero]
    exact le_top
  · obtain ⟨n,g,hg,nonzero,factor⟩:=hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr zero
    have order : analyticOrderAt f 0=(n:ℕ∞):=hf.analyticOrderAt_eq_natCast.mpr ⟨g,hg,nonzero,factor⟩
    rw [order,ENat.natCast_le_natCast]
    by_contra small
    have gap : 0<k-n:=Nat.sub_pos_of_lt (lt_of_not_ge small)
    have embedding : Tendsto (fun s : ℝ => (s:ℂ)) (nhdsWithin 0 (Ioi (0:ℝ))) (𝓝 (0:ℂ)):=
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
    have convergence : Tendsto (fun s : ℝ => s^(k-n)*K) (nhdsWithin 0 (Ioi (0:ℝ))) (𝓝 0) := by
      have identity : Tendsto (fun s : ℝ => s) (nhdsWithin 0 (Ioi (0:ℝ))) (𝓝 (0:ℝ)):=tendsto_id.mono_left inf_le_left
      simpa only [zero_pow gap.ne',zero_mul] using (identity.pow (k-n)).mul_const K
    have vanishing : Tendsto (fun s : ℝ => g (s:ℂ)) (nhdsWithin 0 (Ioi (0:ℝ))) (𝓝 0) := by
      apply squeeze_zero_norm' _ convergence
      filter_upwards [self_mem_nhdsWithin,bound,embedding.eventually factor] with s positive paid generated
      rw [sub_zero] at generated
      rw [generated,norm_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive] at paid
      have split : k=n+(k-n):=by omega
      rw [split,pow_add,mul_assoc] at paid
      exact le_of_mul_le_mul_left paid (pow_pos positive n)
    exact nonzero (tendsto_nhds_unique (hg.continuousAt.tendsto.comp embedding) vanishing)

def actualIRSourcePrice (event : DressedEvent) : ℝ :=
  ∑i : Fin 289,∑j : Fin 289,observedStaticSourcePrice event 0 i j
attribute [local irreducible] actualIRSourcePrice

theorem actual_ir_source_price_nonneg (event : DressedEvent) : 0 ≤ actualIRSourcePrice event := by
  unfold actualIRSourcePrice
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => observed_static_source_price_nonneg event 0 i j))

private theorem entry_price_le_total (event : DressedEvent) (i j : Fin 289) :
    observedStaticSourcePrice event 0 i j ≤ actualIRSourcePrice event := by
  unfold actualIRSourcePrice
  exact (Finset.single_le_sum (fun k _ => observed_static_source_price_nonneg event 0 i k) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => observed_static_source_price_nonneg event 0 k l)) (Finset.mem_univ i))

theorem actual_regular_matrix_real_price (event : DressedEvent) (high : 6 ≤ 2*dressedStaticPoleOrder event)
    (s : ℝ) (positive : 0<s) (small : s ≤ 1) :
    ‖dressedStaticPoleRegular event (s:ℂ)‖ ≤ s^(2*dressedStaticPoleOrder event-6)*actualIRSourcePrice event := by
  have hp : 0 ≤ s^(2*dressedStaticPoleOrder event-6)*actualIRSourcePrice event:=
    mul_nonneg (pow_nonneg positive.le _) (actual_ir_source_price_nonneg event)
  rw [pi_norm_le_iff_of_nonneg hp]
  intro i
  rw [pi_norm_le_iff_of_nonneg hp]
  intro j
  have returned:=dressed_static_polarization_regularized event (s:ℂ) positive i j
  have paid:=actual_static_polarization_sigma_six_price event 0 s positive small i j
  have split : 2*dressedStaticPoleOrder event=(2*dressedStaticPoleOrder event-6)+6:=by omega
  calc
    _=s^(2*dressedStaticPoleOrder event)*‖dressedStaticPolarization event 0 (s:ℂ) i j‖:=by
      rw [←returned,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
    _=s^(2*dressedStaticPoleOrder event-6)*(s^6*‖dressedStaticPolarization event 0 (s:ℂ) i j‖):=by
      conv_lhs => rw [split,pow_add,mul_assoc]
    _ ≤ s^(2*dressedStaticPoleOrder event-6)*observedStaticSourcePrice event 0 i j:=
      mul_le_mul_of_nonneg_left paid (pow_nonneg positive.le _)
    _ ≤ _:=mul_le_mul_of_nonneg_left (entry_price_le_total event i j) (pow_nonneg positive.le _)

/-- Source sixth-order price removes every higher coefficient of this same actual regularized matrix. -/
theorem actual_regular_matrix_order_lower (event : DressedEvent) :
    (((2*dressedStaticPoleOrder event-6):ℕ):ℕ∞) ≤ analyticOrderAt (dressedStaticPoleRegular event) 0 := by
  by_cases high : 6 ≤ 2*dressedStaticPoleOrder event
  · apply analytic_order_from_real_price _ (actual_regular_matrix_analytic event) _ (actualIRSourcePrice event)
    have small : ∀ᶠs : ℝ in nhdsWithin 0 (Ioi (0:ℝ)),s<1:=
      (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono inf_le_left
    filter_upwards [self_mem_nhdsWithin,small] with s positive near
    exact actual_regular_matrix_real_price event high s positive near.le
  · have trivial : 2*dressedStaticPoleOrder event-6=0:=by omega
    rw [trivial,Nat.cast_zero]
    exact bot_le

theorem actual_regular_matrix_factor (event : DressedEvent) :
    ∃G : ℂ→Matrix (Fin 289) (Fin 289) ℂ,AnalyticAt ℂ G 0 ∧
      ∀ᶠz : ℂ in 𝓝 0,dressedStaticPoleRegular event z=z^(2*dressedStaticPoleOrder event-6) • G z := by
  have source:=(natCast_le_analyticOrderAt (actual_regular_matrix_analytic event)).mp (actual_regular_matrix_order_lower event)
  simpa only [sub_zero] using source

end LowEnergy.GaussComposite.ActualDressedIRReturn
