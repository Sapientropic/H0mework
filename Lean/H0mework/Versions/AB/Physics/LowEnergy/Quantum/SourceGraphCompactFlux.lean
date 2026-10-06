import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussGradedUnitary

/-! Graph-compact observables remove the original compression flux on source orbits. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.FullYSourceGraphCompactFlux
open Filter SourceFamilyHilbert SourceFamilyOperator
open scoped Topology InnerProductSpace

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem flux_error (C A B A₀ B₀ : E →L[ℂ] E)
    (hC : ∀ x y, inner ℂ (C x) y=inner ℂ x (C y))
    (hAB : C*A₀=B₀) (u v w : E) (hw : C v=w) :
    ‖inner ℂ (B u) v-inner ℂ (A u) w‖ ≤
      ‖B-B₀‖*‖u‖*‖v‖+‖A-A₀‖*‖u‖*‖w‖ := by
  have he : inner ℂ (B₀ u) v=inner ℂ (A₀ u) w := by
    rw [←hAB,mul_apply_eq_comp,hC,hw]
  have hs : inner ℂ (B u) v-inner ℂ (A u) w=
      inner ℂ ((B-B₀) u) v-inner ℂ ((A-A₀) u) w := by
    simp only [sub_apply,inner_sub_left]
    rw [he]
    abel
  rw [hs]
  calc
    _ ≤ ‖inner ℂ ((B-B₀) u) v‖+‖inner ℂ ((A-A₀) u) w‖ := norm_sub_le _ _
    _ ≤ ‖(B-B₀) u‖*‖v‖+‖(A-A₀) u‖*‖w‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right ((B-B₀).le_opNorm u) (norm_nonneg v))
      (mul_le_mul_of_nonneg_right ((A-A₀).le_opNorm u) (norm_nonneg w))

theorem lifted_graph_pair {I : Type*} (l : Ultrafilter I) (A B : E →L[ℂ] E)
    (f g h : Family E l)
    (zero : Tendsto (fun i => inner ℂ (B (value f i)) (value g i)-
      inner ℂ (A (value f i)) (value h i)) l (𝓝 0)) :
    inner ℂ (lift l (SourceFamilyOperator.constant B) (f : Hilbert E l)) (g : Hilbert E l)=
      inner ℂ (lift l (SourceFamilyOperator.constant A) (f : Hilbert E l)) (h : Hilbert E l) := by
  rw [lift_coe,lift_coe,inner_coe,inner_coe]
  apply sub_eq_zero.mp
  exact tendsto_nhds_unique
    ((pair_tendsto l (act l (SourceFamilyOperator.constant B) f) g).sub
      (pair_tendsto l (act l (SourceFamilyOperator.constant A) f) h)) zero

end Hilbert

open GaussCoreHilbert GaussDiagonalHistory
open GaussUnitaryHistory (Index HistorySpace sourceFilter reader inclusion)

structure CoreColumns where
  count : ℕ
  column : Fin count → diagonal.domain
  coefficient : Fin count → H →L[ℂ] ℂ

def CoreColumns.action (a : CoreColumns) : H →L[ℂ] H :=
  ∑ j, (a.coefficient j).smulRight (a.column j : H)

def CoreColumns.graphAction (a : CoreColumns) : H →L[ℂ] H :=
  ∑ j, (a.coefficient j).smulRight (diagonal (a.column j))

theorem columns_eventually_exact (a : CoreColumns) :
    ∀ᶠ F in (sourceFilter : Filter Index),
      GaussGradedCompression.compression F*a.action=a.graphAction := by
  have h := Filter.eventually_all.mpr (fun j : Fin a.count =>
    GaussGradedCompression.eventually_exact (a.column j))
  filter_upwards [h] with F hF
  apply ContinuousLinearMap.ext
  intro x
  simp only [CoreColumns.action,CoreColumns.graphAction,mul_apply_eq_comp,
    sum_apply,map_sum,ContinuousLinearMap.smulRight_apply,map_smul]
  exact Finset.sum_congr rfl (fun j _ => congrArg ((a.coefficient j x) • ·) (hF j))

/-- A simultaneous operator-norm approximation in the original minimal graph. -/
def CoreGraphApproximation (A B : H →L[ℂ] H) : Prop :=
  ∀ ε : ℝ, 0<ε → ∃ a : CoreColumns, ‖A-a.action‖≤ε ∧ ‖B-a.graphAction‖≤ε

def finiteOrbit (F : Index) (t : ℝ) (f : H) : H :=
  SourceFiniteUnitary.time (GaussGradedCompression.compression F) t f

theorem finite_orbit_norm (F : Index) (t : ℝ) (f : H) : ‖finiteOrbit F t f‖=‖f‖ :=
  SourceFiniteUnitary.time_norm _ (GaussGradedCompression.compression_selfAdjoint F) t f

theorem finite_energy_exact (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ s : ℝ,
      GaussGradedCompression.compression F (finiteOrbit F s (g : H))=
        finiteOrbit F s (diagonal g) := by
  filter_upwards [GaussGradedCompression.eventually_exact g] with F hF s
  have hc := congrArg (fun T : H →L[ℂ] H => T (g : H))
    (SourceFiniteUnitary.time_commutes (GaussGradedCompression.compression F)
      (GaussGradedCompression.compression F) (Commute.refl _) s).eq
  simpa only [finiteOrbit,mul_apply_eq_comp,hF] using hc

theorem original_flux_uniform (A B : H →L[ℂ] H) (approx : CoreGraphApproximation A B)
    (f : H) (g : diagonal.domain) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ t s : ℝ,
      ‖inner ℂ (B (finiteOrbit F t f)) (finiteOrbit F s (g : H))-
        inner ℂ (A (finiteOrbit F t f)) (finiteOrbit F s (diagonal g))‖<ε := by
  let K := ‖f‖*‖(g : H)‖+‖f‖*‖diagonal g‖+1
  have hK : 0<K := by dsimp [K]; positivity
  let δ := ε/K
  have hδ : 0<δ := div_pos hε hK
  obtain ⟨a,ha,hb⟩ := approx δ hδ
  filter_upwards [columns_eventually_exact a,finite_energy_exact g] with F hF hg t s
  have h := flux_error (GaussGradedCompression.compression F) A B a.action a.graphAction
    (GaussGradedCompression.compression_pair F) hF (finiteOrbit F t f)
    (finiteOrbit F s (g : H)) (finiteOrbit F s (diagonal g)) (hg s)
  simp only [finite_orbit_norm] at h
  have he : δ*K=ε := div_mul_cancel₀ ε (ne_of_gt hK)
  have h₁ := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right ha (norm_nonneg f)) (norm_nonneg (diagonal g))
  have h₂ := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hb (norm_nonneg f)) (norm_nonneg (g : H))
  dsimp [K] at he
  nlinarith

theorem original_flux_tendsto (A B : H →L[ℂ] H) (approx : CoreGraphApproximation A B)
    (f : H) (g : diagonal.domain) (t s : ℝ) :
    Tendsto (fun F => inner ℂ (B (finiteOrbit F t f)) (finiteOrbit F s (g : H))-
      inner ℂ (A (finiteOrbit F t f)) (finiteOrbit F s (diagonal g)))
      sourceFilter (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [original_flux_uniform A B approx f g ε hε] with F hF
  simpa only [dist_zero_right] using hF t s

theorem source_graph_pair (A B : H →L[ℂ] H) (approx : CoreGraphApproximation A B)
    (f : H) (g : diagonal.domain) (t s : ℝ) :
    inner ℂ (reader B (GaussGradedUnitary.time t (inclusion f)))
      (GaussGradedUnitary.time s (inclusion (g : H)))=
    inner ℂ (reader A (GaussGradedUnitary.time t (inclusion f)))
      (GaussGradedUnitary.time s (inclusion (diagonal g))) := by
  simp only [GaussGradedUnitary.time_inclusion]
  exact lifted_graph_pair sourceFilter A B (GaussGradedUnitary.trajectory t f)
    (GaussGradedUnitary.trajectory s (g : H))
    (GaussGradedUnitary.trajectory s (diagonal g))
    (original_flux_tendsto A B approx f g t s)

theorem family_flux_uniform (A B : H →L[ℂ] H) (approx : CoreGraphApproximation A B)
    (f : Family H sourceFilter) (g : diagonal.domain) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ s : ℝ,
      ‖inner ℂ (B (value f F)) (finiteOrbit F s (g : H))-
        inner ℂ (A (value f F)) (finiteOrbit F s (diagonal g))‖<ε := by
  obtain ⟨M,hM,hf⟩ := f.property
  have hfn (F : Index) : ‖value f F‖≤M := hf F
  let K := M*‖(g : H)‖+M*‖diagonal g‖+1
  have hK : 0<K := by dsimp [K]; positivity
  let δ := ε/K
  have hδ : 0<δ := div_pos hε hK
  obtain ⟨a,ha,hb⟩ := approx δ hδ
  filter_upwards [columns_eventually_exact a,finite_energy_exact g] with F hF hg s
  have h := flux_error (GaussGradedCompression.compression F) A B a.action a.graphAction
    (GaussGradedCompression.compression_pair F) hF (value f F)
    (finiteOrbit F s (g : H)) (finiteOrbit F s (diagonal g)) (hg s)
  simp only [finite_orbit_norm] at h
  have he : δ*K=ε := div_mul_cancel₀ ε (ne_of_gt hK)
  have h₁ := mul_le_mul_of_nonneg_right
    (mul_le_mul ha (hfn F) (norm_nonneg _) (le_of_lt hδ)) (norm_nonneg (diagonal g))
  have h₂ := mul_le_mul_of_nonneg_right
    (mul_le_mul hb (hfn F) (norm_nonneg _) (le_of_lt hδ)) (norm_nonneg (g : H))
  dsimp [K] at he
  nlinarith

theorem whole_carrier_graph_pair (A B : H →L[ℂ] H) (approx : CoreGraphApproximation A B)
    (x : HistorySpace) (g : diagonal.domain) (s : ℝ) :
    inner ℂ (reader B x) (GaussGradedUnitary.time s (inclusion (g : H)))=
      inner ℂ (reader A x) (GaussGradedUnitary.time s (inclusion (diagonal g))) := by
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro f
  simp only [GaussGradedUnitary.time_inclusion]
  apply lifted_graph_pair sourceFilter A B f
    (GaussGradedUnitary.trajectory s (g : H))
    (GaussGradedUnitary.trajectory s (diagonal g))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [family_flux_uniform A B approx f g ε hε] with F hF
  simp only [dist_zero_right]
  change ‖inner ℂ (B (value f F)) (finiteOrbit F s (g : H))-
    inner ℂ (A (value f F)) (finiteOrbit F s (diagonal g))‖<ε
  exact hF s

theorem source_observable_derivative (A B : H →L[ℂ] H)
    (approx : CoreGraphApproximation A B)
    (hA : ∀ x y, inner ℂ (A x) y=inner ℂ x (A y))
    (f : diagonal.domain) (t : ℝ) :
    HasDerivAt (fun s => inner ℂ (reader A (GaussGradedUnitary.time s (inclusion (f : H))))
      (GaussGradedUnitary.time s (inclusion (f : H))))
      (Complex.I*(inner ℂ (GaussGradedUnitary.time t (inclusion (f : H)))
        (reader B (GaussGradedUnitary.time t (inclusion (f : H))))-
        inner ℂ (reader B (GaussGradedUnitary.time t (inclusion (f : H))))
          (GaussGradedUnitary.time t (inclusion (f : H))))) t := by
  let u := GaussGradedUnitary.time t (inclusion (f : H))
  let v := GaussGradedUnitary.time t (inclusion (diagonal f))
  have hd := GaussGradedUnitary.core_derivative f t
  have ha := (reader A).restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt t hd
  have h := ha.inner ℂ hd
  have hp (x y : HistorySpace) : inner ℂ (reader A x) y=inner ℂ x (reader A y) :=
    lift_pair sourceFilter (SourceFamilyOperator.constant A) (SourceFamilyOperator.constant A)
      (fun _ x y => hA x y) x y
  have hb : inner ℂ (reader A u) v=inner ℂ (reader B u) u :=
    (source_graph_pair A B approx (f : H) f t t).symm
  have hc : inner ℂ (reader A v) u=inner ℂ u (reader B u) := by
    rw [hp]
    simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) hb
  have he : inner ℂ (reader A u) ((-Complex.I) • v)+
      inner ℂ (reader A ((-Complex.I) • v)) u=
      Complex.I*(inner ℂ u (reader B u)-inner ℂ (reader B u) u) := by
    simp only [map_smul,inner_smul_left,inner_smul_right,map_neg,Complex.conj_I,hb,hc]
    ring
  change HasDerivAt (fun s => inner ℂ (reader A (GaussGradedUnitary.time s (inclusion (f : H))))
    (GaussGradedUnitary.time s (inclusion (f : H))))
    (inner ℂ (reader A u) ((-Complex.I) • v)+inner ℂ (reader A ((-Complex.I) • v)) u) t at h
  rw [he] at h
  exact h

#print axioms columns_eventually_exact
#print axioms original_flux_uniform
#print axioms source_graph_pair
#print axioms whole_carrier_graph_pair
#print axioms source_observable_derivative
end LowEnergy.FullYSourceGraphCompactFlux
