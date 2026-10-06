import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceBoundaryGram
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceResolventBandLimit

/-! Frequency regularity of the original minimal particular, without operator-core approximation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace LowEnergy.SourceParticularFrequency
open SymmetricGraphClosure SourceMinimalGraphParticular SourceBoundaryGram
open scoped Topology InnerProductSpace

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem particular_closed_shift (T : E →ₗ.[ℂ] E) (hs : FormalAdjointPair T T)
    (w : ℂ) (hw : w.im ≠ 0) {p : E × E} (hp : p∈closedGraph T) :
    particular T w (p.2-w • p.1)=p.1 := by
  have he : Set.EqOn (fun q : E × E => particular T w (q.2-w • q.1))
      Prod.fst (T.graph : Set (E × E)) := by
    intro q hq
    obtain ⟨x,rfl⟩ := T.mem_graph_iff'.mp hq
    exact particular_core_shift T hs w hw x
  exact he.closure (by fun_prop) continuous_fst hp

theorem defect_closed_shift (T : E →ₗ.[ℂ] E) (w : ℂ)
    {p : E × E} (hp : p∈closedGraph T) : defect T w (p.2-w • p.1)=0 := by
  have he : Set.EqOn (fun q : E × E => defect T w (q.2-w • q.1))
      (fun _ => (0 : E)) (T.graph : Set (E × E)) := by
    intro q hq
    obtain ⟨x,rfl⟩ := T.mem_graph_iff'.mp hq
    have hx : shift T w x∈shiftedRange T w :=
      (LinearMap.range (shift T w)).le_topologicalClosure (LinearMap.mem_range_self _ x)
    change shift T w x-(shiftedRange T w).starProjection (shift T w x)=0
    rw [Submodule.starProjection_eq_self_iff.mpr hx,sub_self]
  exact he.closure (by fun_prop) continuous_const hp

theorem defect_self_adjoint (T : E →ₗ.[ℂ] E) (w : ℂ) :
    IsSelfAdjoint (defect T w) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro x y
  change inner ℂ (x-(shiftedRange T w).starProjection x) y=
    inner ℂ x (y-(shiftedRange T w).starProjection y)
  rw [inner_sub_left,inner_sub_right,(shiftedRange T w).inner_starProjection_left_eq_right]

theorem particular_two_frequency (T : E →ₗ.[ℂ] E) (hs : FormalAdjointPair T T)
    (v w : ℂ) (hv : v.im ≠ 0) (hw : w.im ≠ 0) :
    particular T v-particular T w=(v-w) • (particular T v*particular T w)+
      particular T v*defect T w := by
  ext x
  have he := particular_closed_shift T hs v hv (particular_graph T hs w hw x)
  change particular T v (w • particular T w x+(shiftedRange T w).starProjection x-
    v • particular T w x)=particular T w x at he
  rw [map_sub,map_add,map_smul,map_smul] at he
  change particular T v x-particular T w x=
    (v-w) • particular T v (particular T w x)+
      particular T v (x-(shiftedRange T w).starProjection x)
  rw [map_sub,sub_smul]
  conv_lhs => rhs; rw [←he]
  abel

theorem defect_adjoint_particular_two_frequency (T : E →ₗ.[ℂ] E)
    (hs : FormalAdjointPair T T) (v w : ℂ) (hv : v.im ≠ 0) :
    defect T w*(particular T v).adjoint=
      (w-v) • (defect T w*particular T v*(particular T v).adjoint) := by
  ext x
  let b := (particular T v).adjoint x
  have hr : (shiftedRange T v).starProjection b=b :=
    Submodule.starProjection_eq_self_iff.mpr (adjoint_particular_mem_range T v x)
  have he := defect_closed_shift T w (particular_graph T hs v hv b)
  change defect T w (v • particular T v b+(shiftedRange T v).starProjection b-
    w • particular T v b)=0 at he
  rw [hr,map_sub,map_add,map_smul,map_smul] at he
  change defect T w b=(w-v) • defect T w (particular T v b)
  rw [sub_smul]
  apply sub_eq_zero.mp
  calc
    _ = v • defect T w (particular T v b)+defect T w b-
        w • defect T w (particular T v b) := by abel
    _ = 0 := he

theorem particular_horizontal_bound (T : E →ₗ.[ℂ] E) (hs : FormalAdjointPair T T)
    (v w : ℂ) (μ : ℝ) (hμ : 0<μ) (hvμ : |v.im|=μ) (hwμ : |w.im|=μ) :
    ‖particular T v-particular T w‖ ≤ (2*μ⁻¹*μ⁻¹)*‖v-w‖ := by
  have hv : v.im ≠ 0 := by intro hz; rw [hz,abs_zero] at hvμ; linarith
  have hw : w.im ≠ 0 := by intro hz; rw [hz,abs_zero] at hwμ; linarith
  have hgv : ‖particular T v‖ ≤ μ⁻¹ := by simpa only [hvμ,one_div] using particular_norm T hs v hv
  have hgw : ‖particular T w‖ ≤ μ⁻¹ := by simpa only [hwμ,one_div] using particular_norm T hs w hw
  have hq : ‖defect T w‖ ≤ 1 := defect_norm T w
  have hcross : ‖particular T v*defect T w‖ ≤ ‖v-w‖*(μ⁻¹*μ⁻¹) := by
    have hnorm : ‖particular T v*defect T w‖=‖defect T w*(particular T v).adjoint‖ := by
      rw [←ContinuousLinearMap.adjoint.norm_map (particular T v*defect T w)]
      change ‖(ContinuousLinearMap.comp (particular T v) (defect T w)).adjoint‖=_
      rw [ContinuousLinearMap.adjoint_comp,(defect_self_adjoint T w).adjoint_eq]
      rfl
    rw [hnorm,defect_adjoint_particular_two_frequency T hs v w hv,norm_smul,norm_sub_rev]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have ha : ‖defect T w*particular T v‖ ≤ μ⁻¹ :=
      (norm_mul_le _ _).trans ((mul_le_mul hq hgv (norm_nonneg _) (by positivity)).trans_eq (one_mul _))
    apply (norm_mul_le _ _).trans
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact mul_le_mul ha hgv (norm_nonneg _) (by positivity)
  rw [particular_two_frequency T hs v w hv hw]
  apply (norm_add_le _ _).trans
  rw [norm_smul]
  have hp := mul_le_mul_of_nonneg_left
    ((norm_mul_le _ _).trans (mul_le_mul hgv hgw (norm_nonneg _) (by positivity))) (norm_nonneg (v-w))
  exact (add_le_add hp hcross).trans_eq (by ring)
end Hilbert

open GaussCoreHilbert GaussDiagonalHistory SourceResolventBandLimit
open Filter SourceFamilyHilbert SourceFamilyOperator FullYSourceResolventGraphSplice
open GaussUnitaryHistory (Index HistorySpace sourceFilter inclusion reader)

theorem original_particular_frequency_lipschitz (μ : ℝ) (hμ : 0<μ) :
    LipschitzWith (NNReal.mk (2*μ⁻¹*μ⁻¹) (by positivity))
      (fun t : ℝ => sourceParticular (star (line μ t))) := by
  apply LipschitzWith.of_dist_le_mul
  intro t s
  have hb := particular_horizontal_bound diagonal diagonal_pair
    (star (line μ t)) (star (line μ s)) μ hμ
    (by simp only [Complex.star_def,Complex.conj_im,line_im,abs_neg,abs_of_pos hμ])
    (by simp only [Complex.star_def,Complex.conj_im,line_im,abs_neg,abs_of_pos hμ])
  simpa only [sourceParticular,←star_sub,norm_star,line_difference,dist_eq_norm,
    Real.norm_eq_abs,NNReal.coe_mk] using hb

def lineResolvent (μ : ℝ) (hμ : 0<μ) (t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  sameResolvent (line μ t) (by simpa only [line_im] using ne_of_gt hμ)

theorem whole_resolvent_difference (μ : ℝ) (hμ : 0<μ) (t s : ℝ) (x : HistorySpace) :
    ‖lineResolvent μ hμ t x-lineResolvent μ hμ s x‖ ≤ μ⁻¹*μ⁻¹*|t-s| *‖x‖ := by
  refine UniformSpace.Completion.induction_on x (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro f
  change ‖lift sourceFilter (resolventFamily (line μ t) _) (f : HistorySpace)-
    lift sourceFilter (resolventFamily (line μ s) _) (f : HistorySpace)‖ ≤ _
  rw [lift_coe,lift_coe,←UniformSpace.Completion.coe_sub,UniformSpace.Completion.norm_coe,
    UniformSpace.Completion.norm_coe]
  apply le_of_tendsto_of_tendsto (norm_tendsto sourceFilter _)
    ((norm_tendsto sourceFilter f).const_mul (μ⁻¹*μ⁻¹*|t-s|))
  apply Eventually.of_forall
  intro F
  change ‖(finiteResolvent F (line μ t)-finiteResolvent F (line μ s)) (value f F)‖ ≤ _
  apply ((finiteResolvent F (line μ t)-finiteResolvent F (line μ s)).le_opNorm _).trans
  exact mul_le_mul_of_nonneg_right
    (line_resolvent_difference _ (GaussGradedCompression.compression_selfAdjoint F) μ hμ t s)
    (norm_nonneg _)

theorem whole_resolvent_frequency_lipschitz (μ : ℝ) (hμ : 0<μ) :
    LipschitzWith (NNReal.mk (μ⁻¹*μ⁻¹) (by positivity)) (lineResolvent μ hμ) := by
  apply LipschitzWith.of_dist_le_mul
  intro t s
  simp only [dist_eq_norm,Real.norm_eq_abs,NNReal.coe_mk]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact whole_resolvent_difference μ hμ t s

theorem whole_mixed_word_continuous (μ : ℝ) (hμ : 0<μ) (L : List (Bool × ℕ)) :
    Continuous (fun t => wholeWord μ hμ L t) := by
  induction L with
  | nil =>
    have he : (fun t => wholeWord μ hμ [] t)=lineResolvent μ hμ :=
      funext (whole_word_nil μ hμ)
    rw [he]
    exact (whole_resolvent_frequency_lipschitz μ hμ).continuous
  | cons a L ih =>
    have he : (fun t => wholeWord μ hμ (a::L) t)=
        (fun t => lineResolvent μ hμ t*reader (mixedLetter a)*wholeWord μ hμ L t) :=
      funext (whole_word_cons μ hμ a L)
    rw [he]
    exact ((whole_resolvent_frequency_lipschitz μ hμ).continuous.mul continuous_const).mul ih

theorem original_body_frequency_continuous (μ : ℝ) (hμ : 0<μ)
    (x : ℝ → HistorySpace) (hx : Continuous x) :
    Continuous (fun t => maxParticular (line μ t) (sourceSeen (x t))) := by
  have hg : Continuous (fun t : ℝ => (sourceParticular (star (line μ t))).adjoint) :=
    ContinuousLinearMap.adjoint.continuous.comp (original_particular_frequency_lipschitz μ hμ).continuous
  exact hg.clm_apply (sourceSeen.continuous.comp hx)

#print axioms particular_two_frequency
#print axioms defect_adjoint_particular_two_frequency
#print axioms original_particular_frequency_lipschitz
#print axioms whole_mixed_word_continuous
#print axioms original_body_frequency_continuous
end LowEnergy.SourceParticularFrequency
