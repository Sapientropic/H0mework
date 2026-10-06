import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceResolventGraphSplice
import Mathlib.Analysis.Normed.Operator.Extend

/-! A particular in the original minimal graph, with its actual adjoint defect. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourceMinimalGraphParticular
open SymmetricGraphClosure
open scoped Topology InnerProductSpace

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def shift (T : E →ₗ.[ℂ] E) (w : ℂ) : T.domain →ₗ[ℂ] E :=
  T.toFun-w • T.domain.subtype

def shiftedRange (T : E →ₗ.[ℂ] E) (w : ℂ) : Submodule ℂ E :=
  (LinearMap.range (shift T w)).topologicalClosure

instance (T : E →ₗ.[ℂ] E) (w : ℂ) : CompleteSpace (shiftedRange T w) := by
  unfold shiftedRange
  infer_instance

def intoShiftedRange (T : E →ₗ.[ℂ] E) (w : ℂ) : T.domain →ₗ[ℂ] shiftedRange T w :=
  (shift T w).codRestrict _ (fun x =>
    (LinearMap.range (shift T w)).le_topologicalClosure (LinearMap.mem_range_self _ x))

omit [CompleteSpace E] in
theorem intoShiftedRange_dense (T : E →ₗ.[ℂ] E) (w : ℂ) :
    DenseRange (intoShiftedRange T w) := by
  have hi : DenseRange (Set.inclusion
      (show (LinearMap.range (shift T w) : Set E) ⊆ shiftedRange T w from
        (LinearMap.range (shift T w)).le_topologicalClosure)) := by
    apply (denseRange_inclusion_iff _).mpr
    exact Set.Subset.rfl
  exact hi.comp (shift T w).surjective_rangeRestrict.denseRange
    (continuous_inclusion _)

omit [CompleteSpace E] in
theorem shift_coercive (T : E →ₗ.[ℂ] E) (hs : FormalAdjointPair T T)
    (w : ℂ) (hw : w.im≠0) (x : T.domain) :
    ‖(x : E)‖≤(1/|w.im|)*‖shift T w x‖ := by
  have hr : (inner ℂ (x : E) (T x)).im=0 := by
    apply Complex.conj_eq_iff_im.mp
    rw [inner_conj_symm]
    exact hs x x
  have hxx : inner ℂ (x : E) (x : E)=(‖(x : E)‖^2 : ℝ) := by
    simp only [inner_self_eq_norm_sq_to_K,Complex.ofReal_pow]
    rfl
  have him : (inner ℂ (x : E) (shift T w x)).im= -w.im*‖(x : E)‖^2 := by
    change (inner ℂ (x : E) (T x-w • (x : E))).im=_
    rw [inner_sub_right,inner_smul_right,hxx]
    simp only [Complex.sub_im,Complex.mul_im,hr,Complex.ofReal_im,Complex.ofReal_re,
      mul_zero,zero_add,zero_sub,neg_mul]
  have hb : |w.im| * ‖(x : E)‖^2≤‖(x : E)‖*‖shift T w x‖ := by
    calc
      _ = |(inner ℂ (x : E) (shift T w x)).im| := by
        rw [him,abs_mul,abs_neg,abs_of_nonneg (sq_nonneg ‖(x : E)‖)]
      _ ≤ ‖inner ℂ (x : E) (shift T w x)‖ := Complex.abs_im_le_norm _
      _ ≤ _ := norm_inner_le_norm _ _
  by_cases hx : (x : E)=0
  · rw [hx,norm_zero]
    positivity
  · have hp : 0<‖(x : E)‖ := norm_pos_iff.mpr hx
    have he : |w.im| * ‖(x : E)‖≤‖shift T w x‖ := by nlinarith
    rw [one_div,mul_comm,←div_eq_mul_inv,le_div_iff₀ (abs_pos.mpr hw)]
    simpa only [mul_comm] using he

def inverseOnRange (T : E →ₗ.[ℂ] E) (w : ℂ) : shiftedRange T w →L[ℂ] E :=
  T.domain.subtype.extendOfNorm (intoShiftedRange T w)

theorem inverseOnRange_core (T : E →ₗ.[ℂ] E) (hs : FormalAdjointPair T T)
    (w : ℂ) (hw : w.im≠0) (x : T.domain) :
    inverseOnRange T w (intoShiftedRange T w x)=(x : E) := by
  apply LinearMap.extendOfNorm_eq (intoShiftedRange_dense T w)
  exact ⟨1/|w.im|,shift_coercive T hs w hw⟩

theorem inverseOnRange_bound (T : E →ₗ.[ℂ] E) (hs : FormalAdjointPair T T)
    (w : ℂ) (hw : w.im≠0) (y : shiftedRange T w) :
    ‖inverseOnRange T w y‖≤(1/|w.im|)*‖y‖ :=
  LinearMap.norm_extendOfNorm_apply_le (intoShiftedRange_dense T w) _
    (shift_coercive T hs w hw) y

def particular (T : E →ₗ.[ℂ] E) (w : ℂ) : E →L[ℂ] E :=
  (inverseOnRange T w).comp (shiftedRange T w).orthogonalProjectionOnto

def defect (T : E →ₗ.[ℂ] E) (w : ℂ) : E →L[ℂ] E :=
  1-(shiftedRange T w).starProjection

def graphAction (T : E →ₗ.[ℂ] E) (w : ℂ) : E →L[ℂ] E :=
  w • particular T w+(shiftedRange T w).starProjection

theorem particular_norm (T : E →ₗ.[ℂ] E) (hs : FormalAdjointPair T T)
    (w : ℂ) (hw : w.im≠0) : ‖particular T w‖≤1/|w.im| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  apply (inverseOnRange_bound T hs w hw _).trans
  exact mul_le_mul_of_nonneg_left
    ((shiftedRange T w).norm_orthogonalProjectionOnto_apply_le y) (by positivity)

theorem particular_graph (T : E →ₗ.[ℂ] E) (hs : FormalAdjointPair T T)
    (w : ℂ) (hw : w.im≠0) (y : E) :
    (particular T w y,graphAction T w y)∈closedGraph T := by
  have hr (r : shiftedRange T w) :
      (inverseOnRange T w r,w • inverseOnRange T w r+(r : E))∈closedGraph T := by
    refine (intoShiftedRange_dense T w).induction_on r ?_ ?_
    · exact T.graph.isClosed_topologicalClosure.preimage
        ((inverseOnRange T w).continuous.prodMk
          ((continuous_const.smul (inverseOnRange T w).continuous).add continuous_subtype_val))
    · intro x
      rw [inverseOnRange_core T hs w hw x]
      have he : w • (x : E)+(intoShiftedRange T w x : E)=T x := by
        change w • (x : E)+(T x-w • (x : E))=T x
        abel
      rw [he]
      exact T.graph.le_topologicalClosure (T.mem_graph x)
  exact hr ((shiftedRange T w).orthogonalProjectionOnto y)

theorem particular_core_shift (T : E →ₗ.[ℂ] E) (hs : FormalAdjointPair T T)
    (w : ℂ) (hw : w.im≠0) (x : T.domain) :
    particular T w (shift T w x)=(x : E) := by
  have hp := (shiftedRange T w).orthogonalProjectionOnto_mem_subspace_eq_self
    (intoShiftedRange T w x)
  change (shiftedRange T w).orthogonalProjectionOnto (shift T w x)=intoShiftedRange T w x at hp
  change inverseOnRange T w
    ((shiftedRange T w).orthogonalProjectionOnto (shift T w x))=(x : E)
  rw [hp,inverseOnRange_core T hs w hw x]

theorem adjoint_particular_equation (T : E →ₗ.[ℂ] E) (hs : FormalAdjointPair T T)
    (w : ℂ) (hw : w.im≠0) (x : T.domain) (y : E) :
    inner ℂ (T x) ((particular T w).adjoint y)=
      inner ℂ (x : E) (star w • (particular T w).adjoint y+y) := by
  have he := congrArg (fun a : E => inner ℂ a y) (particular_core_shift T hs w hw x)
  change inner ℂ (particular T w (T x-w • (x : E))) y=inner ℂ (x : E) y at he
  rw [map_sub,map_smul,inner_sub_left,inner_smul_left,
    ←ContinuousLinearMap.adjoint_inner_right,←ContinuousLinearMap.adjoint_inner_right] at he
  rw [inner_add_right,inner_smul_right]
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

theorem original_core_decomposition (T : E →ₗ.[ℂ] E) (hs : FormalAdjointPair T T)
    (w : ℂ) (hw : w.im≠0) (x : T.domain) :
    (x : E)=(particular T w).adjoint (T x-star w • (x : E))+defect T w (x : E) := by
  have he : (particular T w).adjoint (T x-star w • (x : E))=
      (shiftedRange T w).starProjection (x : E) := by
    apply ext_inner_left ℂ
    intro y
    have hg := closed_graph_pairing T T hs (particular_graph T hs w hw y) x
    change inner ℂ (w • particular T w y+(shiftedRange T w).starProjection y) (x : E)=
      inner ℂ (particular T w y) (T x) at hg
    rw [inner_add_left,inner_smul_left,starRingEnd_apply] at hg
    rw [ContinuousLinearMap.adjoint_inner_right,inner_sub_right,inner_smul_right,←hg]
    have hp := (shiftedRange T w).inner_starProjection_left_eq_right y (x : E)
    rw [←hp]
    abel
  rw [he]
  change (x : E)=(shiftedRange T w).starProjection (x : E)+
    ((x : E)-(shiftedRange T w).starProjection (x : E))
  abel

theorem graphAction_shift (T : E →ₗ.[ℂ] E) (w : ℂ) :
    graphAction T w-w • particular T w=1-defect T w := by
  unfold graphAction defect
  abel

theorem defect_adjoint (T : E →ₗ.[ℂ] E) (w : ℂ) (x : T.domain) (y : E) :
    inner ℂ (T x) (defect T w y)=inner ℂ (x : E) (star w • defect T w y) := by
  have hz : inner ℂ (shift T w x) (defect T w y)=0 := by
    exact (Submodule.mem_orthogonal _ _).mp
      ((shiftedRange T w).sub_starProjection_mem_orthogonal y) _
      ((LinearMap.range (shift T w)).le_topologicalClosure (LinearMap.mem_range_self _ x))
  change inner ℂ (T x-w • (x : E)) (defect T w y)=0 at hz
  rw [inner_sub_left,inner_smul_left] at hz
  rw [inner_smul_right]
  exact sub_eq_zero.mp hz

theorem defect_norm (T : E →ₗ.[ℂ] E) (w : ℂ) : ‖defect T w‖≤1 := by
  rw [defect,←Submodule.starProjection_orthogonal']
  exact (shiftedRange T w)ᗮ.starProjection_norm_le

theorem retained_remainder (T : E →ₗ.[ℂ] E) (w z : ℂ) (K Y : E →L[ℂ] E) :
    graphAction T w*K*Y-z • (particular T w*K*Y)-Y=
      (w-z) • (particular T w*K*Y)-defect T w*K*Y-(1-K)*Y := by
  unfold graphAction defect
  simp only [add_mul,sub_mul,one_mul,smul_mul_assoc,sub_smul]
  abel

end Hilbert

open GaussCoreHilbert GaussDiagonalHistory
open GaussUnitaryHistory (Index)
open FullYSourceResolventGraphSplice

def sourceParticular (w : ℂ) : H →L[ℂ] H := particular diagonal w
def sourceDefect (w : ℂ) : H →L[ℂ] H := defect diagonal w
def sourceGraphAction (w : ℂ) : H →L[ℂ] H := graphAction diagonal w

theorem source_particular_graph (w : ℂ) (hw : w.im≠0) (y : H) :
    (sourceParticular w y,sourceGraphAction w y)∈closedGraph diagonal :=
  particular_graph diagonal diagonal_pair w hw y

theorem source_particular_norm (w : ℂ) (hw : w.im≠0) :
    ‖sourceParticular w‖≤1/|w.im| := particular_norm diagonal diagonal_pair w hw

theorem source_original_adjoint_defect (w : ℂ) (x : diagonal.domain) (y : H) :
    inner ℂ (diagonal x) (sourceDefect w y)=
      inner ℂ (x : H) (star w • sourceDefect w y) := defect_adjoint diagonal w x y

theorem source_adjoint_particular_equation (w : ℂ) (hw : w.im≠0)
    (x : diagonal.domain) (y : H) :
    inner ℂ (diagonal x) ((sourceParticular w).adjoint y)=
      inner ℂ (x : H) (star w • (sourceParticular w).adjoint y+y) :=
  adjoint_particular_equation diagonal diagonal_pair w hw x y

theorem compression_mem_core (F : Index) (x : H) :
    GaussGradedCompression.compression F x∈diagonal.domain := by
  classical
  let : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _
  rw [GaussGradedCompression.compression_apply]
  apply Submodule.sum_mem
  intro g _
  have hc : FiniteCoreEvolution.compression diagonal F (NativeHistoryGrade.projection g x)∈
      diagonal.domain :=
    FiniteCoreEvolution.coreSpan_le diagonal F
      (FiniteCoreEvolution.finiteAction diagonal F
        ((FiniteCoreEvolution.coreSpan diagonal F).orthogonalProjectionOnto
          (NativeHistoryGrade.projection g x))).property
  exact GaussDiagonalGrade.stable g ⟨_,hc⟩

theorem finite_resolvent_mem_core (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : finiteResolvent F z (g : H)∈diagonal.domain := by
  have he := congrArg (fun A : H →L[ℂ] H => A (g : H))
    (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change GaussGradedCompression.compression F (finiteResolvent F z (g : H))-
    z • finiteResolvent F z (g : H)=(g : H) at he
  have hzm : z • finiteResolvent F z (g : H)∈diagonal.domain := by
    have heq : z • finiteResolvent F z (g : H)=
        GaussGradedCompression.compression F (finiteResolvent F z (g : H))-(g : H) := by
      apply eq_sub_iff_add_eq.mpr
      exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp he).symm
    rw [heq]
    exact diagonal.domain.sub_mem (compression_mem_core F _) g.property
  have hz0 : z≠0 := by intro h; exact hz (h ▸ rfl)
  have h := diagonal.domain.smul_mem z⁻¹ hzm
  simpa only [smul_smul,inv_mul_cancel₀ hz0,one_smul] using h

def finiteProjectionDefect (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : H :=
  diagonal ⟨finiteResolvent F z (g : H),finite_resolvent_mem_core F z hz g⟩-
    GaussGradedCompression.compression F (finiteResolvent F z (g : H))

theorem finite_resolvent_original_split (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    finiteResolvent F z (g : H)=
      (sourceParticular (star z)).adjoint ((g : H)+finiteProjectionDefect F z hz g)+
        sourceDefect (star z) (finiteResolvent F z (g : H)) := by
  let q : diagonal.domain := ⟨finiteResolvent F z (g : H),finite_resolvent_mem_core F z hz g⟩
  have hsz : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero]
  have he := original_core_decomposition diagonal diagonal_pair (star z) hsz q
  have hr := congrArg (fun A : H →L[ℂ] H => A (g : H))
    (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change GaussGradedCompression.compression F (q : H)-z • (q : H)=(g : H) at hr
  have hd : diagonal q-star (star z) • (q : H)=
      (g : H)+finiteProjectionDefect F z hz g := by
    rw [star_star]
    change diagonal q-z • (q : H)=(g : H)+
      (diagonal q-GaussGradedCompression.compression F (q : H))
    rw [←hr]
    abel
  rw [hd] at he
  exact he

theorem source_retained_remainder (w z : ℂ) (K Y : H →L[ℂ] H) :
    sourceGraphAction w*K*Y-z • (sourceParticular w*K*Y)-Y=
      (w-z) • (sourceParticular w*K*Y)-sourceDefect w*K*Y-(1-K)*Y :=
  retained_remainder diagonal w z K Y

#print axioms source_particular_graph
#print axioms source_particular_norm
#print axioms source_original_adjoint_defect
#print axioms source_adjoint_particular_equation
#print axioms finite_resolvent_original_split
#print axioms source_retained_remainder
end LowEnergy.SourceMinimalGraphParticular
