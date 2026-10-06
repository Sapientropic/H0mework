import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceMinimalGraphParticular

/-! The actual whole-carrier resolvent generates its source-seen boundary Gram. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourceBoundaryGram
open Filter SymmetricGraphClosure SourceMinimalGraphParticular
open SourceFamilyHilbert SourceFamilyOperator
open GaussCoreHilbert GaussDiagonalHistory
open GaussUnitaryHistory (Index HistorySpace sourceFilter inclusion reader)
open FullYSourceResolventGraphSplice
open scoped Topology InnerProductSpace

section Hilbert
variable {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem lift_bound_explicit (l : Ultrafilter I) (A : Operator I E) (C : ℝ) (_hC : 0≤C)
    (hA : ∀ i x, ‖A.component i x‖≤C*‖x‖) (x : Hilbert E l) :
    ‖lift l A x‖≤C*‖x‖ := by
  refine UniformSpace.Completion.induction_on x (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro f
  rw [lift_coe,UniformSpace.Completion.norm_coe,UniformSpace.Completion.norm_coe]
  apply le_of_tendsto_of_tendsto (norm_tendsto l (act l A f))
    ((norm_tendsto l f).const_mul C)
  exact Filter.Eventually.of_forall (fun i => hA i (value f i))

variable [CompleteSpace E]

theorem adjoint_particular_mem_range (T : E →ₗ.[ℂ] E) (w : ℂ) (g : E) :
    (particular T w).adjoint g∈shiftedRange T w := by
  unfold particular
  rw [ContinuousLinearMap.adjoint_comp,Submodule.adjoint_orthogonalProjectionOnto]
  exact Subtype.coe_prop _

omit [CompleteSpace E] in
theorem isometry_norm_add {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (J : E →ₗᵢ[ℂ] F) (x : E) (y : F) :
    ‖J x+y‖^2=‖x‖^2+2*(inner ℂ (J x) y).re+‖y‖^2 := by
  simpa only [J.norm_map,RCLike.re_eq_complex_re] using norm_add_sq (𝕜 := ℂ) (J x) y

end Hilbert

def maxParticular (z : ℂ) : H →L[ℂ] H := (sourceParticular (star z)).adjoint

def sourceInclusion : H →L[ℂ] HistorySpace := inclusion.toContinuousLinearMap

def sourceSeen : HistorySpace →L[ℂ] H := sourceInclusion.adjoint

def sourceBody (z : ℂ) : HistorySpace →L[ℂ] HistorySpace :=
  sourceInclusion.comp ((maxParticular z).comp sourceSeen)

def boundaryReturn (z : ℂ) (hz : z.im≠0) : HistorySpace →L[ℂ] HistorySpace :=
  sameResolvent z hz-sourceBody z

theorem same_resolvent_bound (z : ℂ) (hz : z.im≠0) (x : HistorySpace) :
    ‖sameResolvent z hz x‖≤(1/|z.im|)*‖x‖ := by
  apply lift_bound_explicit sourceFilter (resolventFamily z hz) _ (by positivity)
  intro F g
  exact ((finiteResolvent F z).le_opNorm g).trans
    (mul_le_mul_of_nonneg_right (finite_resolvent_norm F z hz) (norm_nonneg g))

theorem finite_source_pair (F : Index) (z : ℂ) (hz : z.im≠0) (x : diagonal.domain)
    (hx : GaussGradedCompression.compression F (x : H)=diagonal x) (y : H) :
    inner ℂ (shift diagonal (star z) x) (finiteResolvent F z y)=inner ℂ (x : H) y := by
  have hr := congrArg (fun A : H →L[ℂ] H => A y)
    (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change GaussGradedCompression.compression F (finiteResolvent F z y)-
    z • finiteResolvent F z y=y at hr
  change inner ℂ (diagonal x-star z • (x : H)) (finiteResolvent F z y)=_
  have hc : inner ℂ (GaussGradedCompression.compression F (x : H)) (finiteResolvent F z y)=
      inner ℂ (x : H) (GaussGradedCompression.compression F (finiteResolvent F z y)) :=
    GaussGradedCompression.compression_pair F (x : H) (finiteResolvent F z y)
  rw [←hx,inner_sub_left,inner_smul_left,starRingEnd_apply,star_star,
    hc]
  rw [←inner_smul_right,←inner_sub_right,hr]

theorem whole_carrier_source_pair (z : ℂ) (hz : z.im≠0) (x : diagonal.domain)
    (y : HistorySpace) :
    inner ℂ (inclusion (shift diagonal (star z) x)) (sameResolvent z hz y)=
      inner ℂ (inclusion (x : H)) y := by
  refine UniformSpace.Completion.induction_on y (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro f
  change inner ℂ ((SourceFamilyHilbert.constant sourceFilter (shift diagonal (star z) x)) : HistorySpace)
      (lift sourceFilter (resolventFamily z hz) (f : HistorySpace))=
    inner ℂ ((SourceFamilyHilbert.constant sourceFilter (x : H)) : HistorySpace) (f : HistorySpace)
  rw [lift_coe,inner_coe,inner_coe]
  apply tendsto_nhds_unique
    (pair_tendsto sourceFilter (SourceFamilyHilbert.constant sourceFilter (shift diagonal (star z) x))
      (act sourceFilter (resolventFamily z hz) f))
  apply (pair_tendsto sourceFilter (SourceFamilyHilbert.constant sourceFilter (x : H)) f).congr'
  filter_upwards [GaussGradedCompression.eventually_exact x] with F hF
  exact (finite_source_pair F z hz x hF (value f F)).symm

theorem max_particular_source_pair (z : ℂ) (hz : z.im≠0) (x : diagonal.domain) (g : H) :
    inner ℂ (shift diagonal (star z) x) (maxParticular z g)=inner ℂ (x : H) g := by
  have hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  rw [maxParticular,ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (particular diagonal (star z) (shift diagonal (star z) x)) g=_
  rw [particular_core_shift diagonal diagonal_pair (star z) hs x]

theorem max_particular_mem_source_range (z : ℂ) (g : H) :
    maxParticular z g∈shiftedRange diagonal (star z) :=
  adjoint_particular_mem_range diagonal (star z) g

theorem boundary_source_pair_zero (z : ℂ) (hz : z.im≠0) (x : diagonal.domain)
    (y : HistorySpace) :
    inner ℂ (inclusion (shift diagonal (star z) x)) (boundaryReturn z hz y)=0 := by
  change inner ℂ (inclusion (shift diagonal (star z) x))
    (sameResolvent z hz y-inclusion (maxParticular z (sourceSeen y)))=0
  rw [inner_sub_right,whole_carrier_source_pair,inclusion.inner_map_map,
    max_particular_source_pair z hz]
  change inner ℂ (sourceInclusion (x : H)) y-
    inner ℂ (x : H) (sourceInclusion.adjoint y)=0
  rw [ContinuousLinearMap.adjoint_inner_right,sub_self]

theorem boundary_closed_range_pair_zero (z : ℂ) (hz : z.im≠0)
    (r : shiftedRange diagonal (star z)) (y : HistorySpace) :
    inner ℂ (inclusion (r : H)) (boundaryReturn z hz y)=0 := by
  have h : Set.EqOn (fun a : H => inner ℂ (inclusion a) (boundaryReturn z hz y))
      (fun _ => 0) (LinearMap.range (shift diagonal (star z)) : Set H) := by
    intro a ha
    obtain ⟨x,rfl⟩ := ha
    exact boundary_source_pair_zero z hz x y
  exact h.closure (by fun_prop) continuous_const r.property

theorem body_boundary_orthogonal (z : ℂ) (hz : z.im≠0) (x y : HistorySpace) :
    inner ℂ (sourceBody z x) (boundaryReturn z hz y)=0 :=
  boundary_closed_range_pair_zero z hz
    ⟨maxParticular z (sourceSeen x),max_particular_mem_source_range z _⟩ y

theorem whole_carrier_boundary_gram (z : ℂ) (hz : z.im≠0) (x : HistorySpace) :
    ‖sameResolvent z hz x‖^2=
      ‖maxParticular z (sourceSeen x)‖^2+‖boundaryReturn z hz x‖^2 := by
  have he : sameResolvent z hz x=sourceBody z x+boundaryReturn z hz x := by
    change sameResolvent z hz x=sourceBody z x+(sameResolvent z hz x-sourceBody z x)
    abel
  rw [he,norm_add_sq (𝕜 := ℂ),body_boundary_orthogonal]
  simp only [map_zero,mul_zero,add_zero]
  change ‖inclusion (maxParticular z (sourceSeen x))‖^2+_= _
  rw [inclusion.norm_map]

theorem boundary_return_bound (z : ℂ) (hz : z.im≠0) (x : HistorySpace) :
    ‖boundaryReturn z hz x‖≤(1/|z.im|)*‖x‖ := by
  have hgram := whole_carrier_boundary_gram z hz x
  have hr := same_resolvent_bound z hz x
  have hn : 0≤(1/|z.im|)*‖x‖ := by positivity
  nlinarith [sq_nonneg ‖maxParticular z (sourceSeen x)‖,
    norm_nonneg (boundaryReturn z hz x),norm_nonneg (sameResolvent z hz x)]

/-- The weight acts after the actual split; both boundary legs remain. -/
theorem weighted_boundary_gram (z : ℂ) (hz : z.im≠0) (W : H →L[ℂ] H)
    (x : HistorySpace) :
    ‖reader W (sameResolvent z hz x)‖^2=
      ‖W (maxParticular z (sourceSeen x))‖^2+
      2*(inner ℂ (inclusion (W (maxParticular z (sourceSeen x))))
        (reader W (boundaryReturn z hz x))).re+
      ‖reader W (boundaryReturn z hz x)‖^2 := by
  have he : sameResolvent z hz x=sourceBody z x+boundaryReturn z hz x := by
    change sameResolvent z hz x=sourceBody z x+(sameResolvent z hz x-sourceBody z x)
    abel
  have hw : reader W (sourceBody z x)=inclusion (W (maxParticular z (sourceSeen x))) :=
    GaussUnitaryHistory.reader_inclusion W (maxParticular z (sourceSeen x))
  calc
    _ = ‖reader W (sourceBody z x)+reader W (boundaryReturn z hz x)‖^2 := by
      exact congrArg (fun v : HistorySpace => ‖v‖^2)
        ((congrArg (reader W) he).trans ((reader W).map_add _ _))
    _ = ‖inclusion (W (maxParticular z (sourceSeen x)))+
        reader W (boundaryReturn z hz x)‖^2 :=
      congrArg (fun v : HistorySpace => ‖v+reader W (boundaryReturn z hz x)‖^2) hw
    _ = _ := isometry_norm_add inclusion _ _

#print axioms whole_carrier_source_pair
#print axioms whole_carrier_boundary_gram
#print axioms boundary_return_bound
#print axioms weighted_boundary_gram
end LowEnergy.SourceBoundaryGram
