import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceMinimalGraphParticular
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceCutoffVolterra

/-! The original graded finite compression retains its static escaped leg. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceRetardedIncrement
open Filter GaussCoreHilbert GaussDiagonalHistory
open NativeHistoryGrade (Label projection)
open GaussUnitaryHistory (Index HistorySpace sourceFilter inclusion)
open FullYSourceResolventGraphSplice FullYSourceCutoffVolterra
open scoped Topology InnerProductSpace
local instance : Fintype Label := Fintype.ofFinite _

def supportSet (F : Index) : Index := by
  classical
  exact F.biUnion GaussGradedCompression.support

def supportSpan (F : Index) : Submodule ℂ H :=
  FiniteCoreEvolution.coreSpan diagonal (supportSet F)

instance supportSpan_finite (F : Index) : FiniteDimensional ℂ (supportSpan F) :=
  FiniteCoreEvolution.coreSpan_finite diagonal (supportSet F)

def supportProjection (F : Index) : H →L[ℂ] H := (supportSpan F).starProjection

def escapeProjection (F : Index) : H →L[ℂ] H := 1-supportProjection F

theorem piece_mem_support (F : Index) (g : Label) (x : diagonal.domain) (hx : x∈F) :
    (GaussGradedCompression.piece g x : H)∈supportSpan F := by
  classical
  apply FiniteCoreEvolution.mem_coreSpan diagonal (supportSet F)
  exact Finset.mem_biUnion.mpr ⟨x,hx,
    Finset.mem_image.mpr ⟨g,Finset.mem_univ g,rfl⟩⟩

theorem projection_mem_support (F : Index) (g : Label) (x : H)
    (hx : x∈FiniteCoreEvolution.coreSpan diagonal F) : projection g x∈supportSpan F := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y,hy,rfl⟩ := hx
    exact piece_mem_support F g y hy
  | zero => simpa only [map_zero] using (supportSpan F).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (supportSpan F).add_mem ihx ihy
  | smul a x hx ih =>
    simpa only [map_smul] using (supportSpan F).smul_mem a ih

theorem compression_mem_support (F : Index) (x : H) :
    GaussGradedCompression.compression F x∈supportSpan F := by
  rw [GaussGradedCompression.compression_apply]
  apply Submodule.sum_mem
  intro g _
  exact projection_mem_support F g _
    (FiniteCoreEvolution.finiteAction diagonal F
      ((FiniteCoreEvolution.coreSpan diagonal F).orthogonalProjectionOnto
        (projection g x))).property

theorem source_mem_support (F : Index) (x : diagonal.domain) (hx : x∈F) :
    (x : H)∈supportSpan F := by
  have he : ∑ g : Label, projection g (x : H)=(x : H) := by
    simpa only [sum_apply,one_apply_eq_self] using
      congrArg (fun A : H →L[ℂ] H => A (x : H)) NativeHistoryGrade.projection_resolution
  rw [←he]
  exact Submodule.sum_mem _ (fun g _ => piece_mem_support F g x hx)

theorem source_eventually_mem_support (x : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), (x : H)∈supportSpan F := by
  classical
  apply WeakCoreEvolution.sourceFilter_cofinal diagonal
  refine Filter.eventually_atTop.mpr ⟨{x},fun F hF => ?_⟩
  exact source_mem_support F x (hF (Finset.mem_singleton_self x))

theorem compression_escape_zero (F : Index) (x : H) :
    GaussGradedCompression.compression F (escapeProjection F x)=0 := by
  apply ext_inner_right ℂ
  intro y
  rw [inner_zero_left]
  exact (GaussGradedCompression.compression_pair F (escapeProjection F x) y).trans
    ((supportSpan F).starProjection_inner_eq_zero x _ (compression_mem_support F y))

theorem escape_compression_zero (F : Index) (x : H) :
    escapeProjection F (GaussGradedCompression.compression F x)=0 := by
  change GaussGradedCompression.compression F x-
    (supportSpan F).starProjection (GaussGradedCompression.compression F x)=0
  rw [Submodule.starProjection_eq_self_iff.mpr (compression_mem_support F x),sub_self]

theorem resolvent_mem_support (F : Index) (z : ℂ) (hz : z.im≠0)
    (x : H) (hx : x∈supportSpan F) : finiteResolvent F z x∈supportSpan F := by
  have hr := congrArg (fun A : H →L[ℂ] H => A x)
    (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change GaussGradedCompression.compression F (finiteResolvent F z x)-
    z • finiteResolvent F z x=x at hr
  have he : z • finiteResolvent F z x=
      GaussGradedCompression.compression F (finiteResolvent F z x)-x := by
    apply eq_sub_iff_add_eq.mpr
    exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp hr).symm
  have hz0 : z≠0 := by intro h; exact hz (h ▸ rfl)
  have hm := (supportSpan F).smul_mem z⁻¹
    (show z • finiteResolvent F z x∈supportSpan F by
      rw [he]
      exact (supportSpan F).sub_mem (compression_mem_support F _) hx)
  simpa only [smul_smul,inv_mul_cancel₀ hz0,one_smul] using hm

theorem source_resolvent_eventually_mem_support (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), finiteResolvent F z (g : H)∈supportSpan F := by
  filter_upwards [source_eventually_mem_support g] with F hF
  exact resolvent_mem_support F z hz _ hF

theorem resolvent_escape (F : Index) (z : ℂ) (hz : z.im≠0) (x : H) :
    finiteResolvent F z (escapeProjection F x)=(-z⁻¹) • escapeProjection F x := by
  have hr := congrArg (fun A : H →L[ℂ] H => A (escapeProjection F x))
    (resolvent_left _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change finiteResolvent F z
    (GaussGradedCompression.compression F (escapeProjection F x)-
      z • escapeProjection F x)=escapeProjection F x at hr
  rw [compression_escape_zero,zero_sub,map_neg,map_smul] at hr
  have hz0 : z≠0 := by intro h; exact hz (h ▸ rfl)
  have h := congrArg (fun v : H => (-z⁻¹) • v) hr
  simpa only [smul_neg,smul_smul,neg_mul,neg_neg,inv_mul_cancel₀ hz0,
    neg_one_smul,one_smul] using h

theorem resolvent_split (F : Index) (z : ℂ) (hz : z.im≠0) (x : H) :
    finiteResolvent F z x=finiteResolvent F z (supportProjection F x)+
      (-z⁻¹) • escapeProjection F x := by
  have hx : x=supportProjection F x+escapeProjection F x := by
    change x=supportProjection F x+(x-supportProjection F x)
    abel
  conv_lhs => rw [hx,map_add,resolvent_escape F z hz]

theorem resolvent_split_orthogonal (F : Index) (z : ℂ) (hz : z.im≠0) (x : H) :
    inner ℂ (finiteResolvent F z (supportProjection F x))
      ((-z⁻¹) • escapeProjection F x)=0 := by
  rw [inner_smul_right]
  have h := (supportSpan F).starProjection_inner_eq_zero x
    (finiteResolvent F z (supportProjection F x))
    (resolvent_mem_support F z hz (supportProjection F x)
      (Submodule.starProjection_apply_mem (supportSpan F) x))
  have hh : inner ℂ (finiteResolvent F z (supportProjection F x))
      (escapeProjection F x)=0 := by
    rw [←inner_conj_symm]
    change starRingEnd ℂ (inner ℂ (x-(supportSpan F).starProjection x) _)=0
    rw [h,map_zero]
  rw [hh,mul_zero]

theorem resolvent_norm_square (F : Index) (z : ℂ) (hz : z.im≠0) (x : H) :
    ‖finiteResolvent F z x‖^2=
      ‖finiteResolvent F z (supportProjection F x)‖^2+
        ‖z‖⁻¹^2*‖escapeProjection F x‖^2 := by
  rw [resolvent_split F z hz x,norm_add_sq (𝕜 := ℂ),
    resolvent_split_orthogonal F z hz x]
  simp only [map_zero,mul_zero,add_zero,norm_smul,norm_neg,norm_inv,mul_pow]

def increment (m n : ℕ) : H →L[ℂ] H := cutoff n-cutoff m

/-- Both positive legs are generated by the actual finite source compression. -/
theorem source_increment_norm_square (F : Index) (z : ℂ) (hz : z.im≠0)
    (m n : ℕ) (g : diagonal.domain) :
    ‖finiteResolvent F z (increment m n (finiteResolvent F z (g : H)))‖^2=
      ‖finiteResolvent F z
        (supportProjection F (increment m n (finiteResolvent F z (g : H))))‖^2+
      ‖z‖⁻¹^2*‖escapeProjection F (increment m n (finiteResolvent F z (g : H)))‖^2 :=
  resolvent_norm_square F z hz _

/-- Cofinality kills every fixed core test, without killing the escaped norm. -/
theorem escape_eventually_core_pair_zero (x : diagonal.domain) (v : Index → H) :
    ∀ᶠ F in (sourceFilter : Filter Index),
      inner ℂ (escapeProjection F (v F)) (x : H)=0 := by
  filter_upwards [source_eventually_mem_support x] with F hF
  exact (supportSpan F).starProjection_inner_eq_zero (v F) (x : H) hF

def incrementCore (m n : ℕ) (g : diagonal.domain) : diagonal.domain :=
  ⟨increment m n (g : H),
    diagonal.domain.sub_mem (cutoff_core_mem n g) (cutoff_core_mem m g)⟩

theorem source_escape_seed_return (z : ℂ) (hz : z.im≠0)
    (m n : ℕ) (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),
      escapeProjection F (increment m n (finiteResolvent F z (g : H)))=
        z⁻¹ • escapeProjection F (increment m n (finiteResolvent F z (diagonal g))) := by
  filter_upwards [GaussGradedCompression.eventually_exact g,
    source_eventually_mem_support (incrementCore m n g)] with F hF hD
  change increment m n (g : H)∈supportSpan F at hD
  have hzero : escapeProjection F (increment m n (g : H))=0 := by
    change increment m n (g : H)-(supportSpan F).starProjection
      (increment m n (g : H))=0
    rw [Submodule.starProjection_eq_self_iff.mpr hD,sub_self]
  have hr := congrArg (fun A : H →L[ℂ] H => A (g : H))
    (resolvent_compression _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change finiteResolvent F z (GaussGradedCompression.compression F (g : H))=
    (g : H)+z • finiteResolvent F z (g : H) at hr
  rw [hF] at hr
  have h := congrArg (fun v : H => escapeProjection F (increment m n v)) hr
  simp only [map_add,map_smul,hzero,zero_add] at h
  have hz0 : z≠0 := by intro h; exact hz (h ▸ rfl)
  simpa only [smul_smul,inv_mul_cancel₀ hz0,one_smul] using
    (congrArg (fun v : H => z⁻¹ • v) h).symm

def escapeFamily : SourceFamilyOperator.Operator Index H where
  component := escapeProjection
  bounded := ⟨1,zero_le_one,fun F x => by
    rw [one_mul]
    change ‖(1-(supportSpan F).starProjection) x‖≤‖x‖
    rw [←Submodule.starProjection_orthogonal']
    exact (supportSpan F)ᗮ.norm_starProjection_apply_le x⟩

def escaped : HistorySpace →L[ℂ] HistorySpace :=
  SourceFamilyOperator.lift sourceFilter escapeFamily

theorem escaped_core_pair_zero (x : diagonal.domain) (y : HistorySpace) :
    inner ℂ (escaped y) (inclusion (x : H))=0 := by
  refine UniformSpace.Completion.induction_on y (isClosed_eq (by fun_prop) continuous_const) ?_
  intro f
  rw [escaped,SourceFamilyOperator.lift_coe]
  change inner ℂ ((SourceFamilyOperator.act sourceFilter escapeFamily f) : HistorySpace)
    ((SourceFamilyHilbert.constant sourceFilter (x : H)) : HistorySpace)=0
  rw [SourceFamilyHilbert.inner_coe]
  apply tendsto_nhds_unique
    (SourceFamilyHilbert.pair_tendsto sourceFilter
      (SourceFamilyOperator.act sourceFilter escapeFamily f)
      (SourceFamilyHilbert.constant sourceFilter (x : H)))
  apply tendsto_const_nhds.congr'
  filter_upwards [escape_eventually_core_pair_zero x (SourceFamilyHilbert.value f)] with F hF
  exact hF.symm

theorem escaped_source_pair_zero (x : H) (y : HistorySpace) :
    inner ℂ (escaped y) (inclusion x)=0 := by
  have h : Set.EqOn (fun a : H => inner ℂ (escaped y) (inclusion a))
      (fun _ => 0) (diagonal.domain : Set H) := by
    intro a ha
    exact escaped_core_pair_zero ⟨a,ha⟩ y
  exact h.closure (by fun_prop) continuous_const (diagonal_dense x)

theorem same_resolvent_escaped (z : ℂ) (hz : z.im≠0) (y : HistorySpace) :
    sameResolvent z hz (escaped y)=(-z⁻¹) • escaped y := by
  refine UniformSpace.Completion.induction_on y
    (isClosed_eq ((sameResolvent z hz).continuous.comp escaped.continuous)
      (escaped.continuous.const_smul (-z⁻¹))) ?_
  intro f
  rw [escaped,sameResolvent,SourceFamilyOperator.lift_coe,
    SourceFamilyOperator.lift_coe,
    ←UniformSpace.Completion.coe_smul]
  congr 1
  apply SourceFamilyHilbert.Family.ext
  funext F
  exact resolvent_escape F z hz (SourceFamilyHilbert.value f F)

#print axioms compression_escape_zero
#print axioms source_resolvent_eventually_mem_support
#print axioms resolvent_escape
#print axioms source_increment_norm_square
#print axioms escape_eventually_core_pair_zero
#print axioms source_escape_seed_return
#print axioms escaped_source_pair_zero
#print axioms same_resolvent_escaped
end LowEnergy.SourceRetardedIncrement
