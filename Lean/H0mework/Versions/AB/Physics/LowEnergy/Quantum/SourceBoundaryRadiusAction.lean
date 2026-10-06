import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceBoundaryGram
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceSignedRadiusBalance

/-! The original radius acts on the source-seen boundary through its actual commutator. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourceBoundaryRadiusAction
open Filter SymmetricGraphClosure
open SourceBoundaryGram SourceMinimalGraphParticular SourceSignedRadiusBalance
open GaussCoreHilbert GaussDiagonalHistory
open GaussUnitaryHistory (HistorySpace inclusion reader)
open scoped InnerProductSpace Topology

theorem boundary_adjoint_core_zero (z : ℂ) (hz : z.im≠0) (x : diagonal.domain) :
    (boundaryReturn z hz).adjoint (inclusion (shift diagonal (star z) x))=0 := by
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left,inner_zero_left]
  exact boundary_source_pair_zero z hz x y

def coreCommutator (W : H →L[ℂ] H) (x : diagonal.domain)
    (hx : W (x : H)∈diagonal.domain) : H :=
  diagonal ⟨W (x : H),hx⟩-W (diagonal x)

theorem boundary_core_action (z : ℂ) (hz : z.im≠0) (W : H →L[ℂ] H)
    (x : diagonal.domain) (hx : W (x : H)∈diagonal.domain) :
    (boundaryReturn z hz).adjoint (reader W (inclusion (shift diagonal (star z) x)))=
      -(boundaryReturn z hz).adjoint (inclusion (coreCommutator W x hx)) := by
  let wx : diagonal.domain := ⟨W (x : H),hx⟩
  have he : shift diagonal (star z) wx=
      W (shift diagonal (star z) x)+coreCommutator W x hx := by
    change diagonal wx-star z • W (x : H)=
      W (diagonal x-star z • (x : H))+(diagonal wx-W (diagonal x))
    rw [map_sub,map_smul]
    abel
  have ha := boundary_adjoint_core_zero z hz wx
  let T : H →L[ℂ] HistorySpace := (boundaryReturn z hz).adjoint.comp sourceInclusion
  have hm : T (shift diagonal (star z) wx)=
      T (W (shift diagonal (star z) x))+T (coreCommutator W x hx) :=
    (congrArg T he).trans (T.map_add _ _)
  have hs : T (W (shift diagonal (star z) x))+T (coreCommutator W x hx)=0 :=
    hm.symm.trans ha
  calc
    _ = (boundaryReturn z hz).adjoint
        (inclusion (W (shift diagonal (star z) x))) :=
      congrArg (boundaryReturn z hz).adjoint
        (GaussUnitaryHistory.reader_inclusion W (shift diagonal (star z) x))
    _ = _ := eq_neg_of_add_eq_zero_left hs

theorem boundary_core_action_bound (z : ℂ) (hz : z.im≠0) (W : H →L[ℂ] H)
    (x : diagonal.domain) (hx : W (x : H)∈diagonal.domain) :
    ‖(boundaryReturn z hz).adjoint
      (reader W (inclusion (shift diagonal (star z) x)))‖≤
        (1/|z.im|)*‖coreCommutator W x hx‖ := by
  have hb : ‖boundaryReturn z hz‖≤1/|z.im| :=
    (boundaryReturn z hz).opNorm_le_bound (by positivity) (boundary_return_bound z hz)
  rw [boundary_core_action z hz W x hx,norm_neg]
  apply ((boundaryReturn z hz).adjoint.le_opNorm _).trans
  rw [ContinuousLinearMap.adjoint.norm_map,inclusion.norm_map]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

theorem inverse_mem_core (x : diagonal.domain) :
    GaussRadialDomain.inverseRadius (x : H)∈diagonal.domain := by
  obtain ⟨f,rfl⟩ := coreEquiv.surjective x
  change GaussRadialDomain.inverseRadius (embed f)∈Core
  rw [GaussRadialDomain.inverse_core]
  exact embed_mem_core _

theorem radius_mem_core (m : ℕ) (x : diagonal.domain) :
    radiusCutoff m (x : H)∈diagonal.domain := by
  induction m with
  | zero => simpa only [radiusCutoff,Nat.zero_add,Finset.sum_range_one,pow_zero,
      one_apply_eq_self] using x.property
  | succ m ih =>
    rw [radius_recursion,add_apply,one_apply_eq_self,mul_apply_eq_comp,
      sub_apply,one_apply_eq_self]
    exact diagonal.domain.add_mem x.property
      (diagonal.domain.sub_mem ih (inverse_mem_core ⟨_,ih⟩))

def squaredRadius (m : ℕ) : H →L[ℂ] H := radiusCutoff m*radiusCutoff m

theorem squared_radius_mem_core (m : ℕ) (x : diagonal.domain) :
    squaredRadius m (x : H)∈diagonal.domain :=
  radius_mem_core m ⟨radiusCutoff m (x : H),radius_mem_core m x⟩

def quadraticSourceCommutator (m : ℕ) (x : diagonal.domain) : H :=
  coreCommutator (squaredRadius m) x (squared_radius_mem_core m x)

theorem original_quadratic_boundary_action (z : ℂ) (hz : z.im≠0)
    (m : ℕ) (x : diagonal.domain) :
    (boundaryReturn z hz).adjoint
      (reader (squaredRadius m) (inclusion (shift diagonal (star z) x)))=
        -(boundaryReturn z hz).adjoint (inclusion (quadraticSourceCommutator m x)) :=
  boundary_core_action z hz (squaredRadius m) x (squared_radius_mem_core m x)

theorem original_quadratic_boundary_bound (z : ℂ) (hz : z.im≠0)
    (m : ℕ) (x : diagonal.domain) :
    ‖(boundaryReturn z hz).adjoint
      (reader (squaredRadius m) (inclusion (shift diagonal (star z) x)))‖≤
        (1/|z.im|)*‖quadraticSourceCommutator m x‖ :=
  boundary_core_action_bound z hz (squaredRadius m) x (squared_radius_mem_core m x)

/-- This is the mixed Gram leg itself, with the same original source column. -/
theorem original_quadratic_cross_leg (z : ℂ) (hz : z.im≠0)
    (m : ℕ) (x : diagonal.domain) (y : HistorySpace) :
    inner ℂ (reader (squaredRadius m) (inclusion (shift diagonal (star z) x)))
      (boundaryReturn z hz y)=
        -inner ℂ (inclusion (quadraticSourceCommutator m x)) (boundaryReturn z hz y) := by
  have he := congrArg (fun v : HistorySpace => inner ℂ v y)
    (original_quadratic_boundary_action z hz m x)
  simpa only [ContinuousLinearMap.adjoint_inner_left,inner_neg_left] using he

theorem quadratic_compressed_weak_limit (z : ℂ) (hz : z.im≠0) (m : ℕ)
    (x : ℕ → diagonal.domain) (v h : H)
    (hx : Tendsto (fun k => (x k : H)) atTop (𝓝 v))
    (hHx : Tendsto (fun k => diagonal (x k)) atTop (𝓝 h)) :
    Tendsto (fun k => (boundaryReturn z hz).adjoint
      (inclusion (quadraticSourceCommutator m (x k)))) atTop
      (𝓝 (-(boundaryReturn z hz).adjoint
        (reader (squaredRadius m) (inclusion (h-star z • v))))) := by
  let T : H →L[ℂ] HistorySpace := (boundaryReturn z hz).adjoint.comp
    ((reader (squaredRadius m)).comp sourceInclusion)
  have hs : Tendsto (fun k => shift diagonal (star z) (x k)) atTop (𝓝 (h-star z • v)) :=
    hHx.sub (tendsto_const_nhds.smul hx)
  have ht := ((T.continuous.tendsto (h-star z • v)).comp hs).neg
  apply ht.congr'
  apply Filter.Eventually.of_forall
  intro k
  have he := congrArg Neg.neg (original_quadratic_boundary_action z hz m (x k))
  change -(boundaryReturn z hz).adjoint
    (reader (squaredRadius m) (inclusion (shift diagonal (star z) (x k)))) = _
  simpa only [neg_neg] using he

def bodyPreimage (z : ℂ) (y : HistorySpace) : H :=
  sourceParticular (star z) (maxParticular z (sourceSeen y))

def bodyGraphValue (z : ℂ) (y : HistorySpace) : H :=
  sourceGraphAction (star z) (maxParticular z (sourceSeen y))

theorem body_preimage_original_graph (z : ℂ) (hz : z.im≠0) (y : HistorySpace) :
    (bodyPreimage z y,bodyGraphValue z y)∈closedGraph diagonal := by
  have hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  exact source_particular_graph (star z) hs _

theorem body_preimage_shift (z : ℂ) (y : HistorySpace) :
    bodyGraphValue z y-star z • bodyPreimage z y=maxParticular z (sourceSeen y) := by
  let p := maxParticular z (sourceSeen y)
  have hp : (shiftedRange diagonal (star z)).starProjection p=p :=
    Submodule.starProjection_eq_self_iff.mpr (max_particular_mem_source_range z _)
  change (star z • bodyPreimage z y+(shiftedRange diagonal (star z)).starProjection p)-
    star z • bodyPreimage z y=p
  rw [hp]
  abel

#print axioms radius_mem_core
#print axioms original_quadratic_boundary_action
#print axioms original_quadratic_boundary_bound
#print axioms original_quadratic_cross_leg
#print axioms quadratic_compressed_weak_limit
#print axioms body_preimage_original_graph
#print axioms body_preimage_shift
end LowEnergy.SourceBoundaryRadiusAction
