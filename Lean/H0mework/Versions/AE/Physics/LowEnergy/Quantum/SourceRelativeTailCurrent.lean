import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceBoundaryRadiusAction
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceResolventBandLimit

/-! The compressed boundary current has an actual uniformly bounded finite-family representative. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourceRelativeTailCurrent
open Filter SourceFamilyHilbert SourceFamilyOperator
open SourceMinimalGraphParticular SourceBoundaryGram SourceBoundaryRadiusAction
open FullYSourceResolventGraphSplice GaussCoreHilbert GaussDiagonalHistory
open GaussUnitaryHistory (Index HistorySpace sourceFilter inclusion reader)
open scoped Topology InnerProductSpace

def adjointResolventFamily (z : ℂ) (hz : z.im ≠ 0) : Operator Index H where
  component F := (finiteResolvent F z).adjoint
  bounded := ⟨1/|z.im|,by positivity,fun F x => by
    apply ((finiteResolvent F z).adjoint.le_opNorm x).trans
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact mul_le_mul_of_nonneg_right (finite_resolvent_norm F z hz) (norm_nonneg x)⟩

theorem adjoint_family_return (z : ℂ) (hz : z.im ≠ 0) :
    lift sourceFilter (adjointResolventFamily z hz)=(sameResolvent z hz).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  exact lift_pair sourceFilter (adjointResolventFamily z hz) (resolventFamily z hz)
    (fun F x y => ContinuousLinearMap.adjoint_inner_left (finiteResolvent F z) y x)

theorem body_adjoint_inclusion (z : ℂ) (x : H) :
    (sourceBody z).adjoint (inclusion x)=inclusion (sourceParticular (star z) x) := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (inclusion (maxParticular z (sourceSeen y))) (inclusion x)=_
  rw [inclusion.inner_map_map]
  change inner ℂ ((sourceParticular (star z)).adjoint (sourceSeen y)) x=_
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact ContinuousLinearMap.adjoint_inner_left sourceInclusion _ y

theorem finite_current_bound (F : Index) (z : ℂ) (hz : z.im ≠ 0) (x : H) :
    ‖sourceParticular (star z) x-(finiteResolvent F z).adjoint x‖ ≤
      (2/|z.im|)*‖x‖ := by
  have hs : (star z).im ≠ 0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  have hp : ‖sourceParticular (star z) x‖ ≤ (1/|z.im|)*‖x‖ := by
    apply ((sourceParticular (star z)).le_opNorm x).trans
    simpa only [Complex.star_def,Complex.conj_im,abs_neg] using
      mul_le_mul_of_nonneg_right (source_particular_norm (star z) hs) (norm_nonneg x)
  have hr : ‖(finiteResolvent F z).adjoint x‖ ≤ (1/|z.im|)*‖x‖ := by
    apply ((finiteResolvent F z).adjoint.le_opNorm x).trans
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact mul_le_mul_of_nonneg_right (finite_resolvent_norm F z hz) (norm_nonneg x)
  exact (norm_sub_le _ _).trans ((add_le_add hp hr).trans_eq (by ring))

def currentFamily (z : ℂ) (hz : z.im ≠ 0) : Operator Index H where
  component F := sourceParticular (star z)-(finiteResolvent F z).adjoint
  bounded := ⟨2/|z.im|,by positivity,fun F x => finite_current_bound F z hz x⟩

theorem current_family_return (z : ℂ) (hz : z.im ≠ 0) :
    lift sourceFilter (currentFamily z hz)=
      reader (sourceParticular (star z))-(sameResolvent z hz).adjoint := by
  apply SourceFamilyOperator.ext sourceFilter
  intro f
  rw [←adjoint_family_return]
  change lift sourceFilter (currentFamily z hz) (f : HistorySpace)=
    lift sourceFilter (SourceFamilyOperator.constant (sourceParticular (star z))) (f : HistorySpace)-
      lift sourceFilter (adjointResolventFamily z hz) (f : HistorySpace)
  rw [lift_coe,lift_coe,lift_coe,←UniformSpace.Completion.coe_sub]
  rfl

theorem current_boundary_return (z : ℂ) (hz : z.im ≠ 0) (x : H) :
    lift sourceFilter (currentFamily z hz) (inclusion x)=
      -(boundaryReturn z hz).adjoint (inclusion x) := by
  have hc := congrArg (fun T : HistorySpace →L[ℂ] HistorySpace => T (inclusion x))
    (current_family_return z hz)
  have hb := congrArg (fun T : HistorySpace →L[ℂ] HistorySpace => T (inclusion x))
    (map_sub ContinuousLinearMap.adjoint (sameResolvent z hz) (sourceBody z))
  change (boundaryReturn z hz).adjoint (inclusion x)=
    (sameResolvent z hz).adjoint (inclusion x)-(sourceBody z).adjoint (inclusion x) at hb
  rw [body_adjoint_inclusion] at hb
  change lift sourceFilter (currentFamily z hz) (inclusion x)=
    reader (sourceParticular (star z)) (inclusion x)-(sameResolvent z hz).adjoint (inclusion x) at hc
  have hc' := hc.trans (congrArg (fun y : HistorySpace =>
    y-(sameResolvent z hz).adjoint (inclusion x))
    (GaussUnitaryHistory.reader_inclusion (sourceParticular (star z)) x))
  calc
    _ = inclusion (sourceParticular (star z) x)-(sameResolvent z hz).adjoint (inclusion x) := hc'
    _ = -((sameResolvent z hz).adjoint (inclusion x)-inclusion (sourceParticular (star z) x)) := by abel
    _ = _ := (congrArg Neg.neg hb).symm

theorem original_core_current_return (z : ℂ) (hz : z.im ≠ 0)
    (W : H →L[ℂ] H) (x : diagonal.domain) (hx : W (x : H)∈diagonal.domain) :
    lift sourceFilter (currentFamily z hz)
      (inclusion (W (shift diagonal (star z) x)))=
      (boundaryReturn z hz).adjoint (inclusion (coreCommutator W x hx)) := by
  rw [current_boundary_return]
  have h := congrArg Neg.neg (boundary_core_action z hz W x hx)
  simpa only [GaussUnitaryHistory.reader_inclusion,neg_neg] using h

def scalarTail (m ell : ℕ) : H →L[ℂ] H :=
  (1-GaussRadialDomain.inverseRadius)^(m+1)-(1-GaussRadialDomain.inverseRadius)^(ell+1)

theorem complement_power_mem_core (k : ℕ) (x : diagonal.domain) :
    ((1-GaussRadialDomain.inverseRadius)^k) (x : H)∈diagonal.domain := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',mul_apply_eq_comp,sub_apply,one_apply_eq_self]
    exact diagonal.domain.sub_mem ih (inverse_mem_core ⟨_,ih⟩)

theorem scalar_tail_mem_core (m ell : ℕ) (x : diagonal.domain) :
    scalarTail m ell (x : H)∈diagonal.domain :=
  diagonal.domain.sub_mem (complement_power_mem_core (m+1) x) (complement_power_mem_core (ell+1) x)

theorem original_tail_current_return (z : ℂ) (hz : z.im ≠ 0)
    (m ell : ℕ) (x : diagonal.domain) :
    lift sourceFilter (currentFamily z hz)
      (inclusion (scalarTail m ell (shift diagonal (star z) x)))=
      (boundaryReturn z hz).adjoint
        (inclusion (coreCommutator (scalarTail m ell) x (scalar_tail_mem_core m ell x))) :=
  original_core_current_return z hz (scalarTail m ell) x (scalar_tail_mem_core m ell x)

open MeasureTheory SourceResolventBandLimit

/-- The lambda integral is evaluated on each finite F before the source filter. -/
theorem finite_current_lintegral_bound (F : Index) (μ : ℝ) (hμ : 0<μ)
    (h : ℝ → H) (ν : Measure ℝ) :
    (∫⁻ t, ENNReal.ofReal (‖sourceParticular (star (line μ t)) (h t)-
      (finiteResolvent F (line μ t)).adjoint (h t)‖^2) ∂ν) ≤
      ENNReal.ofReal ((2/μ)^2)*(∫⁻ t, ENNReal.ofReal (‖h t‖^2) ∂ν) := by
  calc
    _ ≤ ∫⁻ t, ENNReal.ofReal ((2/μ)^2)*ENNReal.ofReal (‖h t‖^2) ∂ν := by
      apply lintegral_mono
      intro t
      dsimp only
      rw [←ENNReal.ofReal_mul (sq_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have hb := finite_current_bound F (line μ t)
        (by simpa only [line_im] using ne_of_gt hμ) (h t)
      simp only [line_im,abs_of_pos hμ] at hb
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem finite_tail_current_lintegral_bound (F : Index) (μ : ℝ) (hμ : 0<μ)
    (m ell : ℕ) (h : ℝ → H) (ν : Measure ℝ) :
    (∫⁻ t, ENNReal.ofReal (‖sourceParticular (star (line μ t)) (scalarTail m ell (h t))-
      (finiteResolvent F (line μ t)).adjoint (scalarTail m ell (h t))‖^2) ∂ν) ≤
      ENNReal.ofReal ((2/μ)^2)*(∫⁻ t, ENNReal.ofReal (‖scalarTail m ell (h t)‖^2) ∂ν) :=
  finite_current_lintegral_bound F μ hμ (fun t => scalarTail m ell (h t)) ν

#print axioms adjoint_family_return
#print axioms current_boundary_return
#print axioms original_core_current_return
#print axioms finite_current_bound
#print axioms finite_current_lintegral_bound
#print axioms original_tail_current_return
#print axioms finite_tail_current_lintegral_bound
end LowEnergy.SourceRelativeTailCurrent
