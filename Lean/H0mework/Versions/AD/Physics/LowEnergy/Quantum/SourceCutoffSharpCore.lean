import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceCutoffVolterra

/-! The independent source adjoint consumes the same cutoff integral occurrence. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LowEnergy.FullYSourceCutoffSharp
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory
open GaussUnitaryHistory (HistorySpace sourceFilter inclusion)
open FullYSourceCutoffVolterra
open scoped Topology InnerProductSpace ContDiff

theorem bounded_sharp_core (f : QuantumTest) :
    GaussYukawaOperator.bounded.adjoint (embed f)=
      embed (GaussFullHamiltonian.adjointAction (GaussRadialDomain.inverseAction f)) := by
  apply ext_inner_left ℂ
  intro y
  refine GaussBoundedMultiplier.core_dense.induction_on y
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  obtain ⟨g,rfl⟩ := coreEquiv.surjective a
  change inner ℂ (embed g) (GaussYukawaOperator.bounded.adjoint (embed f))=
    inner ℂ (embed g) (embed (GaussFullHamiltonian.adjointAction (GaussRadialDomain.inverseAction f)))
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hg := GaussRadialDomain.original_graph g
  change GaussYukawaOperator.bounded (embed g)=
    GaussRadialDomain.inverseRadius (embed (GaussYukawaOperator.originalAction g)) at hg
  rw [hg,GaussRadialDomain.inverse_pair,GaussRadialDomain.inverse_core]
  exact (GaussFullHamiltonian.yukawa_pair g (GaussRadialDomain.inverseAction f)).symm

private theorem bounded_sharp_core_mem (x : Core) :
    GaussYukawaOperator.bounded.adjoint (x : H) ∈ Core := by
  obtain ⟨f,hf⟩ := embed_surjective_core x
  rw [← hf,bounded_sharp_core]
  exact embed_mem_core _

private theorem inverse_core_mem (x : Core) :
    GaussRadialDomain.inverseRadius (x : H) ∈ Core := by
  obtain ⟨f,hf⟩ := embed_surjective_core x
  rw [← hf,GaussRadialDomain.inverse_core]
  exact embed_mem_core _

private theorem sharp_recursion_algebra {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (B S A : E →L[ℂ] E)
    (hS : IsSelfAdjoint S) :
    (B+(1-S)*A).adjoint=B.adjoint+A.adjoint*(1-S) := by
  change star (B+(1-S)*A)=star B+star A*(1-S)
  rw [star_add,star_mul,star_sub,star_one,hS.star_eq]

theorem cutoff_sharp_recursion (n : ℕ) :
    (cutoff (n+1)).adjoint=GaussYukawaOperator.bounded.adjoint+
      (cutoff n).adjoint*(1-GaussRadialDomain.inverseRadius) := by
  have hs : IsSelfAdjoint GaussRadialDomain.inverseRadius :=
    (show GaussRadialDomain.inverseRadius.toLinearMap.IsSymmetric from
      fun x y => GaussRadialDomain.inverse_pair x y).isSelfAdjoint
  exact sharp_recursion_algebra GaussYukawaOperator.bounded GaussRadialDomain.inverseRadius (cutoff n) hs

theorem cutoff_sharp_core_mem (n : ℕ) (x : Core) : (cutoff n).adjoint (x : H) ∈ Core := by
  induction n generalizing x with
  | zero => exact bounded_sharp_core_mem x
  | succ n ih =>
    rw [cutoff_sharp_recursion]
    change GaussYukawaOperator.bounded.adjoint (x : H)+
      (cutoff n).adjoint ((x : H)-GaussRadialDomain.inverseRadius (x : H)) ∈ Core
    exact Core.add_mem (bounded_sharp_core_mem x)
      (ih ⟨_,Core.sub_mem x.property (inverse_core_mem x)⟩)

def sourceSharpFullCore (cut : ℕ) (x : diagonal.domain) : diagonal.domain :=
  ⟨diagonal x+(cutoff cut).adjoint (x : H),
    Core.add_mem (diagonal_invariant x) (cutoff_sharp_core_mem cut x)⟩

theorem source_full_core_pair (cut : ℕ) (x y : diagonal.domain) :
    inner ℂ (sourceFullCore cut x : H) (y : H)=
      inner ℂ (x : H) (sourceSharpFullCore cut y : H) := by
  change inner ℂ (diagonal x+cutoff cut (x : H)) (y : H)=
    inner ℂ (x : H) (diagonal y+(cutoff cut).adjoint (y : H))
  rw [inner_add_left,inner_add_right]
  exact congrArg₂ (· + ·) (diagonal_pair x y)
    (ContinuousLinearMap.adjoint_inner_right (cutoff cut) (x : H) (y : H)).symm

theorem eventually_sharp_exact (cut : ℕ) (x : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter GaussUnitaryHistory.Index),
      (GaussGradedCompression.compression F+(cutoff cut).adjoint) (x : H)=
        (sourceSharpFullCore cut x : H) := by
  filter_upwards [GaussGradedCompression.eventually_exact x] with F hF
  change GaussGradedCompression.compression F (x : H)+(cutoff cut).adjoint (x : H)=_
  rw [hF]
  rfl

theorem source_sharp_time_bound (cut : ℕ) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    ‖SourceFiniteUnitary.time (GaussGradedCompression.compression F+(cutoff cut).adjoint) t‖ ≤
      sourceGrowth cut |t| := by
  rw [← time_sum_adjoint _ _ (GaussGradedCompression.compression_selfAdjoint F),
    ContinuousLinearMap.adjoint.norm_map]
  simpa only [abs_neg] using source_finite_time_bound cut F (-t)

theorem source_sharp_core_remainder (cut : ℕ) (x : diagonal.domain) (t h : ℝ) :
    ‖sourceSharpEvolution cut (t+h) (inclusion (x : H))-
      sourceSharpEvolution cut t (inclusion (x : H))-
      h • ((-Complex.I) • sourceSharpEvolution cut t (inclusion (sourceSharpFullCore cut x : H)))‖ ≤
      (sourceGrowth cut (|t|+‖h‖)*‖(sourceSharpFullCore cut (sourceSharpFullCore cut x) : H)‖)*‖h‖^2 := by
  apply lift_generator_remainder sourceFilter (sourceSharpEvolutionFamily cut)
    (fun F => GaussGradedCompression.compression F+(cutoff cut).adjoint)
    (x : H) (sourceSharpFullCore cut x : H) (sourceSharpFullCore cut (sourceSharpFullCore cut x) : H)
    t h (sourceGrowth cut (|t|+‖h‖)) (fun _ _ => rfl) ?_
    (eventually_sharp_exact cut x) (eventually_sharp_exact cut (sourceSharpFullCore cut x))
  intro F u hu
  have hd : |u-t| ≤ ‖h‖ := by simpa only [Metric.mem_closedBall,Real.dist_eq] using hu
  have hu' : |u| ≤ |t|+‖h‖ := by
    have ha := abs_add_le (u-t) t
    rw [sub_add_cancel] at ha
    linarith
  exact (source_sharp_time_bound cut F u).trans (sourceGrowth_mono cut (abs_nonneg u) hu')

theorem source_sharp_core_derivative (cut : ℕ) (x : diagonal.domain) (t : ℝ) :
    HasDerivAt (fun s => sourceSharpEvolution cut s (inclusion (x : H)))
      ((-Complex.I) • sourceSharpEvolution cut t (inclusion (sourceSharpFullCore cut x : H))) t := by
  rw [hasDerivAt_iff_tendsto]
  let D := ‖(sourceSharpFullCore cut (sourceSharpFullCore cut x) : H)‖
  have hcont : Continuous (fun s : ℝ => sourceGrowth cut (|t|+‖s-t‖)*D*‖s-t‖) := by
    unfold sourceGrowth
    fun_prop
  have hlim : Filter.Tendsto (fun s : ℝ => sourceGrowth cut (|t|+‖s-t‖)*D*‖s-t‖)
      (𝓝 t) (𝓝 0) := by simpa only [sub_self,norm_zero,mul_zero] using hcont.tendsto t
  apply squeeze_zero (fun s => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    (fun s => ?_) hlim
  have hb := source_sharp_core_remainder cut x t (s-t)
  have he := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (norm_nonneg (s-t)))
  have hi : t+(s-t)=s := by ring
  rw [hi] at he
  have scalar : ‖s-t‖⁻¹*((sourceGrowth cut (|t|+‖s-t‖)*D)*‖s-t‖^2)=
      sourceGrowth cut (|t|+‖s-t‖)*D*‖s-t‖ := by
    by_cases hz : ‖s-t‖=0
    · simp [hz]
    · field_simp
  exact he.trans_eq scalar

theorem source_sharp_core_smooth (cut : ℕ) (x : diagonal.domain) :
    ContDiff ℝ ∞ (fun t => sourceSharpEvolution cut t (inclusion (x : H))) := by
  rw [contDiff_infty]
  intro n
  induction n generalizing x with
  | zero => exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
      (fun t => (source_sharp_core_derivative cut x t).continuousAt))
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_deriv]
    refine ⟨fun t => (source_sharp_core_derivative cut x t).differentiableAt, ?_, ?_⟩
    · simp
    · have hd : deriv (fun t => sourceSharpEvolution cut t (inclusion (x : H)))=
          fun t => (-Complex.I) • sourceSharpEvolution cut t (inclusion (sourceSharpFullCore cut x : H)) :=
        funext (fun t => (source_sharp_core_derivative cut x t).deriv)
      rw [hd]
      exact (ih (sourceSharpFullCore cut x)).const_smul (-Complex.I)

#print axioms bounded_sharp_core
#print axioms cutoff_sharp_core_mem
#print axioms source_full_core_pair
#print axioms source_sharp_core_derivative
#print axioms source_sharp_core_smooth
end LowEnergy.FullYSourceCutoffSharp
