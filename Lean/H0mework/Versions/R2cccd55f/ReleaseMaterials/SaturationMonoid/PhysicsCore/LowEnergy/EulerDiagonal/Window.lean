import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! A test is chosen in physical time. Its support lies strictly after the
original initial surface; contact distributions are not assigned half weights. -/
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace ENNReal
namespace SaturationMonoid.PhysicsCore.LowEnergy.EulerDiagonal
noncomputable section

structure TimeTest where
  cutoff : ℝ → ℝ
  smooth : ContDiff ℝ ∞ cutoff
  compact : HasCompactSupport cutoff
  future : tsupport cutoff ⊆ Ioi 0

def testBump (center : ℝ) (positive : 0 < center) : ContDiffBump center where
  rIn := center / 4
  rOut := center / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

def testAt (center : ℝ) (positive : 0 < center) : TimeTest where
  cutoff := testBump center positive
  smooth := (testBump center positive).contDiff
  compact := (testBump center positive).hasCompactSupport
  future := by
    intro t ht
    rw [ContDiffBump.tsupport_eq, Metric.mem_closedBall, Real.dist_eq] at ht
    change |t-center| ≤ center/2 at ht
    have := (abs_le.mp ht).1
    simp only [mem_Ioi]
    linarith

theorem testAt_center (center : ℝ) (positive : 0 < center) :
    (testAt center positive).cutoff center = 1 := by
  exact (testBump center positive).one_of_mem_closedBall (by simp [testBump]; positivity)

def weight (test : TimeTest) (damping time : ℝ) : ℂ :=
  (test.cutoff time * Real.exp (-damping*time) : ℝ)

theorem weight_smooth (test : TimeTest) (damping : ℝ) :
    ContDiff ℝ ∞ (weight test damping) := by
  unfold weight
  exact Complex.ofRealCLM.contDiff.comp (test.smooth.mul (contDiff_const.mul contDiff_id).exp)

theorem weight_compact (test : TimeTest) (damping : ℝ) :
    HasCompactSupport (weight test damping) := by
  apply test.compact.mono
  intro t ht
  contrapose! ht
  simp only [Function.mem_support] at ht ⊢
  simp [weight, ht]

theorem weight_future (test : TimeTest) (damping : ℝ) :
    tsupport (weight test damping) ⊆ Ioi 0 := by
  refine Set.Subset.trans ?_ test.future
  apply closure_mono
  intro t ht
  contrapose! ht
  simp only [Function.mem_support] at ht ⊢
  simp [weight, ht]

theorem weight_zero_near_initial (test : TimeTest) (damping : ℝ) :
    weight test damping =ᶠ[𝓝 0] 0 := by
  apply notMem_tsupport_iff_eventuallyEq.mp
  intro member
  exact (lt_irrefl (0 : ℝ)) (weight_future test damping member)

theorem weight_initial (test : TimeTest) (damping : ℝ) :
    weight test damping 0 = 0 ∧ deriv (weight test damping) 0 = 0 := by
  have near := weight_zero_near_initial test damping
  exact ⟨near.eq_of_nhds, by simpa using near.deriv_eq⟩

theorem weight_derivative (test : TimeTest) (damping time : ℝ) :
    HasDerivAt (weight test damping)
      (((deriv test.cutoff time-damping*test.cutoff time)*Real.exp (-damping*time) : ℝ) : ℂ) time := by
  have dcut := (test.smooth.differentiable (by simp) time).hasDerivAt
  have dexp := ((hasDerivAt_id time).const_mul (-damping)).exp
  convert! Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt time (dcut.mul dexp) using 1
  congr 1
  simp only [Algebra.algebraMap_self_apply, id_eq]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def tested (test : TimeTest) (damping : ℝ) (field : ℝ → E) (time : ℝ) : E :=
  weight test damping time • field time

theorem tested_continuous (test : TimeTest) (damping : ℝ) {field : ℝ → E}
    (continuousField : Continuous field) : Continuous (tested test damping field) :=
  (weight_smooth test damping).continuous.smul continuousField

theorem tested_compact (test : TimeTest) (damping : ℝ) (field : ℝ → E) :
    HasCompactSupport (tested test damping field) :=
  (weight_compact test damping).smul_right

theorem tested_memLp (test : TimeTest) (damping : ℝ) {field : ℝ → E}
    (continuousField : Continuous field) (p : ℝ≥0∞) :
    MemLp (tested test damping field) p volume :=
  (tested_continuous test damping continuousField).memLp_of_hasCompactSupport
    (tested_compact test damping field)

def timeLp (test : TimeTest) (damping : ℝ) (field : ℝ → E)
    (continuousField : Continuous field) : Lp E 2 (volume : Measure ℝ) :=
  (tested_memLp test damping continuousField 2).toLp _

theorem timeLp_ae (test : TimeTest) (damping : ℝ) (field : ℝ → E)
    (continuousField : Continuous field) :
    timeLp test damping field continuousField =ᵐ[volume] tested test damping field :=
  (tested_memLp test damping continuousField 2).coeFn_toLp

end
end SaturationMonoid.PhysicsCore.LowEnergy.EulerDiagonal
