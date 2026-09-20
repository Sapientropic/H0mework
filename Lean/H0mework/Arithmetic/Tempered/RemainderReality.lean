import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import H0mework.Arithmetic.Tempered.Remainder
import H0mework.Arithmetic.Tempered.RealStructure

/-!
# Reality and nonzeroness of the Clozel tempered remainder

The actual remainder is fixed by real conjugation.  A compactly supported
Schwartz witness whose only nonzero integer sample is at zero proves that the
remainder itself is nonzero.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelEndpointSourceEffect

open Complex FourierTransform MeasureTheory
open scoped SchwartzMap RealInnerProductSpace

noncomputable section

theorem clozelTemperedRemainder_isReal :
    IsReal clozelTemperedRemainder := by
  unfold IsReal
  ext test
  simp only [realConjugation_apply]
  rw [clozelTemperedRemainder_apply,
    clozelTemperedRemainder_apply]
  rw [star_sub, star_sub, tsum_star]
  simp_rw [schwartzConjugation_apply, star_star]
  have integralStar :
      (∫ x : ℝ, star (test x)) = star (∫ x : ℝ, test x) := by
    exact integral_conj
  rw [integralStar, star_star]

def remainderWitnessBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

def remainderWitnessRealSchwartz : 𝓢(ℝ, ℝ) :=
  remainderWitnessBump.hasCompactSupport.toSchwartzMap
    remainderWitnessBump.contDiff

def remainderWitnessSchwartz : 𝓢(ℝ, ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM
    remainderWitnessRealSchwartz

@[simp] theorem remainderWitnessSchwartz_apply (x : ℝ) :
    remainderWitnessSchwartz x = (remainderWitnessBump x : ℂ) := by
  rfl

theorem remainderWitnessBump_zero_at_nonzeroInteger
    (n : ℤ) (nonzero : n ≠ 0) :
    remainderWitnessBump (n : ℝ) = 0 := by
  apply remainderWitnessBump.zero_of_le_dist
  have oneLe : (1 : ℝ) ≤ |(n : ℝ)| := by
    exact_mod_cast Int.one_le_abs nonzero
  simpa [remainderWitnessBump, Real.dist_eq] using
    (show (1 / 2 : ℝ) ≤ |(n : ℝ)| by linarith)

@[simp] theorem remainderWitnessBump_zero_value :
    remainderWitnessBump 0 = 1 := by
  apply remainderWitnessBump.one_of_mem_closedBall
  simp [remainderWitnessBump]

theorem remainderWitness_integer_tsum :
    (∑' n : ℤ, remainderWitnessSchwartz n) = 1 := by
  rw [tsum_eq_single 0]
  · simp
  · intro n nonzero
    rw [remainderWitnessSchwartz_apply,
      remainderWitnessBump_zero_at_nonzeroInteger n nonzero]
    exact ofReal_zero

theorem remainderWitnessBump_integral_pos :
    0 < ∫ x : ℝ, remainderWitnessBump x := by
  apply remainderWitnessBump.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    remainderWitnessBump.hasCompactSupport
    (by intro x; simpa using remainderWitnessBump.nonneg' x)
    (x := 0)
  simp

theorem clozelTemperedRemainder_witness_value :
    clozelTemperedRemainder remainderWitnessSchwartz =
      -((∫ x : ℝ, remainderWitnessBump x : ℝ) : ℂ) := by
  rw [clozelTemperedRemainder_apply,
    remainderWitness_integer_tsum]
  simp only [remainderWitnessSchwartz_apply,
    remainderWitnessBump_zero_value, ofReal_one]
  rw [integral_complex_ofReal]
  ring

theorem clozelTemperedRemainder_witness_value_ne_zero :
    clozelTemperedRemainder remainderWitnessSchwartz ≠ 0 := by
  rw [clozelTemperedRemainder_witness_value]
  exact neg_ne_zero.mpr <|
    Complex.ofReal_ne_zero.mpr (ne_of_gt remainderWitnessBump_integral_pos)

theorem clozelTemperedRemainder_ne_zero :
    clozelTemperedRemainder ≠ 0 := by
  intro zero
  have evaluated := congrArg
    (fun distribution : ComplexTempered =>
      distribution remainderWitnessSchwartz) zero
  rw [zero_apply] at evaluated
  exact clozelTemperedRemainder_witness_value_ne_zero evaluated

end

end ClozelEndpointSourceEffect
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
