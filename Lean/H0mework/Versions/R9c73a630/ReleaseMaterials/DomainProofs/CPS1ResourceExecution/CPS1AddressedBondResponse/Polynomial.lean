import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1AddressedBondResponse.Generic
noncomputable section
open Filter
open scoped Topology

structure Quartic where
  c1 : ℝ
  c2 : ℝ
  c3 : ℝ
  c4 : ℝ

inductive Degree
  | linear
  | quadratic
  | cubic
  | quartic

def Quartic.delta (q : Quartic) (time : ℝ) : ℝ :=
  q.c1*time+q.c2*time^2+q.c3*time^3+q.c4*time^4

def Quartic.coefficient (q : Quartic) : Degree → ℝ
  | .linear => q.c1
  | .quadratic => q.c2
  | .cubic => q.c3
  | .quartic => q.c4

def Quartic.leading? (q : Quartic) : Option Degree := by
  classical
  exact if q.c1 ≠ 0 then some .linear else
    if q.c2 ≠ 0 then some .quadratic else
    if q.c3 ≠ 0 then some .cubic else
    if q.c4 ≠ 0 then some .quartic else none

private theorem residual_eventually_positive (a b c d : ℝ) (nonzero : a ≠ 0) :
    ∀ᶠ time in 𝓝 (0 : ℝ), 0 < a*(a+b*time+c*time^2+d*time^3) := by
  have continuous : ContinuousAt (fun time : ℝ => a*(a+b*time+c*time^2+d*time^3)) 0 :=
    continuousAt_const.mul (((continuousAt_const.add
      (continuousAt_const.mul continuousAt_id)).add
      (continuousAt_const.mul (continuousAt_id.pow 2))).add
      (continuousAt_const.mul (continuousAt_id.pow 3)))
  exact continuousAt_const.eventually_lt continuous (by simpa using mul_self_pos.mpr nonzero)

theorem quartic_eventually_signed (q : Quartic) (degree : Degree)
    (generated : q.leading? = some degree) :
    ∀ᶠ time in 𝓝 (0 : ℝ), 0 < time → 0 < q.coefficient degree*q.delta time := by
  classical
  by_cases first : q.c1 = 0
  · by_cases second : q.c2 = 0
    · by_cases third : q.c3 = 0
      · by_cases fourth : q.c4 = 0
        · simp [Quartic.leading?,first,second,third,fourth] at generated
        · have selected : Degree.quartic = degree := by
            simpa [Quartic.leading?,first,second,third,fourth] using generated
          subst degree
          exact Filter.Eventually.of_forall fun time positive => by
            change 0 < q.c4*q.delta time
            rw [Quartic.delta,first,second,third]
            simpa only [zero_mul,zero_add] using
              (show 0 < q.c4*(q.c4*time^4) from by
                rw [← mul_assoc]
                exact mul_pos (mul_self_pos.mpr fourth) (pow_pos positive 4))
      · have selected : Degree.cubic = degree := by
          simpa [Quartic.leading?,first,second,third] using generated
        subst degree
        filter_upwards [residual_eventually_positive q.c3 q.c4 0 0 third] with time residual
        intro positive
        change 0 < q.c3*q.delta time
        have factor : q.c3*q.delta time = time^3*(q.c3*(q.c3+q.c4*time)) := by
          dsimp [Quartic.delta]
          rw [first,second]
          ring
        rw [factor]
        exact mul_pos (pow_pos positive 3) (by simpa using residual)
    · have selected : Degree.quadratic = degree := by
        simpa [Quartic.leading?,first,second] using generated
      subst degree
      filter_upwards [residual_eventually_positive q.c2 q.c3 q.c4 0 second] with time residual
      intro positive
      change 0 < q.c2*q.delta time
      have factor : q.c2*q.delta time = time^2*(q.c2*(q.c2+q.c3*time+q.c4*time^2)) := by
        dsimp [Quartic.delta]
        rw [first]
        ring
      rw [factor]
      exact mul_pos (pow_pos positive 2) (by simpa using residual)
  · have selected : Degree.linear = degree := by
      simpa [Quartic.leading?,first] using generated
    subst degree
    filter_upwards [residual_eventually_positive q.c1 q.c2 q.c3 q.c4 first] with time residual
    intro positive
    change 0 < q.c1*q.delta time
    have factor : q.c1*q.delta time = time*(q.c1*(q.c1+q.c2*time+q.c3*time^2+q.c4*time^3)) := by
      dsimp [Quartic.delta]
      ring
    rw [factor]
    exact mul_pos positive residual

end
end CPS1AddressedBondResponse.Generic
