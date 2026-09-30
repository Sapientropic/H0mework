import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false

namespace LAlanineContinuousPatch.Parametric

noncomputable section

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def rk4Step (field : E → E) (h : ℝ) (x : E) : E :=
  let k1 := field x
  let k2 := field (x + (h / 2) • k1)
  let k3 := field (x + (h / 2) • k2)
  let k4 := field (x + h • k3)
  x + (h / 6) • (k1 + 2 • k2 + 2 • k3 + k4)

def stageDerivative (h : ℝ) (dh : P →L[ℝ] ℝ) (x' : P →L[ℝ] E)
    (k : E) (k' : P →L[ℝ] E) (scale : ℝ) : P →L[ℝ] E :=
  x' + scale • (h • k' + dh.smulRight k)

def rk4Derivative (field : E → E) (jacobian : E → E →L[ℝ] E)
    (h : ℝ) (dh : P →L[ℝ] ℝ) (x : E) (x' : P →L[ℝ] E) : P →L[ℝ] E :=
  let k1 := field x
  let d1 := (jacobian x).comp x'
  let x2 := x + (h / 2) • k1
  let j2 := stageDerivative h dh x' k1 d1 (1 / 2)
  let k2 := field x2
  let d2 := (jacobian x2).comp j2
  let x3 := x + (h / 2) • k2
  let j3 := stageDerivative h dh x' k2 d2 (1 / 2)
  let k3 := field x3
  let d3 := (jacobian x3).comp j3
  let x4 := x + h • k3
  let j4 := stageDerivative h dh x' k3 d3 1
  let k4 := field x4
  let d4 := (jacobian x4).comp j4
  stageDerivative h dh x' (k1 + 2 • k2 + 2 • k3 + k4)
    (d1 + 2 • d2 + 2 • d3 + d4) (1 / 6)

private theorem hasFDerivAt_stage {h : P → ℝ} {dh : P →L[ℝ] ℝ}
    {x k : P → E} {dx dk : P →L[ℝ] E} {p : P}
    (hh : HasFDerivAt h dh p) (hx : HasFDerivAt x dx p) (hk : HasFDerivAt k dk p)
    (scale : ℝ) :
    HasFDerivAt (fun p => x p + (scale * h p) • k p)
      (stageDerivative (h p) dh dx (k p) dk scale) p := by
  convert hx.add ((hh.const_mul scale).smul hk) using 1 <;>
    ext v <;> simp [stageDerivative, mul_smul, smul_add]

theorem rk4Step_hasFDerivAt (field : E → E) (jacobian : E → E →L[ℝ] E)
    (field_derivative : ∀ x, HasFDerivAt field (jacobian x) x)
    {h : P → ℝ} {dh : P →L[ℝ] ℝ} {x : P → E} {dx : P →L[ℝ] E} {p : P}
    (hh : HasFDerivAt h dh p) (hx : HasFDerivAt x dx p) :
    HasFDerivAt (fun p => rk4Step field (h p) (x p))
      (rk4Derivative field jacobian (h p) dh (x p) dx) p := by
  have k1 := (field_derivative (x p)).comp p hx
  have x2 := hasFDerivAt_stage hh hx k1 (1 / 2)
  have k2 := (field_derivative _).comp p x2
  have x3 := hasFDerivAt_stage hh hx k2 (1 / 2)
  have k3 := (field_derivative _).comp p x3
  have x4 := hasFDerivAt_stage hh hx k3 1
  have k4 := (field_derivative _).comp p x4
  have combined := ((k1.add (k2.const_smul (2 : ℝ))).add (k3.const_smul (2 : ℝ))).add k4
  simpa only [rk4Step, rk4Derivative, one_mul, one_div_mul_eq_div,
    Function.comp_apply, Pi.add_apply, Pi.smul_apply, two_smul] using
    hasFDerivAt_stage hh hx combined (1 / 6)

def rk4JetStep (field : E → E) (jacobian : E → E →L[ℝ] E)
    (h : ℝ) (dh : P →L[ℝ] ℝ) (state : E × (P →L[ℝ] E)) : E × (P →L[ℝ] E) :=
  (rk4Step field h state.1, rk4Derivative field jacobian h dh state.1 state.2)

def rk4JetIterate (field : E → E) (jacobian : E → E →L[ℝ] E)
    (n : Nat) (h : ℝ) (dh : P →L[ℝ] ℝ) (x : E) (dx : P →L[ℝ] E) :=
  ((rk4JetStep field jacobian h dh)^[n]) (x, dx)

theorem rk4JetIterate_value (field : E → E) (jacobian : E → E →L[ℝ] E)
    (n : Nat) (h : ℝ) (dh : P →L[ℝ] ℝ) (x : E) (dx : P →L[ℝ] E) :
    (rk4JetIterate field jacobian n h dh x dx).1 = ((rk4Step field h)^[n]) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [rk4JetIterate, Function.iterate_succ_apply', rk4JetStep] using
      congrArg (rk4Step field h) ih

theorem rk4Iterate_hasFDerivAt (field : E → E) (jacobian : E → E →L[ℝ] E)
    (field_derivative : ∀ x, HasFDerivAt field (jacobian x) x)
    {h : P → ℝ} {dh : P →L[ℝ] ℝ} {x : P → E} {dx : P →L[ℝ] E} {p : P}
    (hh : HasFDerivAt h dh p) (hx : HasFDerivAt x dx p) (n : Nat) :
    HasFDerivAt (fun p => ((rk4Step field (h p))^[n]) (x p))
      (rk4JetIterate field jacobian n (h p) dh (x p) dx).2 p := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    simp only [rk4JetIterate, Function.iterate_succ_apply', rk4JetStep]
    change HasFDerivAt (fun p => rk4Step field (h p) (((rk4Step field (h p))^[n]) (x p)))
      (rk4Derivative field jacobian (h p) dh
        (rk4JetIterate field jacobian n (h p) dh (x p) dx).1
        (rk4JetIterate field jacobian n (h p) dh (x p) dx).2) p
    rw [rk4JetIterate_value]
    exact rk4Step_hasFDerivAt field jacobian field_derivative hh ih

theorem rk4Step_contDiff (field : E → E) {order : WithTop ℕ∞}
    (smooth : ContDiff ℝ order field) {h : P → ℝ} {x : P → E}
    (hh : ContDiff ℝ order h) (hx : ContDiff ℝ order x) :
    ContDiff ℝ order (fun p => rk4Step field (h p) (x p)) := by
  have k1 := smooth.comp hx
  have k2 := smooth.comp (hx.add ((hh.div_const 2).smul k1))
  have k3 := smooth.comp (hx.add ((hh.div_const 2).smul k2))
  have k4 := smooth.comp (hx.add (hh.smul k3))
  simpa only [rk4Step, Function.comp_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply', two_smul] using
    hx.add ((hh.div_const 6).smul (((k1.add (k2.const_smul (2 : ℝ))).add
      (k3.const_smul (2 : ℝ))).add k4))

theorem rk4Iterate_contDiff (field : E → E) {order : WithTop ℕ∞}
    (smooth : ContDiff ℝ order field) {h : P → ℝ} {x : P → E}
    (hh : ContDiff ℝ order h) (hx : ContDiff ℝ order x) (n : Nat) :
    ContDiff ℝ order (fun p => ((rk4Step field (h p))^[n]) (x p)) := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    simpa only [Function.iterate_succ_apply'] using rk4Step_contDiff field smooth hh ih

end
end LAlanineContinuousPatch.Parametric
