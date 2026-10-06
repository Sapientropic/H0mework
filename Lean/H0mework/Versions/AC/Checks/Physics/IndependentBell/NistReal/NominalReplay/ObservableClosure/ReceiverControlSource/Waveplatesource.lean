import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

set_option autoImplicit false

namespace P23.ReceiverControl

open Matrix
open scoped BigOperators
noncomputable section

abbrev Jones := Matrix (Fin 2) (Fin 2) ℂ
abbrev Polarization := Fin 2 → ℂ

inductive QuarterRecipe where
  | aligned
  | orthogonal

structure Pose where
  firstHWP : ℝ
  lastHWP : ℝ
  quarterRecipe : QuarterRecipe

def quarterAxis (p : Pose) : ℝ :=
  2*p.lastHWP+match p.quarterRecipe with | .aligned => 0 | .orthogonal => Real.pi/2

def hwp (t : ℝ) : Jones :=
  !![(Real.cos (2*t) : ℂ),(Real.sin (2*t) : ℂ);
    (Real.sin (2*t) : ℂ),-(Real.cos (2*t) : ℂ)]

def quarterScale : ℝ := 1/Real.sqrt 2
def qwp (q : ℝ) : Jones := (quarterScale : ℂ) • (1-Complex.I • hwp q)
def nativeJones (p : Pose) : Jones := hwp p.lastHWP*qwp (quarterAxis p)*hwp p.firstHWP
def physicalV : Polarization := ![0,1]
def analyzer (a : ℝ) : Polarization := ![(Real.sin a : ℂ),(Real.cos a : ℂ)]
def effectiveAngle (p : Pose) : ℝ := 2*(p.lastHWP-p.firstHWP)
def pulledPort (p : Pose) : Polarization := (nativeJones p)ᴴ *ᵥ physicalV
def rankOne (v : Polarization) : Jones := vecMulVec v (star v)
def nativeEffect (p : Pose) : Jones := (nativeJones p)ᴴ*rankOne physicalV*nativeJones p

def quarterPhase (r : QuarterRecipe) : ℂ :=
  match r with
  | .aligned => (quarterScale : ℂ)*(1-Complex.I)
  | .orthogonal => (quarterScale : ℂ)*(1+Complex.I)

theorem quarterScale_sq : 2*quarterScale^2=1 := by
  have hr : Real.sqrt (2:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  dsimp [quarterScale]
  field_simp [hr]
  norm_num [Real.sq_sqrt]

theorem quarterPhase_unit (r : QuarterRecipe) : quarterPhase r*star (quarterPhase r)=1 := by
  have hs : (2:ℂ)*(quarterScale : ℂ)^2=1 := by exact_mod_cast quarterScale_sq
  cases r <;> simp [quarterPhase,star_mul,Complex.star_def] <;>
    linear_combination hs

theorem hwp_adjoint (t : ℝ) : (hwp t)ᴴ=hwp t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hwp,Matrix.conjTranspose_apply]

theorem hwp_add_quarter_turn (t : ℝ) : hwp (t+Real.pi/2) = -hwp t := by
  have ht : 2*(t+Real.pi/2)=2*t+Real.pi := by ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hwp,ht,Real.sin_add_pi,Real.cos_add_pi]

def lastPort (o : ℝ) : Polarization := ![(Real.sin (2*o) : ℂ),-(Real.cos (2*o) : ℂ)]

theorem last_hwp_port (o : ℝ) : hwp o *ᵥ physicalV=lastPort o := by
  ext i
  fin_cases i <;> simp [hwp,physicalV,lastPort,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem double_hwp_port (o : ℝ) : hwp (2*o) *ᵥ lastPort o= -lastPort o := by
  have hs := Real.sin_sq_add_cos_sq (2*o)
  ext i
  fin_cases i <;> simp [hwp,lastPort,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
    Real.sin_two_mul,Real.cos_two_mul]
  all_goals norm_cast
  · nlinarith [hs]
  · nlinarith [hs]

theorem qwp_adjoint (q : ℝ) :
    (qwp q)ᴴ=(quarterScale : ℂ) • (1+Complex.I • hwp q) := by
  simp [qwp,Matrix.conjTranspose_smul,Matrix.conjTranspose_sub,hwp_adjoint,Complex.star_def]

theorem quarter_pull_last (p : Pose) :
    (qwp (quarterAxis p))ᴴ *ᵥ lastPort p.lastHWP = quarterPhase p.quarterRecipe • lastPort p.lastHWP := by
  rw [qwp_adjoint,Matrix.smul_mulVec,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec]
  cases hc : p.quarterRecipe
  · simp only [quarterAxis,hc,add_zero,double_hwp_port,quarterPhase]
    module
  · simp only [quarterAxis,hc,hwp_add_quarter_turn,Matrix.neg_mulVec,double_hwp_port,neg_neg,quarterPhase]
    module

theorem hwp_pair_port (m o : ℝ) : hwp m *ᵥ lastPort o=analyzer (2*(o-m)) := by
  have ht : 2*(o-m)=2*o-2*m := by ring
  ext i
  fin_cases i <;> simp [hwp,lastPort,analyzer,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
    ht,Real.sin_sub,Real.cos_sub]
  all_goals ring

theorem native_pulled_port (p : Pose) :
    pulledPort p=quarterPhase p.quarterRecipe • analyzer (effectiveAngle p) := by
  dsimp [pulledPort,nativeJones]
  rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,hwp_adjoint,hwp_adjoint]
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,last_hwp_port,quarter_pull_last,
    Matrix.mulVec_smul,hwp_pair_port]
  rfl

theorem pulled_rankOne (J : Jones) : Jᴴ*rankOne physicalV*J=rankOne (Jᴴ *ᵥ physicalV) := by
  ext i j
  simp [rankOne,physicalV,Matrix.mul_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
    Matrix.conjTranspose_apply]

theorem phase_rankOne (r : QuarterRecipe) (v : Polarization) :
    rankOne (quarterPhase r • v)=rankOne v := by
  ext i j
  dsimp [rankOne,vecMulVec]
  simp only [Pi.smul_apply,smul_eq_mul,Pi.star_apply,star_mul]
  linear_combination v i*star (v j)*(quarterPhase_unit r)

theorem native_effective_projector (p : Pose) : nativeEffect p=rankOne (analyzer (effectiveAngle p)) := by
  rw [nativeEffect,pulled_rankOne,native_pulled_port,phase_rankOne]

def signedBasis : Jones := !![0,-1;1,0]
def codeAnalyzer (a : ℝ) : Polarization := ![(Real.cos a : ℂ),-(Real.sin a : ℂ)]

theorem signedBasis_unit : signedBasisᴴ*signedBasis=1 ∧ signedBasis*signedBasisᴴ=1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [signedBasis,Matrix.conjTranspose_apply,Matrix.mul_apply,Fin.sum_univ_succ]

theorem signed_analyzer (a : ℝ) : signedBasis *ᵥ analyzer a= -codeAnalyzer a := by
  ext i
  fin_cases i <;> simp [signedBasis,analyzer,codeAnalyzer,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem signed_effect (p : Pose) :
    signedBasis*nativeEffect p*signedBasisᴴ=rankOne (codeAnalyzer (effectiveAngle p)) := by
  rw [native_effective_projector]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [signedBasis,rankOne,analyzer,codeAnalyzer,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fin.sum_univ_succ]
  all_goals ring

def transported (J : Jones) : Jones := signedBasis*J*signedBasisᴴ

theorem transport_product (A B : Jones) : transported (A*B)=transported A*transported B := by
  dsimp [transported]
  calc
    signedBasis*(A*B)*signedBasisᴴ = signedBasis*A*(signedBasisᴴ*signedBasis)*B*signedBasisᴴ := by
      rw [signedBasis_unit.1]
      simp [Matrix.mul_assoc]
    _ = (signedBasis*A*signedBasisᴴ)*(signedBasis*B*signedBasisᴴ) := by simp [Matrix.mul_assoc]

theorem transport_trace (A : Jones) : (transported A).trace=A.trace := by
  rw [transported,Matrix.trace_mul_comm]
  rw [← Matrix.mul_assoc,signedBasis_unit.1,Matrix.one_mul]

theorem transport_born (rho effect : Jones) :
    (transported rho*transported effect).trace=(rho*effect).trace := by
  rw [← transport_product,transport_trace]

end
end P23.ReceiverControl
