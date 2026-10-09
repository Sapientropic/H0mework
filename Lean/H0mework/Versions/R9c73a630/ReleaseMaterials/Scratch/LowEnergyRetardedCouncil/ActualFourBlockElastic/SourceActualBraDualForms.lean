import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateBraPairData
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualContactDualImaginaryCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.ActualBraContactDualContraction
open ActualCandidateBra ActualContactDualImaginary MixedSpectatorDual24Data
open scoped Matrix BigOperators

def dualSourceForm (t : Fin 4) (a : Fin 97) : ℂ :=
  match t.val,a.val with
  | 0,74 => (3/25 : ℂ)*(Real.sqrt 15 : ℂ)
  | 0,84 => (-1/2 : ℂ)*(Real.sqrt 2 : ℂ)
  | 0,94 => (1/2 : ℂ)*(Real.sqrt 2 : ℂ)
  | 1,73 => (3/25 : ℂ)*(Real.sqrt 15 : ℂ)
  | 1,90 => (1/2 : ℂ)*(Real.sqrt 2 : ℂ)
  | 1,95 => (-1/2 : ℂ)*(Real.sqrt 2 : ℂ)
  | 2,75 => (-3/25 : ℂ)*(Real.sqrt 15 : ℂ)
  | 2,79 => (-1/2 : ℂ)*(Real.sqrt 2 : ℂ)
  | 2,83 => (-1/2 : ℂ)*(Real.sqrt 2 : ℂ)
  | 2,86 => (-1/2 : ℂ)*(Real.sqrt 2 : ℂ)
  | 2,88 => (1/2 : ℂ)*(Real.sqrt 2 : ℂ)
  | 2,93 => (-1/2 : ℂ)*(Real.sqrt 2 : ℂ)
  | 3,75 => (-3/25 : ℂ)*(Real.sqrt 15 : ℂ)
  | 3,79 => (1/2 : ℂ)*(Real.sqrt 2 : ℂ)
  | 3,83 => (-1/2 : ℂ)*(Real.sqrt 2 : ℂ)
  | 3,86 => (1/2 : ℂ)*(Real.sqrt 2 : ℂ)
  | 3,88 => (1/2 : ℂ)*(Real.sqrt 2 : ℂ)
  | 3,93 => (1/2 : ℂ)*(Real.sqrt 2 : ℂ)
  | _,_ => 0

def dualSourceClass (i : Fin 24) : Fin 4 :=
  match i.val with
  | 12 | 16 | 18 | 22 => 1
  | 13 | 21 => 2
  | 15 | 19 => 3
  | _ => 0

def dualSourceSign (i : Fin 24) : ℂ :=
  match i.val with
  | 0 | 4 | 6 | 10 | 12 | 13 | 15 | 18 | 19 | 21 => 1
  | 16 | 22 => -1
  | _ => 0

theorem actual_dual_source_form (i : Fin 24) (a : Fin 97) :
    axialSourceMap i a = dualSourceSign i*dualSourceForm (dualSourceClass i) a := by
  unfold axialSourceMap
  split <;> simp_all [dualSourceSign,dualSourceClass,dualSourceForm] <;> norm_num
  all_goals fin_cases i <;> simp_all [dualSourceSign,dualSourceClass,dualSourceForm]
  all_goals norm_num at *
  all_goals split <;> simp_all

def dualPairForm (t u : Fin 4) : ℂ :=
  match t.val,u.val with
  | 0,0 | 1,1 => -243/250
  | 2,2 => -162/125
  | 2,3 | 3,2 => 162/125
  | _,_ => 0

private theorem sqrt2_sq : (Real.sqrt 2 : ℂ)^2 = 2 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

private theorem sqrt15_sq : (Real.sqrt 15 : ℂ)^2 = 15 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

private theorem sqrt30_sq : (Real.sqrt 30 : ℂ)^2 = 30 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

private theorem sqrt15_sqrt2_sqrt30 :
    (Real.sqrt 15 : ℂ)*(Real.sqrt 2 : ℂ)*(Real.sqrt 30 : ℂ) = 30 := by
  have h : (Real.sqrt 15 : ℂ)*(Real.sqrt 2 : ℂ) = (Real.sqrt 30 : ℂ) := by
    norm_cast
    rw [←Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 15)]
    norm_num
  rw [h,←pow_two,sqrt30_sq]

end LowEnergy.ActualBraContactDualContraction
