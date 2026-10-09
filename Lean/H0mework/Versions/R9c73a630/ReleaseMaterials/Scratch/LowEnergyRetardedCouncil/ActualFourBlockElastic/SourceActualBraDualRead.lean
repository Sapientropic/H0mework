import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualBraDualForms

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
open ActualCandidateBra
open scoped BigOperators Matrix

def dualSourceRead (t : Fin 4) (f : Fin 97 → ℂ) : ℂ :=
  match t.val with
  | 0 => (3/25 : ℂ)*(Real.sqrt 15 : ℂ)*f 74 -
      (1/2 : ℂ)*(Real.sqrt 2 : ℂ)*f 84 + (1/2 : ℂ)*(Real.sqrt 2 : ℂ)*f 94
  | 1 => (3/25 : ℂ)*(Real.sqrt 15 : ℂ)*f 73 +
      (1/2 : ℂ)*(Real.sqrt 2 : ℂ)*f 90 - (1/2 : ℂ)*(Real.sqrt 2 : ℂ)*f 95
  | 2 => (-3/25 : ℂ)*(Real.sqrt 15 : ℂ)*f 75 -
      (1/2 : ℂ)*(Real.sqrt 2 : ℂ)*f 79 - (1/2 : ℂ)*(Real.sqrt 2 : ℂ)*f 83 -
      (1/2 : ℂ)*(Real.sqrt 2 : ℂ)*f 86 + (1/2 : ℂ)*(Real.sqrt 2 : ℂ)*f 88 -
      (1/2 : ℂ)*(Real.sqrt 2 : ℂ)*f 93
  | _ => (-3/25 : ℂ)*(Real.sqrt 15 : ℂ)*f 75 +
      (1/2 : ℂ)*(Real.sqrt 2 : ℂ)*f 79 - (1/2 : ℂ)*(Real.sqrt 2 : ℂ)*f 83 +
      (1/2 : ℂ)*(Real.sqrt 2 : ℂ)*f 86 + (1/2 : ℂ)*(Real.sqrt 2 : ℂ)*f 88 +
      (1/2 : ℂ)*(Real.sqrt 2 : ℂ)*f 93

private theorem source_form_delta (t : Fin 4) (a : Fin 97) :
    dualSourceForm t a = dualSourceRead t (fun b => if a = b then 1 else 0) := by
  fin_cases t <;> fin_cases a <;> norm_num [dualSourceForm,dualSourceRead,Fin.ext_iff]

theorem actual_dual_form_sum (t : Fin 4) (f : Fin 97 → ℂ) :
    (∑a : Fin 97,dualSourceForm t a*f a) = dualSourceRead t f := by
  simp_rw [source_form_delta]
  fin_cases t <;> simp [dualSourceRead,add_mul,sub_mul,Finset.sum_add_distrib,
    Finset.sum_sub_distrib,Finset.mul_sum,mul_assoc]

theorem actual_dual_form_pair_return (t u : Fin 4) (dual : Bool) :
    (∑a : Fin 97,∑b : Fin 97,dualSourceForm t a*pairPoint dual a b*dualSourceForm u b) =
      dualSourceRead t (fun a => dualSourceRead u (fun b => pairPoint dual a b)) := by
  have hb (a : Fin 97) :
      (∑b : Fin 97,dualSourceForm t a*pairPoint dual a b*dualSourceForm u b) =
        dualSourceForm t a*(∑b : Fin 97,dualSourceForm u b*pairPoint dual a b) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [hb,actual_dual_form_sum]

end LowEnergy.ActualBraContactDualContraction
