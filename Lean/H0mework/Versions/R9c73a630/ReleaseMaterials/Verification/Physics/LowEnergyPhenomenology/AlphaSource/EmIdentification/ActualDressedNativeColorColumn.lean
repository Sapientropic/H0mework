import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeColorSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedConstraintHistory

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNativeQuantumWard
open PreparationVacuumMixedFieldReturn PreparationVacuumOriginalGreenFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open SourcePropagationNativeActionHessian ActualDressedNullNative
open scoped Matrix BigOperators
attribute [local irreducible] originalChange
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

private theorem vec_three_last {A : Type*} (x y z : A) :
    (![x,y,z] : Fin 3→A) ⟨2,by omega⟩=z:=rfl

private theorem real_indicator (P : Prop) [Decidable P] :
    (((if P then (1:ℝ) else 0):ℝ):ℂ)=(if P then (1:ℂ) else 0) :=by
  by_cases h : P <;> simp [h]

private theorem mul_indicator (P : Prop) [Decidable P] (x c : ℂ) :
    (x*(if P then 1 else 0))*c=(if P then x*c else 0) :=by
  by_cases h : P <;> simp [h]

private theorem if_negative_half (P : Prop) [Decidable P] (x : ℂ) :
    (if P then x*(-1/2) else 0)= -(if P then x*(1/2) else 0) :=by
  by_cases h : P
  · simp only [if_pos h]
    ring
  · simp [h]

private theorem source_entry (terms : List SourceTerm) (p : Fin 4→ℂ) (row col : Fin 289) :
    sourceMatrix terms p row col=(terms.map (fun t=>coefficientValue t.coefficient*t.powers.value p*
      if row=t.row ∧ col=t.column then 1 else 0)).sum :=by
  induction terms with
  | nil=>rfl
  | cons t rest ih=>
    rw [sourceMatrix_cons,Matrix.add_apply,ih]
    simp [SourceTerm.matrix,Matrix.single_apply,mul_ite,eq_comm]

private def colorColumn (p : Fin 4→ℂ) (g : Fin 3) (row : Fin 289) : ℂ:=
  ![∑mu : Fin 4,(p mu/2)*(gaugeField mu 1 row:ℂ),
    ∑mu : Fin 4,(p mu/2)*(gaugeField mu 0 row:ℂ),
    ∑mu : Fin 4,(p mu/2)*((gaugeField mu 6 row:ℂ)-(gaugeField mu 7 row:ℂ))] g

private theorem single_weight (p : ℂ) (k : Fin 12) (read : Fin 12→ℂ) :
    (∑a : Fin 12,p*((((Pi.single k (1/2:ℝ) : Fin 12→ℝ) a):ℝ):ℂ)*read a)=(p/2)*read k :=by
  rw [Finset.sum_eq_single k]
  · simp only [Pi.single_eq_same,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
    ring
  · intro a _ other
    simp [other]
  · simp

private theorem color_column_sum (p : Fin 4→ℂ) (g : Fin 3) (row : Fin 289) :
    (∑a : Fin 12,∑mu : Fin 4,(p mu*(gaugeColorRaw g a:ℂ))*(gaugeField mu a row:ℂ))=colorColumn p g row :=by
  rw [Finset.sum_comm]
  fin_cases g
  · change (∑mu : Fin 4,∑a : Fin 12,p mu*((((Pi.single 1 (1/2:ℝ) : Fin 12→ℝ) a):ℝ):ℂ)*
      (gaugeField mu a row:ℂ))=∑mu : Fin 4,(p mu/2)*(gaugeField mu 1 row:ℂ)
    exact Finset.sum_congr rfl (fun mu _=>single_weight (p mu) 1 (fun a=>(gaugeField mu a row:ℂ)))
  · change (∑mu : Fin 4,∑a : Fin 12,p mu*((((Pi.single 0 (1/2:ℝ) : Fin 12→ℝ) a):ℝ):ℂ)*
      (gaugeField mu a row:ℂ))=∑mu : Fin 4,(p mu/2)*(gaugeField mu 0 row:ℂ)
    exact Finset.sum_congr rfl (fun mu _=>single_weight (p mu) 0 (fun a=>(gaugeField mu a row:ℂ)))
  · simp only [gaugeColorRaw,colorColumn,vec_three_last]
    apply Finset.sum_congr rfl
    intro mu _
    simp only [Pi.sub_apply,Complex.ofReal_sub,mul_sub,sub_mul,Finset.sum_sub_distrib,single_weight]

/-- All original289 components remain: only the true source color gauge-current terms depend on the Fourier covector. -/
theorem original_color_column_gradient (p : Fin 4→ℂ) (g : Fin 3) :
    originalNullColumn p (Fin.castAdd 6 g)=originalNullColumn 0 (Fin.castAdd 6 g)-
      ∑a : Fin 12,∑mu : Fin 4,(p mu*(gaugeColorRaw g a:ℂ)) •
        (fun row=>(gaugeField mu a row:ℂ)) :=by
  funext row
  simp only [Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [color_column_sum,original_null_column_literal,original_null_column_literal,source_entry,source_entry]
  fin_cases g
  all_goals norm_num [nullColumnTerms,nullColumnIndex,Fin.castAdd,Fin.castLE,Fin.ext_iff]
  all_goals norm_num [coefficientValue,Powers.value,rootTwo,rootFifteen,colorColumn,
    gaugeField,gaugeSlot,Pi.single_apply,Fin.sum_univ_four,Fin.ext_iff]
  all_goals ring_nf
  all_goals simp only [real_indicator,mul_indicator,if_negative_half]

end LowEnergy.GaussComposite.ActualDressedNativeQuantumWard
