import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualNullNativeColumn

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNullNative
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedFieldReturn
open scoped Matrix BigOperators

private theorem coefficient_imaginary_zero (c : SourceCoefficient) : (coefficientValue c).im=0 := by
  simp [coefficientValue,rootTwo,rootFifteen]

private theorem affine_monomial (c : SourceCoefficient) (powers : Powers) (degree : powers.total ≤ 1)
    (p : Fin 4→ℂ) :
    (coefficientValue c*powers.value p).re=
      (coefficientValue c*powers.value (fun mu=>((p mu).re:ℂ))).re ∧
    (coefficientValue c*powers.value p).im=
      (coefficientValue c*powers.value (fun mu=>((p mu).im:ℂ))).re-
        (coefficientValue c*powers.value 0).re := by
  rcases powers with ⟨a,b,d,e⟩
  have total : a+b+d+e ≤ 1:=degree
  have ha : a ≤ 1:=by omega
  have hb : b ≤ 1:=by omega
  have hd : d ≤ 1:=by omega
  have he : e ≤ 1:=by omega
  interval_cases a <;> interval_cases b <;> interval_cases d <;> interval_cases e
  all_goals norm_num at total
  all_goals simp [Powers.value,Complex.mul_re,Complex.mul_im,coefficient_imaginary_zero]

private theorem affine_term (term : SourceTerm) (degree : term.powers.total ≤ 1)
    (p : Fin 4→ℂ) (row col : Fin 289) :
    (term.matrix p row col).re=(term.matrix (fun mu=>((p mu).re:ℂ)) row col).re ∧
    (term.matrix p row col).im=(term.matrix (fun mu=>((p mu).im:ℂ)) row col).re-(term.matrix 0 row col).re := by
  have scalar:=affine_monomial term.coefficient term.powers degree p
  by_cases inside : term.row=row ∧ term.column=col
  · simpa [SourceTerm.matrix,inside] using scalar
  · simp [SourceTerm.matrix,inside]

private theorem affine_source_matrix (terms : List SourceTerm) (degree : ∀t∈terms,t.powers.total ≤ 1)
    (p : Fin 4→ℂ) (row col : Fin 289) :
    (sourceMatrix terms p row col).re=(sourceMatrix terms (fun mu=>((p mu).re:ℂ)) row col).re ∧
    (sourceMatrix terms p row col).im=(sourceMatrix terms (fun mu=>((p mu).im:ℂ)) row col).re-
      (sourceMatrix terms 0 row col).re := by
  induction terms with
  | nil=>norm_num [sourceMatrix]
  | cons t rest ih=>
    obtain ⟨left,right⟩:=affine_term t (degree t (by simp)) p row col
    obtain ⟨tailLeft,tailRight⟩:=ih (fun u hu=>degree u (by simp [hu]))
    simp only [sourceMatrix_cons,Matrix.add_apply,Complex.add_re,Complex.add_im,left,tailLeft,right,tailRight]
    constructor
    · exact True.intro
    · ring

private theorem null_degree (n : Fin 9) : ∀t∈nullColumnTerms n,t.powers.total ≤ 1 := by
  have certificate : ∀n : Fin 9,(nullColumnTerms n).all (fun t=>decide (t.powers.total ≤ 1))=true := by decide +kernel
  intro t member
  exact of_decide_eq_true (List.all_eq_true.mp (certificate n) t member)

/-- The complete source column's real Fourier quadrature keeps the original unit parameter. -/
theorem original_null_real_part (p : Fin 4→ℂ) (n : Fin 9) :
    (fun row=>(originalNullColumn p n row).re)=originalNullReal (fun mu=>(p mu).re) n := by
  funext row
  unfold originalNullReal
  rw [original_null_column_literal,original_null_column_literal]
  exact (affine_source_matrix (nullColumnTerms n) (null_degree n) p row (nullColumnIndex n)).1

/-- The imaginary Fourier quadrature is the actual derivative part; the fixed-reference column is subtracted, not discarded. -/
theorem original_null_imaginary_part (p : Fin 4→ℂ) (n : Fin 9) :
    (fun row=>(originalNullColumn p n row).im)=
      originalNullReal (fun mu=>(p mu).im) n-originalNullReal 0 n := by
  funext row
  simp only [Pi.sub_apply,originalNullReal]
  rw [original_null_column_literal,original_null_column_literal,original_null_column_literal]
  exact (affine_source_matrix (nullColumnTerms n) (null_degree n) p row (nullColumnIndex n)).2

end LowEnergy.GaussComposite.ActualDressedNullNative
