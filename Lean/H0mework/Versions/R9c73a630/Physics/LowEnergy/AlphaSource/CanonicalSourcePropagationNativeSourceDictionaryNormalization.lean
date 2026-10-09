import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationNativeFourierDictionary

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
noncomputable section
namespace LowEnergy.SourcePropagationNativeActionHessian
open PreparationVacuumOriginalGreenFeedback
open scoped BigOperators

def nativeSourceKey (t : SourceTerm) : ℕ :=
  (((((t.row.val*289+t.column.val)*3+t.powers.temporal)*3+t.powers.first)*3+
    t.powers.second)*3+t.powers.third)

def sourceAdjacentInsert (a : SourceTerm) : List SourceTerm → List SourceTerm
  | [] => if a.coefficient=0 then [] else [a]
  | b::rest => if a.sameKey b then
      let c := a.coefficient+b.coefficient
      if c=0 then rest else {b with coefficient:=c}::rest
    else if a.coefficient=0 then b::rest else a::b::rest

def sourceAdjacentNormalize (terms : List SourceTerm) : List SourceTerm :=
  terms.foldr sourceAdjacentInsert []

def sourceCanonicalTerms (terms : List SourceTerm) : List SourceTerm :=
  sourceAdjacentNormalize (terms.mergeSort fun a b => nativeSourceKey a ≤ nativeSourceKey b)

private theorem nativeSourceTerm_zero (a : SourceTerm) (zero : a.coefficient=0) (p : Fin 4 → ℂ) :
    a.matrix p=0 := by simp [SourceTerm.matrix,zero,coefficient_zero]

private theorem nativeSourceSameKey (a b : SourceTerm) (same : a.sameKey b=true) (p : Fin 4 → ℂ) :
    ({b with coefficient:=a.coefficient+b.coefficient}:SourceTerm).matrix p = a.matrix p+b.matrix p := by
  have h : a.row=b.row ∧ a.column=b.column ∧ a.powers=b.powers := of_decide_eq_true same
  simp only [SourceTerm.matrix,h.1,h.2.1,h.2.2,coefficient_add,add_mul,Matrix.single_add]

theorem sourceAdjacentInsert_value (a : SourceTerm) (terms : List SourceTerm) (p : Fin 4 → ℂ) :
    sourceMatrix (sourceAdjacentInsert a terms) p = a.matrix p+sourceMatrix terms p := by
  cases terms with
  | nil =>
    simp only [sourceAdjacentInsert,sourceMatrix_nil]
    split_ifs with zero
    · rw [nativeSourceTerm_zero a zero p,add_zero]
      rfl
    · simp [sourceMatrix]
  | cons b rest =>
    simp only [sourceAdjacentInsert]
    split_ifs with same zero zero
    · have eq := nativeSourceSameKey a b same p
      rw [nativeSourceTerm_zero _ zero p] at eq
      rw [sourceMatrix_cons,←add_assoc,←eq,zero_add]
    · rw [sourceMatrix_cons,nativeSourceSameKey a b same p,sourceMatrix_cons,add_assoc]
    · rw [nativeSourceTerm_zero a zero p,zero_add]
    · rw [sourceMatrix_cons]

theorem sourceAdjacentNormalize_value (terms : List SourceTerm) (p : Fin 4 → ℂ) :
    sourceMatrix (sourceAdjacentNormalize terms) p = sourceMatrix terms p := by
  induction terms with
  | nil => rfl
  | cons a rest ih =>
    change sourceMatrix (sourceAdjacentInsert a (sourceAdjacentNormalize rest)) p = _
    rw [sourceAdjacentInsert_value,ih,sourceMatrix_cons]

theorem sourceCanonicalTerms_value (terms : List SourceTerm) (p : Fin 4 → ℂ) :
    sourceMatrix (sourceCanonicalTerms terms) p=sourceMatrix terms p := by
  rw [sourceCanonicalTerms,sourceAdjacentNormalize_value]
  exact ((List.mergeSort_perm terms _).map (fun term => term.matrix p)).sum_eq

end LowEnergy.SourcePropagationNativeActionHessian
