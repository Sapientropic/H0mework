import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineResponseWords

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEngineCancellation
open PreparationVacuumEngineSource PreparationVacuumEngineIdentities PreparationVacuumEngineResponse
open PreparationVacuumCanonicalMoyal
open scoped BigOperators

open Lean Elab Term in
elab "table_const%" name:str : term => do
  unless #["table","sourceSeries","traceSeries","crossFirst","crossSecond","crossSlot"].contains name.getString do
    throwError "Not an original source Engine table input"
  let ns := Name.str (Name.str (Name.num `_private.H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineProgram 0) "LowEnergy") "PreparationVacuumEngineSource"
  Lean.Meta.mkConstWithFreshMVarLevels (Name.str ns name.getString)

private abbrev originalT := program_const% "applyT"
private abbrev originalWord := program_const% "word"
private abbrev originalTable := table_const% "table"

theorem average_sub (P Q : AngularPolynomial) : average (P-Q)=average P-average Q := by
  unfold average
  change (AddMonoidAlgebra.coeff P-AddMonoidAlgebra.coeff Q).sum (fun u f => fun zp => angularMoment u*f zp)=
    (AddMonoidAlgebra.coeff P).sum (fun u f => fun zp => angularMoment u*f zp)-(AddMonoidAlgebra.coeff Q).sum (fun u f => fun zp => angularMoment u*f zp)
  apply Finsupp.sum_sub_index
  intro u f g
  funext zp
  change angularMoment u*(f zp-g zp)=angularMoment u*f zp-angularMoment u*g zp
  ring

private theorem foldl_add {α : Type*} (xs : List α) (f : α → AngularPolynomial) (initial : AngularPolynomial) :
    xs.foldl (fun out term => out+f term) initial=initial+(xs.map f).sum := by
  induction xs generalizing initial with
  | nil => simp
  | cons t xs ih => simp only [List.foldl_cons,ih,List.map_cons,List.sum_cons,add_assoc]

private theorem list_sum_sub {α : Type*} (xs : List α) (f g : α → AngularPolynomial) :
    (xs.map f).sum-(xs.map g).sum=(xs.map (fun t => f t-g t)).sum := by
  induction xs with
  | nil => simp
  | cons t xs ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [←ih]
    ring

def sourceTableResponse (k : ℕ) (a b : Fin 4) (equation : Option (Fin 4))
    (X : List AngularPolynomial) : Symbol :=
  average ((originalTable a b equation).foldl (fun out term =>
    out+MvPolynomial.C (fun _ => term.coefficient)*
      (MvPolynomial.monomial term.exponent 1*(sourceWordPair k term.tokens (X.getD 0 0) 0).2)) 0)

private theorem word_response (k : ℕ) (tokens : List Token) (X : List AngularPolynomial) :
    (originalWord (k+1) (sourceEngine (k+1)) tokens X).getD (k+1) 0-
      (originalWord (k+1) (sourceEngine k) tokens X).getD (k+1) 0=
      (sourceWordPair k tokens (X.getD 0 0) 0).2 := by
  have response := (sourceWord_newest k tokens X X (fun _ _ => rfl)).2
  change (originalWord (k+1) (sourceEngine (k+1)) tokens X).getD (k+1) 0-
    (originalWord (k+1) (sourceEngine k) tokens X).getD (k+1) 0=
    (sourceWordPair k tokens (X.getD 0 0) (X.getD (k+1) 0-X.getD (k+1) 0)).2 at response
  simpa only [sub_self] using response

theorem sourceTable_newest (k : ℕ) (a b : Fin 4) (equation : Option (Fin 4))
    (X : List AngularPolynomial) :
    originalT (k+1) (sourceEngine (k+1)) a b equation X (Fin.last (k+1))-
      originalT (k+1) (sourceEngine k) a b equation X (Fin.last (k+1))=
      sourceTableResponse k a b equation X := by
  program_unfold "applyT"
  program_unfold "scale"
  unfold sourceTableResponse
  rw [←average_sub]
  apply congrArg average
  rw [foldl_add,foldl_add,zero_add,zero_add,list_sum_sub,foldl_add,zero_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro term _
  change MvPolynomial.C (fun _ => term.coefficient)*
      (MvPolynomial.monomial term.exponent 1*(originalWord (k+1) (sourceEngine (k+1)) term.tokens X).getD (k+1) 0)-
    MvPolynomial.C (fun _ => term.coefficient)*
      (MvPolynomial.monomial term.exponent 1*(originalWord (k+1) (sourceEngine k) term.tokens X).getD (k+1) 0)=_
  rw [←mul_sub,←mul_sub,word_response]

end LowEnergy.PreparationVacuumEngineCancellation
