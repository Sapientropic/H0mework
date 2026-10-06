import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineLeading
import Mathlib.Data.List.GetD

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEngineIdentities
open PreparationVacuumEngineSource PreparationVacuumCanonicalMoyal
open scoped BigOperators

open Lean Elab Term in
elab "program_const%" name:str : term => do
  unless #["resolventNext","ellPolynomial","clockPolynomial","word","applyT","affine","scale"].contains name.getString do
    throwError "Not an original Engine program helper"
  let ns := Name.str (Name.str (Name.num `_private.H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineProgram 0) "LowEnergy") "PreparationVacuumEngineSource"
  Lean.Meta.mkConstWithFreshMVarLevels (Name.str ns name.getString)

open Lean Elab Tactic in
elab "program_unfold " name:str : tactic => do
  unless #["resolvent","resolventNext","ellPolynomial","clockPolynomial","clockAt","js","act","word","applyT","affine","scale"].contains name.getString do
    throwError "Not an original Engine program helper"
  let ns := Name.str (Name.str (Name.num `_private.H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineProgram 0) "LowEnergy") "PreparationVacuumEngineSource"
  let id := mkIdent (Name.str ns name.getString)
  evalTactic (← `(tactic| simp only [$id:ident]))

private abbrev originalR := engine_const% "resolvent"
private abbrev originalJ := engine_const% "js"
private abbrev originalClockAt := engine_const% "clockAt"
private abbrev originalAct := engine_const% "act"
private abbrev originalRNext := program_const% "resolventNext"
private abbrev originalEll := program_const% "ellPolynomial"
private abbrev originalClockPolynomial := program_const% "clockPolynomial"
private abbrev originalWord := program_const% "word"
private abbrev originalT := program_const% "applyT"
private abbrev originalAffine := program_const% "affine"

def ClockAgreement {k l : ℕ} (n : ℕ) (c : ClockAt k) (d : ClockAt l) : Prop :=
  ∀ a i, i≤n → originalClockAt c a i=originalClockAt d a i

private def SeriesAgreement (n : ℕ) (X Y : List AngularPolynomial) : Prop :=
  ∀ i, i≤n → X.getD i 0=Y.getD i 0

private theorem clockPolynomial_agreement {k l : ℕ} {n : ℕ} {c : ClockAt k} {d : ClockAt l}
    (h : ClockAgreement n c d) (a : Fin 4) (i : ℕ) (bound : i≤n) :
    originalClockPolynomial c a i=originalClockPolynomial d a i := by
  program_unfold "clockPolynomial"
  exact congrArg MvPolynomial.C (h a i bound)

private theorem ell_agreement {k l : ℕ} {n : ℕ} {c : ClockAt k} {d : ClockAt l}
    (h : ClockAgreement n c d) (i : ℕ) (bound : i≤n) : originalEll c i=originalEll d i := by
  program_unfold "ellPolynomial"
  simp only [clockPolynomial_agreement h _ i bound]

private theorem R_succ {k : ℕ} (n : ℕ) (c : ClockAt k) (X : List AngularPolynomial) :
    originalR (n+1) c X=originalR n c X++[originalRNext c X (originalR n c X) (n+1)] := by
  program_unfold "resolvent"
  rw [List.range_succ,List.foldl_append]
  rfl

private theorem R_agreement {k l : ℕ} (n : ℕ) (c : ClockAt k) (d : ClockAt l)
    (X Y : List AngularPolynomial) (hc : ClockAgreement n c d) (hx : SeriesAgreement n X Y) :
    originalR n c X=originalR n d Y := by
  induction n with
  | zero =>
    program_unfold "resolvent"
    simp only [Nat.zero_add,List.range_one,List.foldl_cons,List.foldl_nil,List.nil_append]
    apply congrArg List.singleton
    program_unfold "resolventNext"
    program_unfold "scale"
    simpa using congrArg (fun Z => MvPolynomial.C (fun zp => (sourceClock zp)⁻¹)*Z) (hx 0 (by omega))
  | succ n ih =>
    have prev := ih (fun a i hi => hc a i (by omega)) (fun i hi => hx i (by omega))
    rw [R_succ,R_succ,prev]
    apply congrArg (fun Z : AngularPolynomial => originalR n d Y++[Z])
    program_unfold "resolventNext"
    rw [hx (n+1) (by omega)]
    apply congrArg (fun Z : AngularPolynomial => MvPolynomial.C (fun zp => (sourceClock zp)⁻¹)*(Y.getD (n+1) 0-Z))
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have eq := ell_agreement hc i (by have := Finset.mem_range.mp hi; omega)
    exact congrArg (fun Z : AngularPolynomial => if i=0 ∧ n+1-i-j=0 then 0 else weighted (n+1-i-j) Z ((originalR n d Y).getD j 0)) eq

private theorem J_agreement {k l : ℕ} (n : ℕ) (c : ClockAt k) (d : ClockAt l)
    (a : Fin 4) (X Y : List AngularPolynomial)
    (hc : ClockAgreement n c d) (hx : SeriesAgreement n X Y) :
    originalJ n c a X=originalJ n d a Y := by
  program_unfold "js"
  apply congrArg List.ofFn
  funext m
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have bi : i≤n := by have := Finset.mem_range.mp hi; have := m.isLt; omega
  have bj : j≤n := by have := Finset.mem_range.mp hj; have := m.isLt; omega
  exact congrArg₂ (weighted (m.val-i-j)) (clockPolynomial_agreement hc a i bi) (hx j bj)

private theorem act_agreement {k l : ℕ} (n : ℕ) (c : ClockAt k) (d : ClockAt l)
    (token : Token) (X Y : List AngularPolynomial)
    (hc : ClockAgreement n c d) (hx : SeriesAgreement n X Y) :
    originalAct n c token X=originalAct n d token Y := by
  cases token with
  | inverse => exact R_agreement n c d X Y hc hx
  | jordan a => exact J_agreement n c d a X Y hc hx

private theorem word_agreement {k l : ℕ} (n : ℕ) (c : ClockAt k) (d : ClockAt l)
    (tokens : List Token) (X Y : List AngularPolynomial)
    (hc : ClockAgreement n c d) (hx : SeriesAgreement n X Y) :
    SeriesAgreement n (originalWord n c tokens X) (originalWord n d tokens Y) := by
  induction tokens with
  | nil => exact hx
  | cons token tokens ih =>
    program_unfold "word"
    simp only [List.foldr_cons]
    have eq := act_agreement n c d token _ _ hc ih
    exact fun _ _ => congrArg (fun Z : List AngularPolynomial => Z.getD _ 0) eq

private theorem foldl_functions_eq {α β : Type*} (xs : List α) (initial : β)
    (f g : β → α → β) (eq : ∀ out term, f out term=g out term) :
    xs.foldl f initial=xs.foldl g initial :=
  congrArg (fun F => xs.foldl F initial) (funext (fun out => funext (eq out)))

private theorem T_agreement {k l : ℕ} (n : ℕ) (c : ClockAt k) (d : ClockAt l)
    (a b : Fin 4) (equation : Option (Fin 4)) (X : List AngularPolynomial)
    (hc : ClockAgreement n c d) : originalT n c a b equation X=originalT n d a b equation X := by
  funext m
  program_unfold "applyT"
  apply congrArg average
  apply foldl_functions_eq
  intro out term
  have eq := word_agreement n c d term.tokens X X hc (fun _ _ => rfl) m.val (by omega)
  exact congrArg (fun Z => out+MvPolynomial.C (fun _ => term.coefficient)*(MvPolynomial.monomial term.exponent 1*Z)) eq

private theorem affine_agreement {k l : ℕ} (n : ℕ) (c : ClockAt k) (d : ClockAt l)
    (equation : Option (Fin 4)) (m : Fin (n+1)) (hc : ClockAgreement n c d) :
    originalAffine n c equation m=originalAffine n d equation m := by
  cases equation with
  | none =>
    program_unfold "affine"
    apply Finset.sum_congr rfl
    intro a _
    exact congrArg (fun X : List AngularPolynomial => MvPolynomial.coeff 0 (X.getD m.val 0)) (J_agreement n c d a _ _ hc (fun _ _ => rfl))
  | some a => rfl

theorem forceOrEnergy_clockAgreement {k l : ℕ} (n : ℕ) (c : ClockAt k) (d : ClockAt l)
    (hc : ClockAgreement n c d) (equation : Option (Fin 4)) :
    forceOrEnergy n c equation=forceOrEnergy n d equation := by
  funext m
  unfold forceOrEnergy
  simp only [affine_agreement n c d equation m hc,T_agreement n c d _ _ equation _ hc]

theorem sourceEngine_clockAgreement (k : ℕ) :
    ClockAgreement k (sourceEngine (k+1)) (sourceEngine k) := by
  intro a i hi
  program_unfold "clockAt"
  have left : i<k+1+1 := by omega
  have right : i<k+1 := by omega
  simp only [left,right,dif_pos]
  exact sourceEngine_preserves k a ⟨i,right⟩

theorem sourceEngine_paidFiltration (k : ℕ) (equation : Option (Fin 4)) :
    forceOrEnergy k (sourceEngine (k+1)) equation=forceOrEnergy k (sourceEngine k) equation :=
  forceOrEnergy_clockAgreement k _ _ (sourceEngine_clockAgreement k) equation

theorem sourceEngine_energyPreserved (k : ℕ) :
    forceOrEnergy k (sourceEngine (k+1)) none (Fin.last k)=sourceEngineEnergy k := by
  rw [sourceEngine_paidFiltration]
  rfl

theorem sourceEngine_forcesPreserved (k : ℕ) (a : Fin 4) :
    forceOrEnergy k (sourceEngine (k+1)) (some a) (Fin.last k)=sourceEngineForces k a := by
  rw [sourceEngine_paidFiltration]
  rfl

end LowEnergy.PreparationVacuumEngineIdentities
