import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineResponseResolvent

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEngineResponse
open PreparationVacuumEngineSource PreparationVacuumEngineIdentities
open PreparationVacuumCanonicalMoyal
open scoped BigOperators

private abbrev originalR := engine_const% "resolvent"
private abbrev originalJ := engine_const% "js"
private abbrev originalAct := engine_const% "act"
private abbrev originalWord := program_const% "word"
private abbrev originalRNext := program_const% "resolventNext"

def sourceInversePolynomial : AngularPolynomial := MvPolynomial.C (fun zp => (sourceClock zp)⁻¹)

def sourceActZero (k : ℕ) (token : Token) (P : AngularPolynomial) : AngularPolynomial :=
  match token with
  | .inverse => sourceInversePolynomial*P
  | .jordan a => sourceClockCoefficient k a 0*P

def sourceActVariation (k : ℕ) (token : Token) (P delta : AngularPolynomial) : AngularPolynomial :=
  match token with
  | .inverse => sourceInversePolynomial*(delta-sourceNewestEll k*(sourceInversePolynomial*P))
  | .jordan a => sourceClockCoefficient k a 0*delta+sourceNewestPolynomial k a*P

def sourceWordPair (k : ℕ) (tokens : List Token) (P delta : AngularPolynomial) :
    AngularPolynomial×AngularPolynomial :=
  tokens.foldr (fun token result =>
    (sourceActZero k token result.1,sourceActVariation k token result.1 result.2)) (P,delta)

private theorem R_succ {l : ℕ} (n : ℕ) (c : ClockAt l) (X : List AngularPolynomial) :
    originalR (n+1) c X=originalR n c X++[originalRNext c X (originalR n c X) (n+1)] :=
  (filtration_const% "R_succ") n c X

private theorem R_stable {l : ℕ} (small big : ℕ) (bound : small≤big) (c : ClockAt l)
    (X : List AngularPolynomial) (i : ℕ) (hi : i ≤ small) :
    (originalR big c X).getD i 0=(originalR small c X).getD i 0 := by
  induction big,bound using Nat.le_induction with
  | base => rfl
  | succ big bound ih =>
    rw [R_succ,List.getD_append]
    · exact ih
    · rw [source_resolvent_length]
      omega

private theorem R_zero {l : ℕ} (c : ClockAt l) (X : List AngularPolynomial) :
    (originalR 0 c X).getD 0 0=sourceInversePolynomial*X.getD 0 0 := by
  program_unfold "resolvent"
  program_unfold "resolventNext"
  program_unfold "scale"
  simp [sourceInversePolynomial]

private theorem J_coefficient {l : ℕ} (depth : ℕ) (c : ClockAt l) (a : Fin 4)
    (X : List AngularPolynomial) (i : ℕ) (hi : i≤depth) :
    (originalJ depth c a X).getD i 0=
      ∑ r ∈ Finset.range (i+1),∑ j ∈ Finset.range (i+1-r),
        weighted (i-r-j) ((program_const% "clockPolynomial") c a r) (X.getD j 0) := by
  program_unfold "js"
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    show i<depth+1 by omega,dif_pos,Option.getD_some]

private theorem act_zero (k depth : ℕ) (token : Token) (X : List AngularPolynomial) :
    (originalAct depth (sourceEngine k) token X).getD 0 0=sourceActZero k token (X.getD 0 0) := by
  cases token with
  | inverse =>
    change (originalR depth (sourceEngine k) X).getD 0 0=_
    rw [R_stable 0 depth (by omega) _ X 0 (by omega),R_zero]
    rfl
  | jordan a =>
    change (originalJ depth (sourceEngine k) a X).getD 0 0=_
    rw [J_coefficient depth _ a X 0 (by omega)]
    program_unfold "clockPolynomial"
    change (∑ r ∈ Finset.range 1,∑ j ∈ Finset.range (1-r),
      weighted (0-r-j) (sourceClockCoefficient k a r) (X.getD j 0))=_
    simp [sourceActZero,weighted_zero]

private theorem act_lower (k : ℕ) (token : Token) (X Y : List AngularPolynomial)
    (lower : ∀ j, j≤k → X.getD j 0=Y.getD j 0) :
    ∀ i, i≤k → (originalAct (k+1) (sourceEngine (k+1)) token X).getD i 0=
      (originalAct (k+1) (sourceEngine k) token Y).getD i 0 := by
  intro i hi
  cases token with
  | inverse =>
    change (originalR (k+1) (sourceEngine (k+1)) X).getD i 0=
      (originalR (k+1) (sourceEngine k) Y).getD i 0
    rw [R_stable k (k+1) (by omega) _ X i hi,R_stable k (k+1) (by omega) _ Y i hi]
    have eq := (filtration_const% "R_agreement") k (sourceEngine (k+1)) (sourceEngine k)
      X Y (sourceEngine_clockAgreement k) lower
    exact congrArg (fun Z : List AngularPolynomial => Z.getD i 0) eq
  | jordan a =>
    change (originalJ (k+1) (sourceEngine (k+1)) a X).getD i 0=
      (originalJ (k+1) (sourceEngine k) a Y).getD i 0
    rw [J_coefficient _ _ _ X i (by omega),J_coefficient _ _ _ Y i (by omega)]
    program_unfold "clockPolynomial"
    change (∑ r ∈ Finset.range (i+1),∑ j ∈ Finset.range (i+1-r),
      weighted (i-r-j) (sourceClockCoefficient (k+1) a r) (X.getD j 0))=
      (∑ r ∈ Finset.range (i+1),∑ j ∈ Finset.range (i+1-r),
      weighted (i-r-j) (sourceClockCoefficient k a r) (Y.getD j 0))
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro j hj
    rw [sourceClockCoefficient_preserves k a r (by have := Finset.mem_range.mp hr; omega),
      lower j (by have := Finset.mem_range.mp hj; omega)]

private theorem word_lower (k : ℕ) (tokens : List Token) (X Y : List AngularPolynomial)
    (lower : ∀ j, j≤k → X.getD j 0=Y.getD j 0) :
    ∀ i, i≤k → (originalWord (k+1) (sourceEngine (k+1)) tokens X).getD i 0=
      (originalWord (k+1) (sourceEngine k) tokens Y).getD i 0 := by
  induction tokens with
  | nil => exact lower
  | cons token tokens ih =>
    program_unfold "word"
    simp only [List.foldr_cons]
    exact act_lower k token _ _ ih

private theorem act_newest (k : ℕ) (token : Token) (X Y : List AngularPolynomial)
    (lower : ∀ j, j≤k → X.getD j 0=Y.getD j 0) :
    (originalAct (k+1) (sourceEngine (k+1)) token X).getD (k+1) 0-
      (originalAct (k+1) (sourceEngine k) token Y).getD (k+1) 0=
      sourceActVariation k token (Y.getD 0 0) (X.getD (k+1) 0-Y.getD (k+1) 0) := by
  cases token with
  | inverse =>
    have response := sourceResolvent_newest k X Y lower
    change (originalR (k+1) (sourceEngine (k+1)) X).getD (k+1) 0-
      (originalR (k+1) (sourceEngine k) Y).getD (k+1) 0=
      sourceInversePolynomial*(X.getD (k+1) 0-Y.getD (k+1) 0-
        sourceNewestEll k*(originalR k (sourceEngine k) Y).getD 0 0) at response
    rw [R_stable 0 k (by omega) _ Y 0 (by omega),R_zero] at response
    exact response
  | jordan a => exact sourceJordan_newest k a X Y lower

theorem sourceWord_newest (k : ℕ) (tokens : List Token) (X Y : List AngularPolynomial)
    (lower : ∀ j, j≤k → X.getD j 0=Y.getD j 0) :
    (originalWord (k+1) (sourceEngine k) tokens Y).getD 0 0=
        (sourceWordPair k tokens (Y.getD 0 0) (X.getD (k+1) 0-Y.getD (k+1) 0)).1 ∧
    (originalWord (k+1) (sourceEngine (k+1)) tokens X).getD (k+1) 0-
      (originalWord (k+1) (sourceEngine k) tokens Y).getD (k+1) 0=
        (sourceWordPair k tokens (Y.getD 0 0) (X.getD (k+1) 0-Y.getD (k+1) 0)).2 := by
  induction tokens with
  | nil => exact ⟨rfl,rfl⟩
  | cons token tokens ih =>
    change (originalAct (k+1) (sourceEngine k) token (originalWord (k+1) (sourceEngine k) tokens Y)).getD 0 0=
      sourceActZero k token (sourceWordPair k tokens (Y.getD 0 0) (X.getD (k+1) 0-Y.getD (k+1) 0)).1 ∧
      (originalAct (k+1) (sourceEngine (k+1)) token (originalWord (k+1) (sourceEngine (k+1)) tokens X)).getD (k+1) 0-
        (originalAct (k+1) (sourceEngine k) token (originalWord (k+1) (sourceEngine k) tokens Y)).getD (k+1) 0=
      sourceActVariation k token (sourceWordPair k tokens (Y.getD 0 0) (X.getD (k+1) 0-Y.getD (k+1) 0)).1
        (sourceWordPair k tokens (Y.getD 0 0) (X.getD (k+1) 0-Y.getD (k+1) 0)).2
    constructor
    · exact (act_zero k (k+1) token _).trans (congrArg (sourceActZero k token) ih.1)
    · exact (act_newest k token _ _ (word_lower k tokens X Y lower)).trans
        (congrArg₂ (sourceActVariation k token) ih.1 ih.2)

end LowEnergy.PreparationVacuumEngineResponse
