import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineWeights

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEngineSource
open PreparationVacuumCanonicalMoyal PreparationActualFactor PreparationScalarCoordinates
open SourceQuantumGaugeSliceCoordinates GaussNativeEnergy
open scoped BigOperators Matrix

abbrev ClockAt (k : ℕ) := Fin 4 → Fin (k+1) → Symbol

private def clockAt {k : ℕ} (clock : ClockAt k) (a : Fin 4) (j : ℕ) : Symbol :=
  if h : j<k+1 then clock a ⟨j,h⟩ else 0

private def clockPolynomial {k : ℕ} (clock : ClockAt k) (a : Fin 4) (j : ℕ) : AngularPolynomial :=
  MvPolynomial.C (clockAt clock a j)

private def ellPolynomial {k : ℕ} (clock : ClockAt k) (j : ℕ) : AngularPolynomial :=
  clockPolynomial clock 0 j+∑ a : Fin 3,MvPolynomial.X a*clockPolynomial clock (Fin.succ a) j

private def sourceSeries (slot : Fin 13) : List AngularPolynomial :=
  [MvPolynomial.C (engineSource 0 slot),MvPolynomial.C (engineSource 1 slot),MvPolynomial.C (engineSource 2 slot)]

private def traceSeries : List AngularPolynomial :=
  [MvPolynomial.C (engineTrace 0),MvPolynomial.C (engineTrace 1),MvPolynomial.C (engineTrace 2)]

private def scale (f : Symbol) (P : AngularPolynomial) : AngularPolynomial := MvPolynomial.C f*P

private def js {k : ℕ} (depth : ℕ) (clock : ClockAt k) (a : Fin 4)
    (X : List AngularPolynomial) : List AngularPolynomial :=
  List.ofFn (fun n : Fin (depth+1) =>
    ∑ i ∈ Finset.range (n.val+1),∑ j ∈ Finset.range (n.val+1-i),
      weighted (n.val-i-j) (clockPolynomial clock a i) (X.getD j 0))

private def resolventNext {k : ℕ} (clock : ClockAt k) (X : List AngularPolynomial)
    (answers : List AngularPolynomial) (n : ℕ) : AngularPolynomial :=
  scale (fun zp => (sourceClock zp)⁻¹)
    (X.getD n 0-∑ i ∈ Finset.range (n+1),∑ j ∈ Finset.range (n+1-i),
      if i=0 ∧ n-i-j=0 then 0
      else weighted (n-i-j) (ellPolynomial clock i) (answers.getD j 0))

private def resolvent {k : ℕ} (depth : ℕ) (clock : ClockAt k)
    (X : List AngularPolynomial) : List AngularPolynomial :=
  (List.range (depth+1)).foldl (fun answers n => answers++[resolventNext clock X answers n]) []

theorem resolvent_summand_earlier (n i j : ℕ) (hi : i≤n) (hj : j≤n-i)
    (nonleading : ¬ (i=0 ∧ n-i-j=0)) : j<n := by omega

private theorem appendedFold_length (indices : List ℕ) (f : List AngularPolynomial → ℕ → AngularPolynomial)
    (initial : List AngularPolynomial) :
    (indices.foldl (fun answers n => answers++[f answers n]) initial).length=initial.length+indices.length := by
  induction indices generalizing initial with
  | nil => simp
  | cons n indices ih =>
      rw [List.foldl_cons,ih]
      simp only [List.length_append,List.length_cons,List.length_nil]
      omega

theorem source_resolvent_length {k : ℕ} (depth : ℕ) (clock : ClockAt k) (X : List AngularPolynomial) :
    (resolvent depth clock X).length=depth+1 := by
  rw [resolvent,appendedFold_length]
  simp

inductive Token where
  | inverse
  | jordan (axis : Fin 4)

private def act {k : ℕ} (depth : ℕ) (clock : ClockAt k) (token : Token)
    (X : List AngularPolynomial) : List AngularPolynomial :=
  match token with
  | .inverse => resolvent depth clock X
  | .jordan a => js depth clock a X

private def word {k : ℕ} (depth : ℕ) (clock : ClockAt k) (tokens : List Token)
    (X : List AngularPolynomial) : List AngularPolynomial :=
  tokens.foldr (act depth clock) X

structure TableTerm where
  exponent : AngularExponent
  tokens : List Token
  coefficient : ℝ

private def energyTable (a b : Fin 4) : List TableTerm :=
  [⟨0,[.inverse,.jordan a,.inverse,.jordan b,.inverse],1⟩,
   ⟨0,[.inverse,.jordan b,.inverse,.jordan a,.inverse],1⟩]

private def derivativeExponent (a : Fin 4) : AngularExponent :=
  if h : a.val=0 then 0 else Finsupp.single ⟨a.val-1,by omega⟩ 1

private def differentiateTerm (a : Fin 4) (term : TableTerm) : List TableTerm :=
  term.tokens.zipIdx.flatMap (fun (token,j) =>
    match token with
    | .inverse => [⟨derivativeExponent a,
        term.tokens.take j++[.inverse,.inverse]++term.tokens.drop (j+1),term.coefficient⟩]
    | .jordan b => if b=a then
        [⟨0,term.tokens.take j++term.tokens.drop (j+1),-term.coefficient⟩]
      else [])

private def table (a b : Fin 4) (equation : Option (Fin 4)) : List TableTerm :=
  match equation with
  | none => energyTable a b
  | some e => (energyTable a b).flatMap (differentiateTerm e)

private def applyT {k : ℕ} (depth : ℕ) (clock : ClockAt k) (a b : Fin 4)
    (equation : Option (Fin 4)) (X : List AngularPolynomial) : Fin (depth+1) → Symbol :=
  fun n => average ((table a b equation).foldl (fun out term =>
    out+scale (fun _ => term.coefficient)
      (MvPolynomial.monomial term.exponent 1*(word depth clock term.tokens X).getD n.val 0)) 0)

private def affine {k : ℕ} (depth : ℕ) (clock : ClockAt k) (equation : Option (Fin 4))
    (n : Fin (depth+1)) : Symbol :=
  match equation with
  | none => ∑ a : Fin 4,MvPolynomial.coeff 0 ((js depth clock a (sourceSeries (Fin.castAdd 9 a))).getD n.val 0)
  | some a => -MvPolynomial.coeff 0 ((sourceSeries (Fin.castAdd 9 a)).getD n.val 0)

private def crossFirst : Fin 3 → Fin 3 := ![0,0,1]
private def crossSecond : Fin 3 → Fin 3 := ![1,2,2]
private def crossSlot : Fin 3 → Fin 13 := ![7,8,9]

def forceOrEnergy {k : ℕ} (depth : ℕ) (clock : ClockAt k) (equation : Option (Fin 4)) :
    Fin (depth+1) → Symbol := fun n =>
  affine depth clock equation n+
    (fun zp => (1/2 : ℝ)*applyT depth clock 0 0 equation traceSeries n zp)-
    (∑ i : Fin 3,fun zp => (1/2 : ℝ)*
      applyT depth clock (Fin.succ i) (Fin.succ i) equation
        (sourceSeries ⟨4+i.val,by omega⟩) n zp)-
    (∑ i : Fin 3,applyT depth clock (Fin.succ (crossFirst i)) (Fin.succ (crossSecond i)) equation
      (sourceSeries (crossSlot i)) n)-
    (∑ i : Fin 3,applyT depth clock 0 (Fin.succ i) equation
      (sourceSeries ⟨10+i.val,by omega⟩) n)

def principalForceJacobian (zp : Phase) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-sourceTrace zp/sourceClock zp^3,0,0,0;
    0,(S (nativePhase zp).1 (nativePhase zp).2 0 0-sourceTrace zp)/sourceClock zp^3,
      S (nativePhase zp).1 (nativePhase zp).2 0 1/sourceClock zp^3,
      S (nativePhase zp).1 (nativePhase zp).2 0 2/sourceClock zp^3;
    0,S (nativePhase zp).1 (nativePhase zp).2 1 0/sourceClock zp^3,
      (S (nativePhase zp).1 (nativePhase zp).2 1 1-sourceTrace zp)/sourceClock zp^3,
      S (nativePhase zp).1 (nativePhase zp).2 1 2/sourceClock zp^3;
    0,S (nativePhase zp).1 (nativePhase zp).2 2 0/sourceClock zp^3,
      S (nativePhase zp).1 (nativePhase zp).2 2 1/sourceClock zp^3,
      (S (nativePhase zp).1 (nativePhase zp).2 2 2-sourceTrace zp)/sourceClock zp^3]

private def generatedResidual {k : ℕ} (clock : ClockAt k) (a : Fin 4) : Symbol :=
  forceOrEnergy (k+1) clock (some a) (Fin.last (k+1))

private def generatedCorrection {k : ℕ} (clock : ClockAt k) (a : Fin 4) : Symbol :=
  fun zp => -∑ b : Fin 4,(principalForceJacobian zp)⁻¹ a b*generatedResidual clock b zp

private def nextClock {k : ℕ} (clock : ClockAt k) : ClockAt (k+1) := fun a j =>
  if h : j.val<k+1 then clock a ⟨j.val,h⟩ else generatedCorrection clock a

def sourceEngine (k : ℕ) : ClockAt k :=
  Nat.rec (motive:=ClockAt) (fun a _ => if a=0 then sourceClock else 0)
    (fun _ previous => nextClock previous) k

theorem sourceEngine_initial (a : Fin 4) : sourceEngine 0 a 0=if a=0 then sourceClock else 0 := rfl

theorem sourceEngine_preserves (k : ℕ) (a : Fin 4) (j : Fin (k+1)) :
    sourceEngine (k+1) a (Fin.castSucc j)=sourceEngine k a j := by
  simp only [sourceEngine,nextClock,Fin.val_castSucc,j.isLt,dif_pos]

theorem sourceEngine_generated (k : ℕ) (a : Fin 4) (zp : Phase) :
    sourceEngine (k+1) a (Fin.last (k+1)) zp=
      -∑ b : Fin 4,(principalForceJacobian zp)⁻¹ a b*
        forceOrEnergy (k+1) (sourceEngine k) (some b) (Fin.last (k+1)) zp := by
  simp only [sourceEngine,nextClock,Fin.val_last,lt_self_iff_false,dite_false,
    generatedCorrection,generatedResidual]

def sourceEngineEnergy (k : ℕ) : Symbol :=
  forceOrEnergy k (sourceEngine k) none (Fin.last k)

def sourceEngineForces (k : ℕ) : Fin 4 → Symbol :=
  fun a => forceOrEnergy k (sourceEngine k) (some a) (Fin.last k)

theorem sourceEngineEnergy_actual (k : ℕ) :
    sourceEngineEnergy k=forceOrEnergy k (sourceEngine k) none (Fin.last k) := rfl

end LowEnergy.PreparationVacuumEngineSource
