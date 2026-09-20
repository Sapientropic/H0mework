import H0mework.Physics.LowEnergyMatterSpace.SpatialCARAlgebra

/-! Every finite word is evaluated on the same original one-particle Fock state.
Its exact recursive expression depends only on spatial Gram entries. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.SpatialCAR
open QuantizationCheck.Fermion Fermion
noncomputable section
variable {α m : Type*} [Fintype m] [LinearOrder m]

inductive Letter (α : Type*)
  | create : α → Letter α
  | annihilate : α → Letter α

inductive ExteriorExpression (α : Type*)
  | ket : List α → ExteriorExpression α
  | add : ExteriorExpression α → ExteriorExpression α → ExteriorExpression α
  | scale : ℂ → ExteriorExpression α → ExteriorExpression α

def exteriorKet (coordinates : α → m → ℂ) : List α → Fock m
  | [] => vacuum
  | i::rest => waveCreation (coordinates i) (exteriorKet coordinates rest)

def interpretation (coordinates : α → m → ℂ) : ExteriorExpression α → Fock m
  | .ket occupied => exteriorKet coordinates occupied
  | .add first second => interpretation coordinates first+interpretation coordinates second
  | .scale c expression => c • interpretation coordinates expression

def createExpression (i : α) : ExteriorExpression α → ExteriorExpression α
  | .ket occupied => .ket (i::occupied)
  | .add first second => .add (createExpression i first) (createExpression i second)
  | .scale c expression => .scale c (createExpression i expression)

def contractKet (gram : α → α → ℂ) (i : α) : List α → ExteriorExpression α
  | [] => .scale 0 (.ket [])
  | j::rest => .add (.scale (gram i j) (.ket rest))
      (.scale (-1) (createExpression j (contractKet gram i rest)))

def annihilateExpression (gram : α → α → ℂ) (i : α) : ExteriorExpression α → ExteriorExpression α
  | .ket occupied => contractKet gram i occupied
  | .add first second => .add (annihilateExpression gram i first) (annihilateExpression gram i second)
  | .scale c expression => .scale c (annihilateExpression gram i expression)

def letterExpression (gram : α → α → ℂ) : Letter α → ExteriorExpression α → ExteriorExpression α
  | .create i => createExpression i
  | .annihilate i => annihilateExpression gram i

def letterOperator (coordinates : α → m → ℂ) : Letter α → Module.End ℂ (Fock m)
  | .create i => waveCreation (coordinates i)
  | .annihilate i => annihilator (coordinates i)

def wordOperator (coordinates : α → m → ℂ) : List (Letter α) → Module.End ℂ (Fock m)
  | [] => 1
  | letter::rest => letterOperator coordinates letter * wordOperator coordinates rest

def wordExpression (gram : α → α → ℂ) (source : α) : List (Letter α) → ExteriorExpression α
  | [] => .ket [source]
  | letter::rest => letterExpression gram letter (wordExpression gram source rest)

def expressionEvaluation (gram : α → α → ℂ) (source : α) : ExteriorExpression α → ℂ
  | .ket [i] => gram source i
  | .ket _ => 0
  | .add first second => expressionEvaluation gram source first+expressionEvaluation gram source second
  | .scale c expression => c*expressionEvaluation gram source expression

theorem interpretation_create (coordinates : α → m → ℂ) (i : α) (expression : ExteriorExpression α) :
    interpretation coordinates (createExpression i expression)=
      waveCreation (coordinates i) (interpretation coordinates expression) := by
  induction expression with
  | ket occupied => rfl
  | add first second ihFirst ihSecond =>
    simp only [createExpression,interpretation,map_add,ihFirst,ihSecond]
  | scale c expression ih => simp only [createExpression,interpretation,map_smul,ih]

theorem interpretation_contract (coordinates : α → m → ℂ) (gram : α → α → ℂ)
    (sameGram : ∀ i j, modePair (coordinates i) (coordinates j)=gram i j) (i : α) (occupied : List α) :
    interpretation coordinates (contractKet gram i occupied)=
      annihilator (coordinates i) (exteriorKet coordinates occupied) := by
  induction occupied with
  | nil => simp only [contractKet,interpretation,exteriorKet,zero_smul,annihilator_vacuum]
  | cons j rest ih =>
    simp only [contractKet,interpretation,interpretation_create,ih,exteriorKet,
      annihilator_wave,sameGram,neg_smul,one_smul,sub_eq_add_neg]

theorem interpretation_annihilate (coordinates : α → m → ℂ) (gram : α → α → ℂ)
    (sameGram : ∀ i j, modePair (coordinates i) (coordinates j)=gram i j) (i : α)
    (expression : ExteriorExpression α) :
    interpretation coordinates (annihilateExpression gram i expression)=
      annihilator (coordinates i) (interpretation coordinates expression) := by
  induction expression with
  | ket occupied => exact interpretation_contract coordinates gram sameGram i occupied
  | add first second ihFirst ihSecond =>
    simp only [annihilateExpression,interpretation,map_add,ihFirst,ihSecond]
  | scale c expression ih => simp only [annihilateExpression,interpretation,map_smul,ih]

theorem interpretation_letter (coordinates : α → m → ℂ) (gram : α → α → ℂ)
    (sameGram : ∀ i j, modePair (coordinates i) (coordinates j)=gram i j) (letter : Letter α)
    (expression : ExteriorExpression α) :
    interpretation coordinates (letterExpression gram letter expression)=
      letterOperator coordinates letter (interpretation coordinates expression) := by
  cases letter with
  | create i => exact interpretation_create coordinates i expression
  | annihilate i => exact interpretation_annihilate coordinates gram sameGram i expression

theorem interpretation_word (coordinates : α → m → ℂ) (gram : α → α → ℂ)
    (sameGram : ∀ i j, modePair (coordinates i) (coordinates j)=gram i j)
    (source : α) (word : List (Letter α)) :
    interpretation coordinates (wordExpression gram source word)=
      wordOperator coordinates word (oneParticle (coordinates source)) := by
  induction word with
  | nil => simp only [wordExpression,interpretation,exteriorKet,waveCreation_vacuum,
      wordOperator,Module.End.one_apply]
  | cons letter rest ih =>
    rw [wordExpression,interpretation_letter coordinates gram sameGram,ih,
      wordOperator,Module.End.mul_apply]

omit [LinearOrder m] in
theorem pairing_add_right (ψ φ χ : Fock m) : pairing ψ (φ+χ)=pairing ψ φ+pairing ψ χ := by
  simp only [pairing,Pi.add_apply,mul_add,Finset.sum_add_distrib]

theorem pairing_exteriorKet (coordinates : α → m → ℂ) (gram : α → α → ℂ)
    (sameGram : ∀ i j, modePair (coordinates i) (coordinates j)=gram i j)
    (source : α) (occupied : List α) :
    pairing (oneParticle (coordinates source)) (exteriorKet coordinates occupied)=
      expressionEvaluation gram source (.ket occupied) := by
  cases occupied with
  | nil => simp [exteriorKet,expressionEvaluation,pairing_oneParticle_left,vacuum,occupationBasis]
  | cons i rest =>
    rw [exteriorKet,pairing_oneParticle_wave,sameGram]
    cases rest with
    | nil => simp [exteriorKet,expressionEvaluation,vacuum,occupationBasis]
    | cons j rest => simp only [exteriorKet,wave_empty,mul_zero,expressionEvaluation]

theorem pairing_interpretation (coordinates : α → m → ℂ) (gram : α → α → ℂ)
    (sameGram : ∀ i j, modePair (coordinates i) (coordinates j)=gram i j)
    (source : α) (expression : ExteriorExpression α) :
    pairing (oneParticle (coordinates source)) (interpretation coordinates expression)=
      expressionEvaluation gram source expression := by
  induction expression with
  | ket occupied => exact pairing_exteriorKet coordinates gram sameGram source occupied
  | add first second ihFirst ihSecond =>
    simp only [interpretation,pairing_add_right,ihFirst,ihSecond,expressionEvaluation]
  | scale c expression ih => simp only [interpretation,pairing_smul_right,ih,expressionEvaluation]

theorem allWord_gram_evaluation (coordinates : α → m → ℂ) (gram : α → α → ℂ)
    (sameGram : ∀ i j, modePair (coordinates i) (coordinates j)=gram i j)
    (source : α) (word : List (Letter α)) :
    pairing (oneParticle (coordinates source))
      (wordOperator coordinates word (oneParticle (coordinates source)))=
      expressionEvaluation gram source (wordExpression gram source word) := by
  rw [← interpretation_word coordinates gram sameGram source word]
  exact pairing_interpretation coordinates gram sameGram source _

theorem allWord_embedding_invariant {n : Type*} [Fintype n] [LinearOrder n]
    (first : α → m → ℂ) (second : α → n → ℂ)
    (preserved : ∀ i j, modePair (first i) (first j)=modePair (second i) (second j))
    (source : α) (word : List (Letter α)) :
    pairing (oneParticle (first source)) (wordOperator first word (oneParticle (first source)))=
      pairing (oneParticle (second source)) (wordOperator second word (oneParticle (second source))) := by
  rw [allWord_gram_evaluation first (fun i j => modePair (second i) (second j)) preserved,
    allWord_gram_evaluation second (fun i j => modePair (second i) (second j)) (fun _ _ => rfl)]

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.SpatialCAR
