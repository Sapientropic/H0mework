import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationCentralArrays
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationDAGNormalized
import Mathlib.Data.Finsupp.Lex
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCentralBudget
open PreparationVacuumDAGCoefficient PreparationVacuumEngineBudget PreparationVacuumCanonicalMoyal
open PreparationVacuumClockSymbol PreparationVacuumClockJacobian PreparationVacuumEngineSmooth
open PreparationVacuumMoyalBudget
open scoped BigOperators ContDiff Topology

abbrev Exponent := CentralVariable →₀ ℕ
def sortedTerms (P : CentralPolynomial) : List Exponent :=
  ((P.support.image (fun e => toLex e)).sort (· ≥ ·)).map ofLex
def activeVariables (e : Exponent) : List CentralVariable := (List.finRange 7).filter (fun i => e i != 0)
def activePoles (e : PoleExponent) : List (Fin 3) := (List.finRange 3).filter (fun i => e i != 0)

def fieldFunction (i : CentralVariable) : RealSymbol := fun x => sourceVariables x i

def coefficientCeiling (c : ℚ) : ℝ := (⌈|c|⌉₊ : ℕ)

def termArray (B : CentralVariable → ArrayBound) (e : Exponent) (c : ℚ) : ArrayBound :=
  foldArray (fun i => powerArray (B i) (e i)) (activeVariables e) (constantArray (coefficientCeiling c))

def numeratorArray (B : CentralVariable → ArrayBound) (P : CentralPolynomial) (n : ℕ) : ℝ :=
  ((sortedTerms P).map (fun e => termArray B e (P.coeff e) n)).sum

def coefficientArray (B : CentralVariable → ArrayBound) (I : Fin 3 → ArrayBound)
    (c : NormalizedCoefficient) : ArrayBound :=
  foldArray (fun i => powerArray (I i) (c.poles i)) (activePoles c.poles) (numeratorArray B c.numerator)

theorem coefficientCeiling_nonnegative (c : ℚ) : 0 ≤ coefficientCeiling c := Nat.cast_nonneg _
theorem coefficientCeiling_bound (c : ℚ) : |(c : ℝ)| ≤ coefficientCeiling c := by
  unfold coefficientCeiling
  exact_mod_cast Nat.le_ceil (|c|)

theorem sortedTerms_sum (P : CentralPolynomial) (f : Exponent → ℝ) :
    ((sortedTerms P).map f).sum=∑ e∈P.support,f e := by
  let support : Finset (Lex Exponent) := P.support.image (fun e => toLex e)
  have sorted : ((support.sort (· ≥ ·)).map (fun e => f (ofLex e))).sum=
      ∑ e∈support,f (ofLex e) := by
    simpa using ((support.sort_perm_toList (· ≥ ·)).map (fun e => f (ofLex e))).sum_eq
  unfold sortedTerms
  rw [List.map_map]
  change ((support.sort (· ≥ ·)).map (fun e => f (ofLex e))).sum=_
  rw [sorted]
  dsimp only [support]
  rw [Finset.sum_image]
  · rfl
  · intro a _ b _ h
    exact congrArg ofLex h

theorem fieldFunction_smooth (i : CentralVariable) : SmoothSymbol (fieldFunction i) := by
  intro x hx
  fin_cases i
  · simpa [fieldFunction,sourceVariables] using! (actualC_smooth x hx.1).contDiffWithinAt
  · simpa [fieldFunction,sourceVariables] using! (actualT_smooth x hx.1.1).contDiffWithinAt
  · simpa [fieldFunction,sourceVariables] using! (actualS_smooth x hx.1.1 0 0).contDiffWithinAt
  · simpa [fieldFunction,sourceVariables] using! (actualS_smooth x hx.1.1 1 1).contDiffWithinAt
  · simpa [fieldFunction,sourceVariables] using! (actualS_smooth x hx.1.1 0 1).contDiffWithinAt
  · simpa [fieldFunction,sourceVariables] using! (actualS_smooth x hx.1.1 0 2).contDiffWithinAt
  · simpa [fieldFunction,sourceVariables] using! (actualS_smooth x hx.1.1 1 2).contDiffWithinAt

private theorem filtered_powers {k : ℕ} (e : Fin k → ℕ) (f : Fin k → ℝ) (xs : List (Fin k)) :
    ((xs.filter (fun i => e i != 0)).map (fun i => f i^e i)).prod=(xs.map (fun i => f i^e i)).prod := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    by_cases zero : e i=0
    · simp [zero,ih]
    · simp [zero,ih]

theorem field_power_product (e : Exponent) (x : SourcePhase) :
    ((activeVariables e).map (fun i => fieldFunction i x^e i)).prod=∏ i,sourceVariables x i^e i := by
  rw [activeVariables,filtered_powers,←List.ofFn_eq_map,List.prod_ofFn]
  rfl

theorem pole_power_product (e : PoleExponent) (x : SourcePhase) :
    ((activePoles e).map (fun i => ((poleFunction i x)⁻¹)^e i)).prod=(sourceDenominator e x)⁻¹ := by
  rw [activePoles,filtered_powers]
  rw [←List.ofFn_eq_map,List.prod_ofFn]
  simp only [sourceDenominator,inv_pow,Finset.prod_inv_distrib]

def termValue (e : Exponent) (c : ℚ) : RealSymbol :=
  foldValue (fun i => fieldFunction i^e i) (activeVariables e) (fun _ => (c : ℝ))

theorem termValue_native (e : Exponent) (c : ℚ) (x : SourcePhase) :
    termValue e c x=(c : ℝ)*∏ i,sourceVariables x i^e i := by
  rw [termValue,foldValue_native]
  simp only [Pi.pow_apply]
  rw [field_power_product]

theorem termValue_smooth (e : Exponent) (c : ℚ) : SmoothSymbol (termValue e c) :=
  foldValue_smooth _ (fun i => (fieldFunction_smooth i).pow (e i)) _ _ contDiffOn_const

theorem termArray_nonnegative (B : CentralVariable → ArrayBound) (positive : ∀ i n,0 ≤ B i n)
    (e : Exponent) (c : ℚ) (n : ℕ) : 0 ≤ termArray B e c n :=
  foldArray_nonnegative _ (fun i => powerArray_nonnegative (B i) (positive i) (e i)) _ _
    (constantArray_nonnegative _ (coefficientCeiling_nonnegative c)) n

theorem numeratorArray_nonnegative (B : CentralVariable → ArrayBound) (positive : ∀ i n,0 ≤ B i n)
    (P : CentralPolynomial) (n : ℕ) : 0 ≤ numeratorArray B P n := by
  rw [numeratorArray,sortedTerms_sum]
  exact Finset.sum_nonneg (fun e _ => termArray_nonnegative B positive e _ n)

theorem finite_term (B : CentralVariable → ArrayBound) (positive : ∀ i n,0 ≤ B i n)
    (N : ℕ) (x : SourcePhase) (hx : x∈poleDomain)
    (bounds : ∀ i,FiniteBound (fieldFunction i) N (B i) x) (e : Exponent) (c : ℚ) :
    FiniteBound (termValue e c) N (termArray B e c) x := by
  exact finite_fold _ (fun i => (fieldFunction_smooth i).pow (e i))
    (fun i => powerArray (B i) (e i)) (fun i => powerArray_nonnegative (B i) (positive i) (e i)) N x hx
    (fun i => finite_power (fieldFunction i) (fieldFunction_smooth i) (B i) (positive i) N x hx (bounds i) (e i))
    _ _ contDiffOn_const _ (constantArray_nonnegative _ (coefficientCeiling_nonnegative c))
    (finite_constant _ _ (coefficientCeiling_bound c) N x)

theorem polynomialSymbol_terms (P : CentralPolynomial) :
    polynomialSymbol P=fun x => ∑ e∈P.support,termValue e (P.coeff e) x := by
  funext x
  simp_rw [termValue_native]
  exact MvPolynomial.eval₂_eq' (Rat.castHom ℝ) (sourceVariables x) P

theorem polynomialSymbol_smooth (P : CentralPolynomial) : SmoothSymbol (polynomialSymbol P) := by
  rw [polynomialSymbol_terms]
  exact ContDiffOn.sum (fun e _ => termValue_smooth e _)

theorem finite_numerator (B : CentralVariable → ArrayBound) (positive : ∀ i n,0 ≤ B i n)
    (N : ℕ) (x : SourcePhase) (hx : x∈poleDomain)
    (bounds : ∀ i,FiniteBound (fieldFunction i) N (B i) x) (P : CentralPolynomial) :
    FiniteBound (polynomialSymbol P) N (numeratorArray B P) x := by
  intro m hm w
  rw [polynomialSymbol_terms,jet_sum poleDomain_open _ _ (fun e _ => termValue_smooth e _) m w x hx,
    numeratorArray,sortedTerms_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun e _ => finite_term B positive N x hx bounds e _ m hm w))

theorem inversePole_smooth (i : Fin 3) : SmoothSymbol (fun x => (poleFunction i x)⁻¹) := by
  intro x hx
  fin_cases i
  · exact ((actualC_smooth x hx.1).inv (poleFunction_nonzero x hx 0)).contDiffWithinAt
  · exact ((actualT_smooth x hx.1.1).inv (poleFunction_nonzero x hx 1)).contDiffWithinAt
  · exact ((sourceDet_smooth x hx.1.1).inv (poleFunction_nonzero x hx 2)).contDiffWithinAt

theorem coefficientValue_fold (c : NormalizedCoefficient) :
    coefficientValue c=foldValue (fun i => (fun x => (poleFunction i x)⁻¹)^c.poles i)
      (activePoles c.poles) (polynomialSymbol c.numerator) := by
  funext x
  rw [foldValue_native]
  simp only [Pi.pow_apply]
  rw [pole_power_product]
  simp only [coefficientValue,polynomialSymbol,div_eq_mul_inv]

/-- Direct normalized coefficient consumer; its three inverse inputs are generated in CentralCoefficients. -/
theorem finite_coefficient (B : CentralVariable → ArrayBound) (I : Fin 3 → ArrayBound)
    (positive : ∀ i n,0 ≤ B i n) (inversePositive : ∀ i n,0 ≤ I i n)
    (N : ℕ) (x : SourcePhase) (hx : x∈poleDomain)
    (bounds : ∀ i,FiniteBound (fieldFunction i) N (B i) x)
    (inverseBounds : ∀ i,FiniteBound (fun y => (poleFunction i y)⁻¹) N (I i) x)
    (c : NormalizedCoefficient) : FiniteBound (coefficientValue c) N (coefficientArray B I c) x := by
  rw [coefficientValue_fold]
  exact finite_fold _ (fun i => (inversePole_smooth i).pow (c.poles i))
    (fun i => powerArray (I i) (c.poles i)) (fun i => powerArray_nonnegative (I i) (inversePositive i) (c.poles i)) N x hx
    (fun i => finite_power _ (inversePole_smooth i) (I i) (inversePositive i) N x hx (inverseBounds i) (c.poles i))
    _ _ (polynomialSymbol_smooth c.numerator) _ (numeratorArray_nonnegative B positive _)
    (finite_numerator B positive N x hx bounds c.numerator)

end LowEnergy.PreparationVacuumCentralBudget
