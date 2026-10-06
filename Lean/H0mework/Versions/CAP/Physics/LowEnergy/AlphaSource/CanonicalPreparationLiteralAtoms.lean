import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationLiteralFamilies

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLiteralAdmission
open PreparationVacuumCentralBudget PreparationVacuumPrincipalBudget PreparationVacuumLowerClassical
open PreparationVacuumLowerAssembly PreparationVacuumLowerCorrections PreparationVacuumLowerTensorBudget
open PreparationVacuumTimeReader PreparationVacuumCoframeBudget PreparationVacuumCanonicalMoyal
open PreparationVacuumClockSymbol PreparationVacuumEngineBudget
open scoped BigOperators

-- Exact OriginalRationalBounds profiles from the original coframe and matter matrices.
-- Each pair records (total numerator degree, original entrywise amplitude ceiling).
abbrev Profile := ℕ × List (ℕ × ℕ)
abbrev MatrixProfile := List (List (Fin 18 × ℕ))

def profiles : Fin 18 → Profile := ![(3,[(0,2)]),
  (3,[(1,1)]),
  (2,[(0,1)]),
  (3,[(0,1)]),
  (3,[(2,1),(2,1),(2,1)]),
  (3,[(2,1),(2,1)]),
  (1,[(0,1)]),
  (2,[(1,1)]),
  (0,[(0,1)]),
  (2,[(1,1),(1,1)]),
  (2,[(0,2)]),
  (3,[(1,2),(1,2)]),
  (0,[(2,1)]),
  (0,[(2,2)]),
  (0,[(2,2),(2,2)]),
  (0,[(2,1),(2,1)]),
  (0,[(2,3),(2,1),(2,1),(2,1)]),
  (0,[(2,2),(2,2),(2,2)])]

def oneBodyCorrectionRows : MatrixProfile := [[(0,1)]]

def WRows : MatrixProfile := [[],[(1,1),(2,1)],[(1,1),(2,1),(4,1),(5,2),(6,1),(7,2)],[(1,1),(2,1),(4,1),(5,2),(6,1),(7,3)],[(1,1),(2,1),(5,2),(6,1),(7,2)],[(1,1),(2,2),(3,1)],[(1,1),(5,3),(6,2),(7,1)],[(1,2),(2,2),(3,1)],[(1,2),(4,1),(5,1),(6,2),(7,2)],[(1,3),(2,2),(3,1)],[(2,1)],[(2,1),(5,3),(6,1),(7,2)],[(2,1),(6,1),(7,3)],[(2,1),(6,1),(7,4)],[(6,2),(7,4)]]

def inverseERows : MatrixProfile := [[(3,1)]]

def JRows : List MatrixProfile := [
  [[(8,1)]],
  [[(8,1)]],
  [[(8,1)]],
  [[(8,1)]],
  [[(8,1)]],
  [[(8,1)]],
  [[(6,1)]],
  [[(6,1)]],
  [[(6,1)]],
  [[(6,1)]],
  [[(6,1)]],
  [[(6,1)]],
  [[(9,1)]],
  [[(9,1)]],
  [[(9,1)]],
  [[(9,1)]],
  [[(9,1)]],
  [[(9,1)]],
  [[(4,1),(6,1)]],
  [[(4,1),(6,1)]],
  [[(4,1),(6,1)]],
  [[(4,1),(6,1)]],
  [[(4,1),(6,1)]],
  [[(4,1),(6,1)]]]

def MhRows : List MatrixProfile := [
  [[]],
  [[(10,1)]],
  [[]],
  [[(11,1)]],
  [[(10,1)]],
  [[]]]

def spatialPrincipalsRows : List MatrixProfile := [
  [[(12,1),(13,1)]],
  [[(14,1),(15,1)]],
  [[(16,1),(17,1)]]]

def numeratorNat (p : Profile) (m : ℕ) : ℕ :=
  (p.2.map (fun term => if m ≤ term.1 then
    term.2*(term.1.factorial/(term.1-m).factorial)*15^(term.1-m) else 0)).sum

def reciprocalNat (p : Profile) (m : ℕ) : ℕ := p.1.ascFactorial m*15^(p.1+m)

def profileNat (i : Fin 18) (m : ℕ) : ℕ :=
  ∑ r∈Finset.range (m+1),m.choose r*numeratorNat (profiles i) r*reciprocalNat (profiles i) (m-r)

def rowNat (row : List (Fin 18 × ℕ)) (m : ℕ) : ℕ :=
  (row.map (fun term => term.2*profileNat term.1 m)).sum

def matrixNat (rows : MatrixProfile) (m : ℕ) : ℕ :=
  rows.foldl (fun old row => max old (rowNat row m)) 0

def matrixArray (rows : MatrixProfile) (m : ℕ) : ℝ := matrixNat rows m

def matrixSumArray (rows : List MatrixProfile) (m : ℕ) : ℝ :=
  (rows.map (fun row => matrixNat row m)).sum

theorem matrixArray_nonnegative (rows : MatrixProfile) : Nonnegative (matrixArray rows) := fun _ => Nat.cast_nonneg _
theorem matrixSumArray_nonnegative (rows : List MatrixProfile) : Nonnegative (matrixSumArray rows) := fun _ => Nat.cast_nonneg _

def literalCoframeZero : ArrayBound := fun m =>
  2*504*matrixArray oneBodyCorrectionRows m+
    2*504*(504+1)*productArray (matrixArray WRows) (powerArray (matrixSumArray JRows) 2) m+
      originalCf0ScalarArray m

def literalCoframeFirst : ArrayBound := fun m =>
  504*productArray (affineArray 2 1) (matrixSumArray MhRows) m

def literalMatter : ArrayBound := fun m =>
  504*productArray (productArray (matrixArray inverseERows) (matrixSumArray spatialPrincipalsRows))
    (fun r => 12*AentryArray r) m

def literalY : ArrayBound := fun m => 504*1*35*literalPhi m*2

def literalZeroSample : ArrayBound := fun m =>
  literalScalarZero m+literalGaugeZero m+literalCoframeZero m+literalMatter m

def literalFirstSample : ArrayBound := fun m =>
  literalScalarFirst m+literalGaugeFirst m+literalCoframeFirst m

def literalZeroAtoms (j : Fin 14) : ArrayBound :=
  Fin.lastCases literalY (fun k m => (originalRowFactors k : ℝ)*literalZeroSample m) j

def literalFirstAtoms (j : Fin 14) : ArrayBound :=
  Fin.lastCases (fun _ => 0) (fun k m => (originalRowFactors k : ℝ)*literalFirstSample m) j

def literalLowerAtoms (d : Fin 2) (j : Fin 14) : ArrayBound :=
  Fin.cases (literalZeroAtoms j) (fun _ => literalFirstAtoms j) d

theorem profileNat_product (i : Fin 18) (m : ℕ) :
    (profileNat i m : ℝ)=productArray (fun k => (numeratorNat (profiles i) k : ℝ))
      (fun k => (reciprocalNat (profiles i) k : ℝ)) m := by
  simp only [profileNat,productArray,Nat.cast_sum,Nat.cast_mul]

theorem literalCoframeZero_nonnegative : Nonnegative literalCoframeZero := by
  have scalar (m : ℕ) : 0 ≤ originalCf0ScalarArray m := by
    unfold originalCf0ScalarArray
    positivity
  exact add_nonnegative _ _ (add_nonnegative _ _
    (scale_nonnegative (2*504 : ℝ) (by norm_num) _ (matrixArray_nonnegative _))
    (scale_nonnegative (2*504*(504+1) : ℝ) (by norm_num) _ (product_nonnegative _ _
      (matrixArray_nonnegative _) (power_nonnegative _ (matrixSumArray_nonnegative _) 2)))) scalar

theorem literalCoframeFirst_nonnegative : Nonnegative literalCoframeFirst :=
  scale_nonnegative 504 (by norm_num) _ (product_nonnegative _ _
    (affine_nonnegative 2 1 (by norm_num) (by norm_num)) (matrixSumArray_nonnegative _))

theorem literalMatter_nonnegative : Nonnegative literalMatter :=
  scale_nonnegative 504 (by norm_num) _ (product_nonnegative _ _
    (product_nonnegative _ _ (matrixArray_nonnegative _) (matrixSumArray_nonnegative _))
    (scale_nonnegative 12 (by norm_num) _ (affine_nonnegative 15 1 (by norm_num) (by norm_num))))

theorem literalY_nonnegative : Nonnegative literalY := by
  intro m
  exact mul_nonneg (mul_nonneg (by norm_num) (literalPhi_nonnegative m)) (by norm_num)

theorem literalZeroSample_nonnegative : Nonnegative literalZeroSample :=
  add_nonnegative _ _ (add_nonnegative _ _
    (add_nonnegative _ _ literalScalarZero_nonnegative literalGaugeZero_nonnegative)
    literalCoframeZero_nonnegative) literalMatter_nonnegative

theorem literalFirstSample_nonnegative : Nonnegative literalFirstSample :=
  add_nonnegative _ _ (add_nonnegative _ _ literalScalarFirst_nonnegative literalGaugeFirst_nonnegative)
    literalCoframeFirst_nonnegative

theorem literalCoframeZero_floor (m : ℕ) :
    6*volumeBudget m+(5/4 : ℝ)*inverseVolumeArray m ≤ literalCoframeZero m := by
  have one := matrixArray_nonnegative oneBodyCorrectionRows m
  have quadratic := product_nonnegative _ _ (matrixArray_nonnegative WRows)
    (power_nonnegative _ (matrixSumArray_nonnegative JRows) 2) m
  have inverse : (0 : ℝ) ≤ inverseVolumeArray m := Nat.cast_nonneg _
  unfold literalCoframeZero originalCf0ScalarArray volumeBudget
  norm_num
  nlinarith

theorem coframe_leaf_admission (j : Fin 13) (m : ℕ) :
    coframeCorrectionArray j m ≤ (originalRowFactors j : ℝ)*((5/4 : ℝ)*inverseVolumeArray m) := by
  by_cases zero : j=0
  · subst j
    have inverse : (0 : ℝ) ≤ inverseVolumeArray m := Nat.cast_nonneg _
    norm_num [coframeCorrectionArray,originalRowFactors]
    linarith
  · simp only [coframeCorrectionArray,zero,if_false]
    positivity

theorem zero_leaf_admission (j : Fin 14) : Dominates (zeroLeafArray j) (literalZeroAtoms j) := by
  induction j using Fin.lastCases with
  | last => exact literalY_nonnegative
  | cast j =>
    intro m
    simp only [zeroLeafArray,literalZeroAtoms,Fin.lastCases_castSucc]
    have core := mul_le_mul_of_nonneg_left (source_zero_core_admission m)
      (Nat.cast_nonneg (originalRowFactors j) : (0 : ℝ) ≤ originalRowFactors j)
    have cf := literalCoframeZero_floor m
    have matter := literalMatter_nonnegative m
    calc
      _ = (originalRowFactors j : ℝ)*(classicalSampleArray m+originalRhoDensityArray m+originalRhoWeylArray m)+
          coframeCorrectionArray j m := by
        unfold classicalLeafArray correctionArray originalHalfLeafArray originalQuarterLeafArray
        ring
      _ ≤ (originalRowFactors j : ℝ)*(literalScalarZero m+literalGaugeZero m+6*volumeBudget m)+
          (originalRowFactors j : ℝ)*((5/4 : ℝ)*inverseVolumeArray m) :=
        add_le_add core (coframe_leaf_admission j m)
      _ = (originalRowFactors j : ℝ)*(literalScalarZero m+literalGaugeZero m+
          (6*volumeBudget m+(5/4 : ℝ)*inverseVolumeArray m)) := by ring
      _ ≤ (originalRowFactors j : ℝ)*literalZeroSample m := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        unfold literalZeroSample
        linarith

theorem first_leaf_admission (j : Fin 14) : Dominates (firstLeafArray j) (literalFirstAtoms j) := by
  induction j using Fin.lastCases with
  | last => exact fun _ => le_rfl
  | cast j =>
    intro m
    simp only [firstLeafArray,literalFirstAtoms,Fin.lastCases_castSucc]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact (source_first_admission m).trans (le_add_of_nonneg_right (literalCoframeFirst_nonnegative m))

theorem literal_lower_nonnegative (d : Fin 2) (j : Fin 14) : Nonnegative (literalLowerAtoms d j) := by
  fin_cases d
  · induction j using Fin.lastCases with
    | last => exact literalY_nonnegative
    | cast j =>
      intro m
      simp only [literalLowerAtoms,literalZeroAtoms,Fin.lastCases_castSucc]
      exact mul_nonneg (Nat.cast_nonneg _) (literalZeroSample_nonnegative m)
  · induction j using Fin.lastCases with
    | last => exact fun _ => le_rfl
    | cast j =>
      intro m
      simp only [literalLowerAtoms,literalFirstAtoms,Fin.lastCases_castSucc]
      exact mul_nonneg (Nat.cast_nonneg _) (literalFirstSample_nonnegative m)

theorem lower_arrays_admitted (d : Fin 2) (j : Fin 14) :
    Dominates (lowerLeafArray d j) (literalLowerAtoms d j) := by
  fin_cases d
  · exact zero_leaf_admission j
  · exact first_leaf_admission j

theorem actual_literal_lower_budget (M : ℕ) (x : PreparationVacuumCanonicalMoyal.Phase)
    (hx : x∈poleDomain) (box : sourceBox x) (annulus : (∑ i : Fin 100,(x.2 i)^2) ≤ 4)
    (d : Fin 2) (j : Fin 14) :
    FiniteBound (originalLeaf (Fin.castSucc d) j) M (literalLowerAtoms d j) x :=
  finite_dominate _ _ _ M x (actual_lower_leaf_budget M x hx box annulus d j) (lower_arrays_admitted d j)

end LowEnergy.PreparationVacuumLiteralAdmission
