import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationLiteralStages

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLiteralRows
open PreparationVacuumDAGCoefficient PreparationVacuumDAGSemantic PreparationVacuumArenaCollect
open PreparationVacuumClockSymbol PreparationVacuumArenaRows
abbrev Phase := PreparationVacuumCanonicalMoyal.Phase

def scalarRow (k : ℕ) (c : ℝ) : Row k := by
  classical
  exact if rational : ∃ q : ℚ,(q : ℝ)=c then
    ⟨polynomialCoefficient (MvPolynomial.C (Classical.choose rational)),[]⟩ else
    atomRow (.literal c)

theorem scalarRow_value (k : ℕ) (c : ℝ) (x : Phase) : rowValue (scalarRow k c) x=(c : ℂ) := by
  classical
  unfold scalarRow
  split_ifs with rational
  · have value : ((Classical.choose rational : ℚ) : ℝ)=c := Classical.choose_spec rational
    simp only [rowValue,List.map_nil,orderedProduct,List.foldr_nil,mul_one]
    simpa [polynomialCoefficient_source,polynomialSymbol,evalAt] using congrArg Complex.ofReal value
  · exact atomRow_value (.literal c) x

theorem scalarRow_rational (k : ℕ) (q : ℚ) :
    scalarRow k (q : ℝ)=⟨polynomialCoefficient (MvPolynomial.C q),[]⟩ := by
  classical
  have rational : ∃ r : ℚ,(r : ℝ)=(q : ℝ) := ⟨q,rfl⟩
  have value : Classical.choose rational=q := by
    exact_mod_cast Classical.choose_spec rational
  simp only [scalarRow,dif_pos rational,value]

theorem scalarRow_irrational (k : ℕ) (c : ℝ) (nonrational : ¬∃ q : ℚ,(q : ℝ)=c) :
    scalarRow k c=atomRow (.literal c) := by
  classical
  simp only [scalarRow,dif_neg nonrational]

theorem scalarRow_zero (k : ℕ) : scalarRow k 0=⟨polynomialCoefficient 0,[]⟩ := by
  simpa using scalarRow_rational k 0

theorem scalarRow_one (k : ℕ) : scalarRow k 1=⟨polynomialCoefficient 1,[]⟩ := by
  simpa using scalarRow_rational k 1

end LowEnergy.PreparationVacuumLiteralRows
