import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79ImaginarySourceMap
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary

/-- The original two source-polynomial vectors, indexed directly by the
closed natural slot so source-field normalization does not depend on vector matching. -/
def polynomialLiteral (negative : Bool) (a : Fin 16) : ℂ :=
  match a.val with
  | 0 => 1
  | 2 => (Real.sqrt 2 : ℂ)
  | 5 => if negative then (-1 * Complex.I * (Real.sqrt 2 : ℂ)) else
      (Complex.I * (Real.sqrt 2 : ℂ))
  | 7 => if negative then ((3/25) * Complex.I * (Real.sqrt 15 : ℂ)) else
      ((-3/25) * Complex.I * (Real.sqrt 15 : ℂ))
  | 8 => if negative then ((-1/2) * Complex.I * (Real.sqrt 2 : ℂ)) else
      ((1/2) * Complex.I * (Real.sqrt 2 : ℂ))
  | 11 => if negative then ((-3/25) * Complex.I * (Real.sqrt 15 : ℂ)) else
      ((3/25) * Complex.I * (Real.sqrt 15 : ℂ))
  | 12 => ((3/25) * (Real.sqrt 15 : ℂ))
  | 13 => ((-1/2) * (Real.sqrt 2 : ℂ))
  | 14 => ((1/2) * (Real.sqrt 2 : ℂ))
  | 15 => ((-3/25) * (Real.sqrt 15 : ℂ))
  | _ => 0

theorem actual_source_polynomial_literal (negative : Bool) :
    sourcePolynomialPoint negative = polynomialLiteral negative := by
  funext a
  cases negative <;> fin_cases a <;> rfl

theorem source_polynomial_fourteen_literal (negative : Bool) :
    sourcePolynomialPoint negative 14 = (1/2 : ℂ)*(Real.sqrt 2 : ℂ) := by
  cases negative <;> rfl

theorem source_polynomial_fourteen (negative : Bool) :
    sourcePolynomialPoint negative 14 = (Real.sqrt 2 : ℂ)/2 := by
  rw [source_polynomial_fourteen_literal]
  ring

theorem source_polynomial_six (negative : Bool) :
    sourcePolynomialPoint negative 6 = 0 := by
  cases negative <;> rfl

end LowEnergy.ActualCanonical79Imaginary
