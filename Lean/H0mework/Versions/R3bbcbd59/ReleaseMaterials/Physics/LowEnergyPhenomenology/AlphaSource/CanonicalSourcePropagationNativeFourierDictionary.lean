import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeGravityScalarReturn

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourcePropagationNativeActionHessian
open PreparationVacuumOriginalGreenFeedback
open scoped BigOperators

theorem nativeCoefficient_basis (a b : NativeJetIndex) :
    nativeCoefficientCLM a (nativeJetBasis b) = if a=b then 1 else 0 := by
  rcases a with ⟨d,i⟩
  rcases b with ⟨e,j⟩
  cases d <;> cases e <;>
    simp [nativeCoefficientCLM, nativeCoefficientLinear, nativeJetCoefficient,
      nativeJetBasis, Pi.single_apply, Prod.ext_iff, eq_comm, ite_and, ite_apply]

def nativeOrderedTermHessian (a b : NativeJetIndex) :
    NativeFirstJet →L[ℝ] NativeFirstJet →L[ℝ] ℝ :=
  (nativeCoefficientCLM a).smulRight (nativeCoefficientCLM b)

theorem nativeOrderedTermFourier (a b : NativeJetIndex) (p : Fin 4 → ℂ) :
    nativeFourierHessian (nativeOrderedTermHessian a b) p =
      Matrix.single a.2 b.2 (jetSymbol a.1 (-p)*jetSymbol b.1 p) := by
  rcases a with ⟨d,i⟩
  rcases b with ⟨e,j⟩
  ext row column
  change (∑ left : Option (Fin 4), ∑ right : Option (Fin 4),
    (((nativeCoefficientCLM (d,i) (nativeJetBasis (left,row))) *
      (nativeCoefficientCLM (e,j) (nativeJetBasis (right,column))) : ℝ) : ℂ) *
      jetSymbol left (-p) * jetSymbol right p) = _
  simp only [nativeCoefficient_basis]
  by_cases ri : i=row <;> by_cases cj : j=column <;>
    cases d <;> cases e <;>
    simp [Matrix.single_apply, Prod.ext_iff, ite_and, ri, cj, apply_ite, ite_mul, mul_ite]

def nativeLiteralHessian (terms : List (NativeJetIndex × NativeJetIndex × ℝ)) :
    NativeFirstJet →L[ℝ] NativeFirstJet →L[ℝ] ℝ :=
  (terms.map fun term => term.2.2 •
    (nativeOrderedTermHessian term.1 term.2.1 + nativeOrderedTermHessian term.2.1 term.1)).sum

def nativeLiteralFourier (terms : List (NativeJetIndex × NativeJetIndex × ℝ))
    (p : Fin 4 → ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  (terms.map fun term => Matrix.single term.1.2 term.2.1.2
      ((term.2.2:ℂ)*jetSymbol term.1.1 (-p)*jetSymbol term.2.1.1 p) +
    Matrix.single term.2.1.2 term.1.2
      ((term.2.2:ℂ)*jetSymbol term.2.1.1 (-p)*jetSymbol term.1.1 p)).sum

theorem nativeLiteralFourier_sound (terms : List (NativeJetIndex × NativeJetIndex × ℝ))
    (p : Fin 4 → ℂ) : nativeFourierHessian (nativeLiteralHessian terms) p =
      nativeLiteralFourier terms p := by
  induction terms with
  | nil =>
    change nativeFourierLinear p 0 = 0
    exact map_zero (nativeFourierLinear p)
  | cons term terms ih =>
    change nativeFourierLinear p
      (term.2.2 • (nativeOrderedTermHessian term.1 term.2.1 +
        nativeOrderedTermHessian term.2.1 term.1) + nativeLiteralHessian terms) = _
    rw [map_add, map_smul, map_add]
    change term.2.2 • (nativeFourierHessian (nativeOrderedTermHessian term.1 term.2.1) p +
      nativeFourierHessian (nativeOrderedTermHessian term.2.1 term.1) p) +
      nativeFourierHessian (nativeLiteralHessian terms) p = _
    rw [nativeOrderedTermFourier, nativeOrderedTermFourier, ih]
    simp only [nativeLiteralFourier, List.map_cons, List.sum_cons, smul_add,
      Matrix.smul_single, RCLike.real_smul_eq_coe_mul, mul_assoc]
    rfl


def nativeDerivativePower (d : Option (Fin 4)) : Powers :=
  match d with
  | none => ⟨0,0,0,0⟩
  | some mu => ⟨if mu=0 then 1 else 0, if mu=1 then 1 else 0,
    if mu=2 then 1 else 0, if mu=3 then 1 else 0⟩

def nativeDerivativeSign (d : Option (Fin 4)) : SourceCoefficient :=
  match d with
  | none => 1
  | some _ => -1

def nativeSourceOrderedTerm (a b : NativeJetIndex) (c : SourceCoefficient) : SourceTerm :=
  ⟨a.2,b.2,(nativeDerivativePower a.1).join (nativeDerivativePower b.1),nativeDerivativeSign a.1*c⟩

def nativeSourceQuadraticTerms (terms : List (NativeJetIndex × NativeJetIndex × SourceCoefficient)) :
    List SourceTerm := terms.flatMap fun term =>
      [nativeSourceOrderedTerm term.1 term.2.1 term.2.2,
       nativeSourceOrderedTerm term.2.1 term.1 term.2.2]

def nativeSourceRealTerms (terms : List (NativeJetIndex × NativeJetIndex × SourceCoefficient)) :
    List (NativeJetIndex × NativeJetIndex × ℝ) :=
  terms.map fun term => (term.1,term.2.1,(coefficientValue term.2.2).re)

theorem sourceCoefficient_real (c : SourceCoefficient) :
    ((coefficientValue c).re:ℂ) = coefficientValue c := by
  simp [coefficientValue, rootTwo, rootFifteen, Complex.mul_re, Complex.mul_im,
    Complex.ext_iff, Complex.ofReal_re, Complex.ofReal_im]

theorem nativeDerivativePower_value (d : Option (Fin 4)) (p : Fin 4 → ℂ) :
    (nativeDerivativePower d).value p = jetSymbol d p := by
  cases d with
  | none => simp [nativeDerivativePower, Powers.value, jetSymbol]
  | some mu => fin_cases mu <;> simp [nativeDerivativePower, Powers.value, jetSymbol]

theorem nativeDerivativeSign_value (d : Option (Fin 4)) (p : Fin 4 → ℂ) :
    coefficientValue (nativeDerivativeSign d)*jetSymbol d p = jetSymbol d (-p) := by
  cases d <;> simp [nativeDerivativeSign, coefficientValue, jetSymbol,
    QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem nativeSourceOrderedTerm_value (a b : NativeJetIndex) (c : SourceCoefficient)
    (p : Fin 4 → ℂ) :
    (nativeSourceOrderedTerm a b c).matrix p = Matrix.single a.2 b.2
      (coefficientValue c * jetSymbol a.1 (-p) * jetSymbol b.1 p) := by
  unfold nativeSourceOrderedTerm SourceTerm.matrix
  rw [coefficient_mul, Powers.value_join, nativeDerivativePower_value, nativeDerivativePower_value]
  congr 1
  calc
    coefficientValue (nativeDerivativeSign a.1)*coefficientValue c *
      (jetSymbol a.1 p*jetSymbol b.1 p) = coefficientValue c *
        (coefficientValue (nativeDerivativeSign a.1)*jetSymbol a.1 p)*jetSymbol b.1 p := by ring
    _ = _ := by rw [nativeDerivativeSign_value]

theorem nativeSourceFourier_sound (terms : List (NativeJetIndex × NativeJetIndex × SourceCoefficient))
    (p : Fin 4 → ℂ) :
    nativeFourierHessian (nativeLiteralHessian (nativeSourceRealTerms terms)) p =
      sourceMatrix (nativeSourceQuadraticTerms terms) p := by
  rw [nativeLiteralFourier_sound]
  induction terms with
  | nil => rfl
  | cons term terms ih =>
    simp only [nativeSourceRealTerms, nativeLiteralFourier, List.map_cons, List.map_map,
      List.sum_cons, Function.comp_apply] at ih ⊢
    rw [ih]
    simp only [nativeSourceQuadraticTerms, List.flatMap_cons, sourceMatrix_append,
      sourceMatrix_cons, sourceMatrix_nil, add_zero, nativeSourceOrderedTerm_value,
      sourceCoefficient_real]

end LowEnergy.SourcePropagationNativeActionHessian
