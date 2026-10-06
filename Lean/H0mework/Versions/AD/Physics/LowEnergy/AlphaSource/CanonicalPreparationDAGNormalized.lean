import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationDAGFields

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumDAGCoefficient
open PreparationVacuumClockSymbol PreparationVacuumClockJacobian PreparationVacuumEngineBudget
open scoped BigOperators

abbrev PoleExponent := Fin 3 → ℕ

def denominatorPolynomial (e : PoleExponent) : CentralPolynomial := ∏ i : Fin 3,polePolynomial i^e i
def sourceDenominator (e : PoleExponent) (x : SourcePhase) : ℝ := ∏ i : Fin 3,poleFunction i x^e i

theorem denominatorPolynomial_source (e : PoleExponent) (x : SourcePhase) :
    evalAt x (denominatorPolynomial e)=sourceDenominator e x := by
  simp only [denominatorPolynomial,sourceDenominator,map_prod,map_pow,polePolynomial_source]

theorem sourceDenominator_nonzero (e : PoleExponent) (x : SourcePhase) (hx : x∈poleDomain) :
    sourceDenominator e x≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (poleFunction_nonzero x hx i))

theorem sourceDenominator_add (e f : PoleExponent) (x : SourcePhase) :
    sourceDenominator (e+f) x=sourceDenominator e x*sourceDenominator f x := by
  simp only [sourceDenominator,Pi.add_apply,pow_add,Finset.prod_mul_distrib]

theorem sourceDenominator_factor (e d : PoleExponent) (h : ∀ i,e i≤d i) (x : SourcePhase) :
    sourceDenominator d x=sourceDenominator e x*sourceDenominator (d-e) x := by
  have split : e+(d-e)=d := by funext i; exact Nat.add_sub_of_le (h i)
  rw [←sourceDenominator_add,split]

structure NormalizedCoefficient where
  numerator : CentralPolynomial
  poles : PoleExponent

def coefficientValue (c : NormalizedCoefficient) : RealSymbol :=
  fun x => evalAt x c.numerator/sourceDenominator c.poles x

theorem coefficientValue_denominator (c : NormalizedCoefficient) (x : SourcePhase) :
    coefficientValue c x=evalAt x c.numerator/
      (actualC x^c.poles 0*actualT x^c.poles 1*sourceDet x^c.poles 2) := by
  simp [coefficientValue,sourceDenominator,Fin.prod_univ_three,poleFunction]

def polynomialCoefficient (P : CentralPolynomial) : NormalizedCoefficient := ⟨P,0⟩
def inversePoleCoefficient (i : Fin 3) : NormalizedCoefficient := ⟨1,Pi.single i 1⟩
def negateCoefficient (c : NormalizedCoefficient) : NormalizedCoefficient := ⟨-c.numerator,c.poles⟩
def multiplyCoefficient (c d : NormalizedCoefficient) : NormalizedCoefficient :=
  ⟨c.numerator*d.numerator,c.poles+d.poles⟩

def commonExponent (c d : NormalizedCoefficient) : PoleExponent := fun i => max (c.poles i) (d.poles i)
def addCoefficient (c d : NormalizedCoefficient) : NormalizedCoefficient :=
  ⟨c.numerator*denominatorPolynomial (commonExponent c d-c.poles)+
    d.numerator*denominatorPolynomial (commonExponent c d-d.poles),commonExponent c d⟩

theorem polynomialCoefficient_source (P : CentralPolynomial) (x : SourcePhase) :
    coefficientValue (polynomialCoefficient P) x=polynomialSymbol P x := by
  simp [coefficientValue,polynomialCoefficient,sourceDenominator,polynomialSymbol]

theorem inversePoleCoefficient_source (i : Fin 3) (x : SourcePhase) :
    coefficientValue (inversePoleCoefficient i) x=(poleFunction i x)⁻¹ := by
  simp [coefficientValue,inversePoleCoefficient,sourceDenominator,Pi.single_apply]

theorem negateCoefficient_source (c : NormalizedCoefficient) (x : SourcePhase) :
    coefficientValue (negateCoefficient c) x= -coefficientValue c x := by
  simp only [coefficientValue,negateCoefficient,map_neg,neg_div]

theorem multiplyCoefficient_source (c d : NormalizedCoefficient) (x : SourcePhase) :
    coefficientValue (multiplyCoefficient c d) x=coefficientValue c x*coefficientValue d x := by
  simp only [coefficientValue,multiplyCoefficient,map_mul,sourceDenominator_add,div_mul_div_comm]

theorem addCoefficient_source (c d : NormalizedCoefficient) (x : SourcePhase) (hx : x∈poleDomain) :
    coefficientValue (addCoefficient c d) x=coefficientValue c x+coefficientValue d x := by
  have left := sourceDenominator_factor c.poles (commonExponent c d) (fun _ => le_max_left _ _) x
  have right := sourceDenominator_factor d.poles (commonExponent c d) (fun _ => le_max_right _ _) x
  simp only [coefficientValue,addCoefficient,map_add,map_mul,denominatorPolynomial_source,add_div]
  congr 1
  · rw [left]
    field_simp [sourceDenominator_nonzero c.poles x hx,
      sourceDenominator_nonzero (commonExponent c d-c.poles) x hx]
  · rw [right]
    field_simp [sourceDenominator_nonzero d.poles x hx,
      sourceDenominator_nonzero (commonExponent c d-d.poles) x hx]

-- This grammar is the source arena's coefficient algebra before its cancel pass.
-- Inversion is restricted to its three generated source poles; no normal-form witness is input.
inductive CentralExpression where
  | polynomial (P : CentralPolynomial)
  | inversePole (i : Fin 3)
  | neg (e : CentralExpression)
  | add (e f : CentralExpression)
  | mul (e f : CentralExpression)

def expressionValue : CentralExpression → RealSymbol :=
  CentralExpression.rec (motive:=fun _ => RealSymbol) polynomialSymbol
    (fun i x => (poleFunction i x)⁻¹) (fun _ f x => -f x)
    (fun _ _ f g x => f x+g x) (fun _ _ f g x => f x*g x)

def normalize : CentralExpression → NormalizedCoefficient :=
  CentralExpression.rec (motive:=fun _ => NormalizedCoefficient)
    polynomialCoefficient inversePoleCoefficient (fun _ c => negateCoefficient c)
    (fun _ _ c d => addCoefficient c d) (fun _ _ c d => multiplyCoefficient c d)

theorem normalize_source (e : CentralExpression) (x : SourcePhase) (hx : x∈poleDomain) :
    coefficientValue (normalize e) x=expressionValue e x := by
  induction e with
  | polynomial P => exact polynomialCoefficient_source P x
  | inversePole i => exact inversePoleCoefficient_source i x
  | neg e ih =>
    change coefficientValue (negateCoefficient (normalize e)) x= -expressionValue e x
    rw [negateCoefficient_source,ih]
  | add e f left right =>
    change coefficientValue (addCoefficient (normalize e) (normalize f)) x=expressionValue e x+expressionValue f x
    rw [addCoefficient_source _ _ x hx,left,right]
  | mul e f left right =>
    change coefficientValue (multiplyCoefficient (normalize e) (normalize f)) x=expressionValue e x*expressionValue f x
    rw [multiplyCoefficient_source,left,right]

end LowEnergy.PreparationVacuumDAGCoefficient
