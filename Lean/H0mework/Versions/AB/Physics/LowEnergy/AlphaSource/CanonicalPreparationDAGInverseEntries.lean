import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationDAGNormalized

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumDAGCoefficient
open PreparationVacuumClockSymbol PreparationVacuumClockJacobian PreparationVacuumEngineBudget
open PreparationVacuumEngineSource PreparationVacuumEnergyTail PreparationActualFactor
open GaussHistoryHilbert PreparationPhaseSource
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff PreparationVacuumWeyl
open scoped BigOperators Matrix

-- These are the literal JI entries in the original Engine's central coefficient algebra.
def inverseCoefficient (a b : Fin 4) : NormalizedCoefficient :=
  Fin.cases (Fin.cases ⟨-MvPolynomial.X 0^3,![0,1,0]⟩
      (fun _ => polynomialCoefficient 0))
    (fun i => Fin.cases (polynomialCoefficient 0)
      (fun j => ⟨-MvPolynomial.X 0^3*adjugatePolynomial i j,![0,0,1]⟩)) a b

def correctionCoefficient (a b : Fin 4) : NormalizedCoefficient := negateCoefficient (inverseCoefficient a b)

theorem inverseCoefficient_sourceInverse (a b : Fin 4) (x : SourcePhase) :
    coefficientValue (inverseCoefficient a b) x=sourceInverse x a b := by
  refine Fin.cases ?_ (fun i => ?_) a
  · refine Fin.cases ?_ (fun j => ?_) b
    · simp [inverseCoefficient,coefficientValue_denominator,evalAt,sourceVariables,sourceInverse_clock]
    · exact polynomialCoefficient_source 0 x
  · refine Fin.cases ?_ (fun j => ?_) b
    · exact polynomialCoefficient_source 0 x
    · change coefficientValue ⟨-MvPolynomial.X 0^3*adjugatePolynomial i j,![0,0,1]⟩ x=
        -actualC x^3*(sourceM x)⁻¹ i j
      rw [coefficientValue_denominator]
      simp only [map_mul,map_neg,map_pow,adjugatePolynomial_source]
      have cvalue : evalAt x (MvPolynomial.X 0)=actualC x := by simp [evalAt,sourceVariables]
      rw [cvalue]
      simp
      simp only [sourceDet,Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul,div_eq_mul_inv]
      ring

theorem inverseCoefficient_native (a b : Fin 4) (x : SourcePhase) (hx : x∈poleDomain) :
    coefficientValue (inverseCoefficient a b) x=(principalForceJacobian x)⁻¹ a b := by
  rw [inverseCoefficient_sourceInverse,sourceInverse_native x hx.1 hx.2]

theorem correctionCoefficient_native (a b : Fin 4) (x : SourcePhase) (hx : x∈poleDomain) :
    coefficientValue (correctionCoefficient a b) x= -(principalForceJacobian x)⁻¹ a b := by
  rw [correctionCoefficient,negateCoefficient_source,inverseCoefficient_native a b x hx]

-- The source's actual resolvent division is the generated first allowed pole.
theorem inverseClockCoefficient_native (x : SourcePhase) :
    coefficientValue (inversePoleCoefficient 0) x=(sourceClock x)⁻¹ := by
  rw [inversePoleCoefficient_source]
  rfl

def principalCoefficient : Fin 13 → NormalizedCoefficient :=
  ![⟨MvPolynomial.C (1/2)*MvPolynomial.X 1,![2,0,0]⟩,
    polynomialCoefficient 0,polynomialCoefficient 0,polynomialCoefficient 0,
    polynomialCoefficient (MvPolynomial.X 2),polynomialCoefficient (MvPolynomial.X 3),
    polynomialCoefficient (MvPolynomial.X 1-MvPolynomial.X 2-MvPolynomial.X 3),
    polynomialCoefficient (MvPolynomial.X 4),polynomialCoefficient (MvPolynomial.X 5),
    polynomialCoefficient (MvPolynomial.X 6),
    polynomialCoefficient 0,polynomialCoefficient 0,polynomialCoefficient 0]

theorem principalCoefficient_native (slot : Fin 13) (x : SourcePhase) :
    coefficientValue (principalCoefficient slot) x=engineSource 0 slot x := by
  fin_cases slot <;>
    simp [principalCoefficient,polynomialCoefficient,evalAt,sourceVariables,
      engineSource,originalEnginePrincipalLeaves,actualC,actualT,actualS,coefficientValue_denominator]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem sourceEngine_generated_normalized (k : ℕ) (a : Fin 4) (x : SourcePhase) (hx : x∈poleDomain) :
    sourceEngine (k+1) a (Fin.last (k+1)) x=
      ∑ b : Fin 4,coefficientValue (correctionCoefficient a b) x*
        forceOrEnergy (k+1) (sourceEngine k) (some b) (Fin.last (k+1)) x := by
  rw [sourceEngine_generated]
  simp_rw [correctionCoefficient_native _ _ x hx]
  simp only [neg_mul,Finset.sum_neg_distrib]

theorem sourceEngine_generated_normalized_support (k : ℕ) (a : Fin 4)
    (z : FlatConfiguration) (p : PhysicalMomentum)
    (position : z∈thetaPositionClosed) (direction : normalizedMomentum p∈thetaDirectionClosed) (nonzero : p≠0) :
    sourceEngine (k+1) a (Fin.last (k+1)) (z,p)=
      ∑ b : Fin 4,coefficientValue (correctionCoefficient a b) (z,p)*
        forceOrEnergy (k+1) (sourceEngine k) (some b) (Fin.last (k+1)) (z,p) :=
  sourceEngine_generated_normalized k a (z,p) (source_support_admitted z p position direction nonzero)

end LowEnergy.PreparationVacuumDAGCoefficient
