import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedSchur97WardDeterminant

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedSchur97WardFactor
open Polynomial CanonicalGradedSpatialSource PreparationVacuumPhysicalCharacteristic
open ActualDressedFullCoulomb ActualSourcePreparedClockReducedPencil
open ActualSourcePreparedEMClockEquation ActualSourcePreparedTemporalEMConstraint
open ActualSourcePreparedAuxiliaryClockReduction ActualPreparedMatterSupport ActualPreparedMatterClock
open ActualSourcePreparedInactiveNativeInverse ActualSourcePreparedSchur97Polynomial
open ActualSourcePreparedSchur97Cofactor ActualSourcePreparedSchur97RatioTail
open ActualDressedNoetherCoulombUnit ActualSourcePreparedFourClockCarrier
open ActualSourcePreparedSchur97WardRow ActualSourcePreparedSchur97WardSchur
open scoped Matrix BigOperators

attribute [local irreducible] sourceClockReducedPencil sourceEMClockReducedRow sourceEMClockForce
  sourceSchur97Polynomial nativeClockInverseNumerator Matrix.det Matrix.adjugate
  sourceSchur97Force sourceFourClockDenominator sourceMatterClockPencil
  ActualEMCarrierOwn.emInsertion sourceTemporalEMForce dotProduct Matrix.mulVec
  sourceSchur97LiteralNoetherNumerator sourceAuxiliaryClockFactor nativeClockDenominator
  sourceClockEval noetherPairScale

open ActualDressedOrderedStatic ActualDressedCorrectedGreen
open ActualSourcePreparedSchur97WardDeterminant
open ActualSourcePreparedSchur97NoetherFraction ActualSourcePreparedN3EMChargeRead

private theorem power_quotient (P : (ℂ[X])[X]) (m : ℕ) (factor : X^m ∣ P) :
    X^m*(P /ₘ X^m) = P := by
  obtain ⟨Q,same⟩ := factor
  rw [same,mul_divByMonic_cancel_left Q (monic_X_pow m)]

def sourceSchur97WardNoetherNumerator (event : DressedEvent) (n : PhysicalMomentum) :
    (ℂ[X])[X] := sourceSchur97LiteralNoetherNumerator event n /ₘ X^3

attribute [local irreducible] sourceSchur97WardNoetherNumerator

private theorem product_three_dvd (a c d v : (ℂ[X])[X])
    (factor : (X : (ℂ[X])[X])^3 ∣ c) : X^3 ∣ a*((c*d)*v) :=
  dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left factor d) v) a

private theorem auxiliary_three_dvd (event : DressedEvent) (n : PhysicalMomentum) :
    (X : (ℂ[X])[X])^3 ∣ sourceAuxiliaryClockFactor event n := by
  delta sourceAuxiliaryClockFactor
  exact dvd_mul_right _ _

private theorem source_literal_function_view :
    sourceSchur97LiteralNoetherNumerator =
      fun (event : DressedEvent) (n : PhysicalMomentum) =>
        (C (C (noetherPairScale^2))*(C (X : ℂ[X]))^4)*
          ((sourceAuxiliaryClockFactor event n*nativeClockDenominator n)*
            dotProduct sourceSchur97Force
              ((sourceSchur97Polynomial event n).adjugate*ᵥsourceSchur97Force)) := by
  delta sourceSchur97LiteralNoetherNumerator
  rfl

theorem source_schur97_noether_three_dvd (event : DressedEvent) (n : PhysicalMomentum) :
    (X : (ℂ[X])[X])^3 ∣ sourceSchur97LiteralNoetherNumerator event n := by
  rw [source_literal_function_view]
  exact product_three_dvd
    (C (C (noetherPairScale^2))*(C (X : ℂ[X]))^4)
    (sourceAuxiliaryClockFactor event n) (nativeClockDenominator n)
    (dotProduct sourceSchur97Force ((sourceSchur97Polynomial event n).adjugate*ᵥsourceSchur97Force))
    (auxiliary_three_dvd event n)

theorem source_schur97_ward_noether_factor (event : DressedEvent) (n : PhysicalMomentum) :
    sourceSchur97LiteralNoetherNumerator event n =
      X^3*sourceSchur97WardNoetherNumerator event n := by
  delta sourceSchur97WardNoetherNumerator
  exact (power_quotient (sourceSchur97LiteralNoetherNumerator event n) 3
    (source_schur97_noether_three_dvd event n)).symm


private theorem scalar_fraction (s a b : ℂ) (away : s ≠ 0) :
    (s^3*a)/(s^2*b) = s*(a/b) := by
  have numerator : s^3*a = s^2*(s*a) := by ring
  rw [numerator,mul_div_mul_left _ _ (pow_ne_zero 2 away),mul_div_assoc]

/-- The exact full source read retains the remaining Ward determinant and
Noether numerator. The explicit base clock power is not a finiteness claim. -/
theorem source_schur97_ward_fraction (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (away : (sigma : ℂ) ≠ 0) :
    sourceClockEval eps sigma (sourceSchur97LiteralNoetherNumerator event n) /
      sourceClockEval eps sigma (sourceSchur97Determinant event n) =
      (sigma : ℂ)*(sourceClockEval eps sigma (sourceSchur97WardNoetherNumerator event n)/
        sourceClockEval eps sigma (sourceSchur97WardDeterminant event n)) := by
  have numerator := congrArg (sourceClockEval eps sigma) (source_schur97_ward_noether_factor event n)
  have denominator := congrArg (sourceClockEval eps sigma) (source_schur97_ward_determinant_factor event n)
  have clock : sourceClockEval eps sigma (X : (ℂ[X])[X]) = (sigma : ℂ) := by
    simp only [sourceClockEval,RingHom.comp_apply,clockSpecialize,Polynomial.coe_mapRingHom,
      Polynomial.map_X,Polynomial.coe_evalRingHom,eval_X]
  simp only [map_mul,map_pow,clock] at numerator denominator
  rw [numerator,denominator]
  exact scalar_fraction _ _ _ away

/-- The original full Noether reader consumes the generated clock factors. -/
theorem source_schur97_ward_actual_noether (event : DressedEvent) (e : scaleDomain)
    (n : PhysicalMomentum) (sigma : ℝ) (unit : spatialSquare n=1)
    (positive : 0<e.val) (small : e.val≤1/2) (damping : 0<sigma)
    (regular : correctedDet event e.val 0 sigma n≠0) :
    (e.val:ℂ)^4*sourceN3TemporalEMCoefficient event e.val sigma n =
      (sigma:ℂ)*(sourceClockEval e.val sigma (sourceSchur97WardNoetherNumerator event n)/
        sourceClockEval e.val sigma (sourceSchur97WardDeterminant event n)) := by
  have original := source_schur97_noether_fraction event e n sigma unit positive small damping regular
  have returned : (e.val:ℂ)^4*sourceN3TemporalEMCoefficient event e.val sigma n =
      sourceClockEval e.val sigma (sourceSchur97LiteralNoetherNumerator event n)/
        sourceClockEval e.val sigma (sourceSchur97Determinant event n) := by
    rw [source_literal_function_view]
    exact original
  exact returned.trans (source_schur97_ward_fraction event n e.val sigma
    (Complex.ofReal_ne_zero.mpr damping.ne'))

private theorem order_shift (P W : (ℂ[X])[X]) (m : ℕ)
    (same : P=X^m*W) (nonzero : P≠0) : P.natTrailingDegree=m+W.natTrailingDegree := by
  have residual : W≠0 := by
    intro zero
    apply nonzero
    rw [same,zero,mul_zero]
  rw [same,natTrailingDegree_mul (pow_ne_zero m X_ne_zero) residual,natTrailingDegree_X_pow]

/-- Zero numerators remain a separate branch of the original response. -/
theorem source_schur97_ward_noether_order (event : DressedEvent) (n : PhysicalMomentum)
    (nonzero : sourceSchur97LiteralNoetherNumerator event n≠0) :
    (sourceSchur97LiteralNoetherNumerator event n).natTrailingDegree =
      3+(sourceSchur97WardNoetherNumerator event n).natTrailingDegree :=
  order_shift _ _ 3 (source_schur97_ward_noether_factor event n) nonzero

theorem source_schur97_ward_determinant_order (event : DressedEvent) (n : PhysicalMomentum)
    (nonzero : sourceSchur97Determinant event n≠0) :
    (sourceSchur97Determinant event n).natTrailingDegree =
      2+(sourceSchur97WardDeterminant event n).natTrailingDegree :=
  order_shift _ _ 2 (source_schur97_ward_determinant_factor event n) nonzero

end LowEnergy.GaussComposite.ActualSourcePreparedSchur97WardFactor
