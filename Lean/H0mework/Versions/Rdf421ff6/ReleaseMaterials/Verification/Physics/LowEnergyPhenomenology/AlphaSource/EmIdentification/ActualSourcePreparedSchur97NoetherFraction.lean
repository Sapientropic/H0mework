import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedSchur97Cofactor
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedSchur97PolynomialNormalization

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedSchur97NoetherFraction
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic ActualDressedFullCoulomb ActualDressedNoetherCoulombUnit
open ActualDressedOrderedStatic ActualDressedCorrectedGreen ActualDressedUniformMaterialCoefficients
open ActualSourcePreparedSchur97PhysicalRead ActualSourcePreparedN3EMChargeRead ActualSourcePreparedTemporalQuantumWard
open ActualSourcePreparedInactiveSchurReturn ActualSourcePreparedSchur97Normalization
open ActualPreparedMatterSupport ActualPreparedMatterClock
open ActualSourcePreparedClockReducedPencil ActualSourcePreparedAuxiliaryClockReduction
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedEMClockEquation
open ActualSourcePreparedMatterClockField ActualSourcePreparedMatterClockPrincipal
open ActualSourcePreparedInactiveNativeInverse ActualSourcePreparedSchur97Polynomial
open ActualSourcePreparedSchur97Cofactor ActualSourcePreparedSchur97PolynomialNormalization
open scoped Matrix BigOperators

open ActualSourcePreparedMatterClockBalance

attribute [local irreducible] Matrix.det Matrix.adjugate Matrix.mulVec sourceSchur97Polynomial

private theorem constant_eval (eps sigma : ℝ) (z : ℂ) :
    sourceClockEval eps sigma (C (C z))=z := by
  simp only [sourceClockEval,RingHom.comp_apply,clockSpecialize,Polynomial.coe_mapRingHom,
    Polynomial.map_C,Polynomial.coe_evalRingHom,Polynomial.eval_C]

private theorem epsilon_eval (eps sigma : ℝ) :
    sourceClockEval eps sigma (C (X:ℂ[X]))=(eps:ℂ) := by
  simp only [sourceClockEval,RingHom.comp_apply,clockSpecialize,Polynomial.coe_mapRingHom,
    Polynomial.map_C,Polynomial.coe_evalRingHom,Polynomial.eval_C,Polynomial.eval_X]

private theorem force_eval (eps sigma : ℝ) :
    sourceClockEval eps sigma ∘ sourceSchur97Force=
      sourceTemporalEMForce ∘ (Subtype.val : NativeActive → Fin 289) := by
  funext i
  exact constant_eval eps sigma (sourceTemporalEMForce i.val)

private theorem map_pairing {I : Type*} [Fintype I] [DecidableEq I]
    (f : ((ℂ[X])[X]) →+* ℂ) (Q : Matrix I I ((ℂ[X])[X]))
    (a c d : (ℂ[X])[X]) (E : I → (ℂ[X])[X]) :
    f (a*((c*d)*dotProduct E (Q.adjugate*ᵥE)))=
      f a*((f c*f d)*dotProduct (f ∘ E) ((Q.map f).adjugate*ᵥ(f ∘ E))) := by
  rw [map_mul,map_mul,map_mul,f.map_dotProduct]
  have vector : f ∘ (Q.adjugate*ᵥE)=(Q.adjugate.map f)*ᵥ(f ∘ E) := by
    funext i
    exact f.map_mulVec Q.adjugate E i
  rw [vector]
  have adj := f.map_adjugate Q
  simp only [RingHom.mapMatrix_apply] at adj
  rw [adj]

private theorem inverse_clear {I : Type*} [Fintype I] [DecidableEq I]
    (S Q : Matrix I I ℂ) (d : ℂ) (nonzero : d≠0) (clear : Q=d • S)
    (regular : S.det≠0) : S⁻¹=d • Q⁻¹ := by
  have qregular : IsUnit Q.det := by
    rw [clear,Matrix.det_smul]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ nonzero) regular)
  have inverse := Matrix.nonsing_inv_mul Q qregular
  have expanded : d • (Q⁻¹*S)=1 := by
    simpa only [clear,Matrix.mul_smul] using inverse
  have target : (d • Q⁻¹)*S=1 := by
    rw [Matrix.smul_mul]
    exact expanded
  exact Matrix.inv_eq_left_inv target

private theorem inverse_read {I : Type*} [Fintype I] [DecidableEq I]
    (Q : Matrix I I ℂ) (E : I → ℂ) :
    dotProduct E (Q⁻¹*ᵥE)=dotProduct E (Q.adjugate*ᵥE)/Q.det := by
  rw [Matrix.inv_def,Ring.inverse_eq_inv',Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
  simp only [div_eq_mul_inv]
  exact mul_comm _ _

private theorem point_fraction {I : Type*} [Fintype I] [DecidableEq I]
    (S Q : Matrix I I ℂ) (E : I → ℂ) (d c a x M D : ℂ)
    (nonzero : d≠0) (clear : Q=d • S) (regular : S.det≠0)
    (coefficient : x=a*c*dotProduct E (S⁻¹*ᵥE))
    (numerator : M=a*((c*d)*dotProduct E (Q.adjugate*ᵥE))) (denominator : D=Q.det) : x=M/D := by
  rw [coefficient,numerator,denominator,inverse_clear S Q d nonzero clear regular,
    Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul,inverse_read]
  simp only [div_eq_mul_inv]
  ac_rfl


private theorem mapped_pairing_return {I : Type*} [Fintype I] [DecidableEq I]
    (f : ((ℂ[X])[X]) →+* ℂ) (Q : Matrix I I ((ℂ[X])[X]))
    (a c d : (ℂ[X])[X]) (E : I → (ℂ[X])[X]) (force : I → ℂ) (w : ℂ)
    (weight : f a=w) (forcing : f ∘ E=force) :
    f (a*((c*d)*dotProduct E (Q.adjugate*ᵥE)))=
      w*((f c*f d)*dotProduct force ((Q.map f).adjugate*ᵥforce)) := by
  have mapped := map_pairing f Q a c d E
  rw [weight,forcing] at mapped
  exact mapped

attribute [local irreducible] sourceClockEval sourceMatterClockPencil
  sourceEMClockForce sourceSchur97Force sourceSchur97EMNumerator
  sourceSchur97FieldNumerator sourceSchur97Determinant

private theorem em_numerator_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) :
    sourceClockEval eps sigma
      ((C (C (noetherPairScale^2))*(C (X:ℂ[X]))^4)*
        ((sourceAuxiliaryClockFactor event n*nativeClockDenominator n)*
          dotProduct sourceSchur97Force ((sourceSchur97Polynomial event n).adjugate*ᵥsourceSchur97Force)))=
      (noetherPairScale^2*(eps:ℂ)^4)*
        ((sourceClockEval eps sigma (sourceAuxiliaryClockFactor event n)*
          sourceClockEval eps sigma (nativeClockDenominator n))*
          dotProduct (sourceTemporalEMForce ∘ (Subtype.val : NativeActive → Fin 289))
            (((sourceSchur97Polynomial event n).map (sourceClockEval eps sigma)).adjugate*ᵥ
              (sourceTemporalEMForce ∘ Subtype.val))) := by
  have weight : sourceClockEval eps sigma
      (C (C (noetherPairScale^2))*(C (X:ℂ[X]))^4)=noetherPairScale^2*(eps:ℂ)^4 := by
    rw [map_mul,constant_eval,map_pow,epsilon_eval]
  exact mapped_pairing_return (sourceClockEval eps sigma) (sourceSchur97Polynomial event n)
    (C (C (noetherPairScale^2))*(C (X:ℂ[X]))^4)
    (sourceAuxiliaryClockFactor event n) (nativeClockDenominator n) sourceSchur97Force
    (sourceTemporalEMForce ∘ (Subtype.val : NativeActive → Fin 289))
    (noetherPairScale^2*(eps:ℂ)^4) weight (force_eval eps sigma)


private theorem denominator_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) :
    sourceClockEval eps sigma (sourceSchur97Determinant event n)=
      ((sourceSchur97Polynomial event n).map (sourceClockEval eps sigma)).det := by
  delta sourceSchur97Determinant
  simpa only [RingHom.mapMatrix_apply] using
    (sourceClockEval eps sigma).map_det (sourceSchur97Polynomial event n)


/-- The complete original finite Noether coefficient consumes the same
source97 cofactor, including its original action weight and source clock. -/
theorem source_schur97_noether_fraction (event : DressedEvent) (e : scaleDomain)
    (n : PhysicalMomentum) (sigma : ℝ) (unit : spatialSquare n=1)
    (positive : 0<e.val) (small : e.val≤1/2) (damping : 0<sigma)
    (regular : correctedDet event e.val 0 sigma n≠0) :
    (e.val:ℂ)^4*sourceN3TemporalEMCoefficient event e.val sigma n=
      sourceClockEval e.val sigma ((C (C (noetherPairScale^2))*(C (X:ℂ[X]))^4)*
          ((sourceAuxiliaryClockFactor event n*nativeClockDenominator n)*
            dotProduct sourceSchur97Force ((sourceSchur97Polynomial event n).adjugate*ᵥsourceSchur97Force)))/
        sourceClockEval e.val sigma (sourceSchur97Determinant event n) := by
  have schur := (source_schur97_original_regular_iff event n e.val sigma unit positive small damping).mp regular
  exact point_fraction (sourceMatterNativeSchur event n e.val sigma)
    ((sourceSchur97Polynomial event n).map (sourceClockEval e.val sigma))
    (sourceTemporalEMForce ∘ (Subtype.val : NativeActive → Fin 289))
    (sourceClockEval e.val sigma (nativeClockDenominator n))
    (sourceClockEval e.val sigma (sourceAuxiliaryClockFactor event n))
    (noetherPairScale^2*(e.val:ℂ)^4)
    ((e.val:ℂ)^4*sourceN3TemporalEMCoefficient event e.val sigma n)
    (sourceClockEval e.val sigma ((C (C (noetherPairScale^2))*(C (X:ℂ[X]))^4)*
          ((sourceAuxiliaryClockFactor event n*nativeClockDenominator n)*
            dotProduct sourceSchur97Force ((sourceSchur97Polynomial event n).adjugate*ᵥsourceSchur97Force))))
    (sourceClockEval e.val sigma (sourceSchur97Determinant event n))
    (source_native_clock_denominator_nonzero n e.val sigma unit positive small)
    (source_schur97_polynomial_eval event n e.val sigma unit positive small) schur
    (source_schur97_actual_coefficient event e n sigma unit positive small damping schur)
    (em_numerator_eval event n e.val sigma) (denominator_eval event n e.val sigma)

end LowEnergy.GaussComposite.ActualSourcePreparedSchur97NoetherFraction
