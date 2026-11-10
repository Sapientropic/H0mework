import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedSchur97Polynomial

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedSchur97Cofactor
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedOrderedStatic ActualDressedNoetherCoulombUnit ActualDressedUniformMaterialCoefficients
open ActualSourcePreparedClockReducedPencil ActualSourcePreparedAuxiliaryClockReduction
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedTemporalQuantumWard
open ActualSourcePreparedEMClockEquation
open ActualSourcePreparedN3EMChargeRead ActualSourcePreparedInactiveNativeInverse
open ActualSourcePreparedInactiveSchurReturn ActualSourcePreparedSchur97PhysicalRead
open ActualSourcePreparedSchur97Polynomial
open scoped Matrix BigOperators
attribute [local irreducible] Matrix.det Matrix.adjugate Matrix.mulVec sourceSchur97Polynomial

def sourceSchur97Force : NativeActive → (ℂ[X])[X] := sourceEMClockForce ∘ Subtype.val

def sourceSchur97Determinant (event : DressedEvent) (n : PhysicalMomentum) : (ℂ[X])[X] :=
  (sourceSchur97Polynomial event n).det

/-- One native clearing factor and the original action clock are retained
in the same source field numerator. -/
def sourceSchur97FieldNumerator (event : DressedEvent) (n : PhysicalMomentum) : NativeActive → (ℂ[X])[X] :=
  (sourceAuxiliaryClockFactor event n*nativeClockDenominator n) •
    ((sourceSchur97Polynomial event n).adjugate*ᵥsourceSchur97Force)

def sourceSchur97EMNumerator (event : DressedEvent) (n : PhysicalMomentum) : (ℂ[X])[X] :=
  C (C (noetherPairScale^2))*(C (X:ℂ[X]))^4*
    dotProduct sourceSchur97Force (sourceSchur97FieldNumerator event n)



private theorem source_constant_eval (eps sigma : ℝ) (z : ℂ) :
    sourceClockEval eps sigma (C (C z))=z := by
  simp only [sourceClockEval,RingHom.comp_apply,clockSpecialize,Polynomial.coe_mapRingHom,
    Polynomial.map_C,Polynomial.coe_evalRingHom,Polynomial.eval_C]


private theorem force_eval (eps sigma : ℝ) :
    sourceClockEval eps sigma ∘ sourceSchur97Force=
      sourceTemporalEMForce ∘ (Subtype.val : NativeActive → Fin 289) := by
  funext i
  exact source_constant_eval eps sigma (sourceTemporalEMForce i.val)



private theorem map_cofactor {I : Type*} [Fintype I] [DecidableEq I]
    (f : ((ℂ[X])[X]) →+* ℂ) (P : Matrix I I ((ℂ[X])[X]))
    (a : (ℂ[X])[X]) (E : I → (ℂ[X])[X]) :
    f ∘ (a • (P.adjugate*ᵥE))=f a • ((P.map f).adjugate*ᵥ(f ∘ E)) := by
  funext i
  change f (a*(P.adjugate*ᵥE) i)=_
  rw [map_mul,f.map_mulVec]
  have adj := f.map_adjugate P
  simp only [RingHom.mapMatrix_apply] at adj
  rw [adj]
  rfl



private theorem mapped_det (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) :
    sourceClockEval eps sigma (sourceSchur97Determinant event n)=
      ((sourceSchur97Polynomial event n).map (sourceClockEval eps sigma)).det := by
  unfold sourceSchur97Determinant
  simpa only [RingHom.mapMatrix_apply] using
    (sourceClockEval eps sigma).map_det (sourceSchur97Polynomial event n)



private theorem scaled_inverse {I : Type*} [Fintype I] [DecidableEq I]
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

private theorem inverse_fraction {I : Type*} [Fintype I] [DecidableEq I]
    (Q : Matrix I I ℂ) (E : I → ℂ) (a : ℂ) (i : I) :
    (a • (Q⁻¹*ᵥE)) i=(a • (Q.adjugate*ᵥE)) i/Q.det := by
  rw [Matrix.inv_def,Ring.inverse_eq_inv',Matrix.smul_mulVec]
  simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv]
  ac_rfl

private theorem scaled_field_fraction {I : Type*} [Fintype I] [DecidableEq I]
    (S Q : Matrix I I ℂ) (d c : ℂ) (E F N : I → ℂ) (D : ℂ)
    (nonzero : d≠0) (clear : Q=d • S) (regular : S.det≠0)
    (field : F=c • (S⁻¹*ᵥE)) (numerator : N=(c*d) • (Q.adjugate*ᵥE))
    (denominator : D=Q.det) (i : I) : F i=N i/D := by
  rw [field,numerator,denominator,scaled_inverse S Q d nonzero clear regular,
    Matrix.smul_mulVec,smul_smul]
  exact inverse_fraction Q E (c*d) i

/-- The unchanged actual full field consumes the new97 polynomial cofactor
on its original determinant chart; the192 reconstruction remains unchanged. -/
theorem source_schur97_actual_field_fraction (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (unit : spatialSquare n=1) (positive : 0<eps) (small : eps≤1/2)
    (damping : 0<sigma) (regular : correctedDet event eps 0 sigma n≠0) (i : NativeActive) :
    sourceTemporalCorrectedField event eps sigma n i.val=
      sourceClockEval eps sigma (sourceSchur97FieldNumerator event n i)/
        sourceClockEval eps sigma (sourceSchur97Determinant event n) := by
  have schur := (source_schur97_original_regular_iff event n eps sigma unit positive small damping).mp regular
  have numerator := map_cofactor (sourceClockEval eps sigma) (sourceSchur97Polynomial event n)
    (sourceAuxiliaryClockFactor event n*nativeClockDenominator n) sourceSchur97Force
  rw [force_eval,map_mul] at numerator
  exact scaled_field_fraction
    (sourceMatterNativeSchur event n eps sigma)
    ((sourceSchur97Polynomial event n).map (sourceClockEval eps sigma))
    (sourceClockEval eps sigma (nativeClockDenominator n))
    (sourceClockEval eps sigma (sourceAuxiliaryClockFactor event n))
    (sourceTemporalEMForce ∘ (Subtype.val : NativeActive → Fin 289))
    (sourceTemporalCorrectedField event eps sigma n ∘ (Subtype.val : NativeActive → Fin 289))
    (sourceClockEval eps sigma ∘ sourceSchur97FieldNumerator event n)
    (sourceClockEval eps sigma (sourceSchur97Determinant event n))
    (source_native_clock_denominator_nonzero n eps sigma unit positive small)
    (source_schur97_polynomial_eval event n eps sigma unit positive small) schur
    (source_schur97_actual_field_return event n eps sigma unit positive small damping schur).1
    numerator (mapped_det event n eps sigma) i


end LowEnergy.GaussComposite.ActualSourcePreparedSchur97Cofactor
