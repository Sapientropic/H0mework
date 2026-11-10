import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedSchur97WardSchur

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedSchur97WardDeterminant
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

def sourceSchur97WardPivot : NativeActive := ⟨15,by decide⟩

private theorem entry_from_projection (M : Matrix (Fin 289) (Fin 4) ℂ)
    (i : Fin 289) (j : Fin 4) (z : ℂ)
    (projection : (M.transpose *ᵥ Pi.single i 1) j = z) : M i j = z := by
  rw [Matrix.mulVec_single_one,Matrix.col_apply,Matrix.transpose_apply] at projection
  exact projection

private theorem em_pivot_coordinate : ActualEMCarrierOwn.emInsertion (15 : Fin 289) 0 = (-1/2 : ℂ) := by
  apply entry_from_projection
  rw [ActualEMCarrierOwn.em_projection_coordinates]
  norm_num [PreparationVacuumMixedFieldReturn.gaugeSlot,Pi.single_apply,Fin.ext_iff]

private theorem pivot_force : sourceSchur97Force sourceSchur97WardPivot = C (C (-1/2 : ℂ)) := by
  unfold sourceSchur97Force sourceEMClockForce sourceTemporalEMForce
  change C (C (ActualEMCarrierOwn.emInsertion (15 : Fin 289) 0)) = C (C (-1/2 : ℂ))
  exact congrArg (fun z : ℂ => (C (C z) : (ℂ[X])[X])) em_pivot_coordinate


def sourceSchur97WardDeterminant (event : DressedEvent) (n : PhysicalMomentum) :
    (ℂ[X])[X] := sourceSchur97Determinant event n /ₘ X^2

attribute [local irreducible] sourceSchur97WardRow sourceSchur97WardDeterminant sourceSchur97Determinant

private theorem ward_det {I : Type*} [Fintype I] [DecidableEq I]
    (Q : Matrix I I ((ℂ[X])[X])) (E R : I → (ℂ[X])[X]) (i : I)
    (x k ki : (ℂ[X])[X]) (row : E ᵥ* Q = x • R) (pivot : E i = k)
    (inverse : ki*k = 1) : Q.det = x*(ki*(Q.updateRow i R).det) := by
  have rows := Matrix.det_updateRow_sum Q i E
  rw [←Matrix.vecMul_eq_sum,row,Matrix.det_updateRow_smul,pivot,smul_eq_mul] at rows
  calc
    _ = ki*(k*Q.det) := by rw [←mul_assoc,inverse,one_mul]
    _ = ki*(x*(Q.updateRow i R).det) := congrArg (fun z => ki*z) rows.symm
    _ = _ := by ring

private theorem source_det_view (event : DressedEvent) (n : PhysicalMomentum) :
    sourceSchur97Determinant event n = (sourceSchur97Polynomial event n).det := by
  delta sourceSchur97Determinant
  rfl

private theorem ward_det_dvd_view {I : Type*} [Fintype I] [DecidableEq I]
    (Q : Matrix I I ((ℂ[X])[X])) (E R : I → (ℂ[X])[X]) (i : I)
    (x k ki D : (ℂ[X])[X]) (dview : D = Q.det)
    (row : E ᵥ* Q = x • R) (pivot : E i = k) (inverse : ki*k = 1) : x ∣ D := by
  rw [dview]
  exact ⟨ki*(Q.updateRow i R).det,ward_det Q E R i x k ki row pivot inverse⟩

private theorem power_quotient (P : (ℂ[X])[X]) (m : ℕ) (factor : X^m ∣ P) :
    X^m*(P /ₘ X^m) = P := by
  obtain ⟨Q,same⟩ := factor
  rw [same,mul_divByMonic_cancel_left Q (monic_X_pow m)]

private theorem pivot_inverse : C (C (-2 : ℂ))*C (C (-1/2 : ℂ)) = (1 : (ℂ[X])[X]) := by
  rw [←map_mul,←map_mul]
  norm_num

/-- The fixed physical EM row removes precisely its two known clock factors;
all residual determinant orders remain in the original reduced matrix. -/
theorem source_schur97_ward_determinant_factor (event : DressedEvent) (n : PhysicalMomentum) :
    sourceSchur97Determinant event n = X^2*sourceSchur97WardDeterminant event n := by
  have factor : (X : (ℂ[X])[X])^2 ∣ sourceSchur97Determinant event n :=
    @ward_det_dvd_view NativeActive inferInstance inferInstance
      (sourceSchur97Polynomial event n) sourceSchur97Force
      (sourceSchur97WardRow event n) sourceSchur97WardPivot (X^2)
      (C (C (-1/2 : ℂ))) (C (C (-2 : ℂ)))
      (sourceSchur97Determinant event n) (source_det_view event n)
      (source_schur97_em_ward_row event n) pivot_force pivot_inverse
  delta sourceSchur97WardDeterminant
  exact (power_quotient (sourceSchur97Determinant event n) 2 factor).symm


end LowEnergy.GaussComposite.ActualSourcePreparedSchur97WardDeterminant
