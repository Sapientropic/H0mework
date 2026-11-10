import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.ActualSourcePreparedNoetherPiOwn.ActualSourcePreparedSchur97EMNormalization
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedSchur97PolynomialNormalization

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedSchur97CommonPrincipal
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open PreparationVacuumPhysicalCharacteristic ActualDressedFullCoulomb ActualDressedNoetherCoulombUnit
open ActualDressedOrderedStatic ActualDressedCorrectedGreen ActualDressedUniformMaterialCoefficients
open ActualSourcePreparedSchur97PhysicalRead ActualSourcePreparedN3EMChargeRead ActualSourcePreparedTemporalQuantumWard
open ActualSourcePreparedInactiveSchurReturn ActualSourcePreparedSchur97Normalization
open ActualPreparedMatterSupport ActualPreparedMatterClock
open ActualSourcePreparedClockReducedPencil ActualSourcePreparedAuxiliaryClockReduction
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedEMClockEquation
open ActualSourcePreparedMatterClockField ActualSourcePreparedMatterClockPrincipal ActualSourcePreparedMatterClockBalance
open ActualSourcePreparedInactiveNativeInverse ActualSourcePreparedSchur97Polynomial
open ActualSourcePreparedSchur97Cofactor ActualSourcePreparedSchur97PolynomialNormalization
open scoped Matrix BigOperators

open ActualSourcePreparedSchur97EMNormalization

private theorem inactive_force (i : NativeInactive) : sourceEMClockForce i.val=0 := by
  unfold sourceEMClockForce
  rw [actual_em_force_inactive_zero i.val i.property,map_zero,map_zero]

private theorem dot_restrict {M A I R : Type*}
    [Fintype M] [Fintype A] [Fintype I] [CommRing R]
    (e : M ⊕ A ≃ I) (E v : I → R) (zero : ∀ i : A,E (e (Sum.inr i))=0) :
    dotProduct E v=dotProduct (E ∘ e ∘ Sum.inl) (v ∘ e ∘ Sum.inl) := by
  unfold dotProduct
  rw [←e.sum_comp,Fintype.sum_sum_type]
  have vanished : (∑i : A,E (e (Sum.inr i))*v (e (Sum.inr i)))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [zero i,zero_mul]
  change (∑i : M,E (e (Sum.inl i))*v (e (Sum.inl i)))+
    (∑i : A,E (e (Sum.inr i))*v (e (Sum.inr i)))=_
  rw [vanished,add_zero]
  rfl

private theorem force_dot_restrict (v : Fin 289 → (ℂ[X])[X]) :
    dotProduct sourceEMClockForce v=
      dotProduct sourceSchur97Force (v ∘ (Subtype.val : NativeActive → Fin 289)) := by
  exact dot_restrict nativeWholeIndex sourceEMClockForce v inactive_force

private theorem mulVec_restrict {M A I R : Type*}
    [Fintype M] [Fintype A] [Fintype I] [CommRing R]
    (e : M ⊕ A ≃ I) (E : I → R) (P : Matrix I I R)
    (zero : ∀ i : A,E (e (Sum.inr i))=0) :
    (P*ᵥE) ∘ e ∘ Sum.inl=P.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)*ᵥ(E ∘ e ∘ Sum.inl) := by
  funext i
  change dotProduct (P (e (Sum.inl i))) E=
    dotProduct (P (e (Sum.inl i)) ∘ e ∘ Sum.inl) (E ∘ e ∘ Sum.inl)
  exact (dotProduct_comm _ _).trans
    ((dot_restrict e E (P (e (Sum.inl i))) zero).trans (dotProduct_comm _ _))

private theorem force_mulVec_restrict (P : Matrix (Fin 289) (Fin 289) ((ℂ[X])[X])) :
    (P*ᵥsourceEMClockForce) ∘ (Subtype.val : NativeActive → Fin 289)=
      P.submatrix Subtype.val Subtype.val*ᵥsourceSchur97Force := by
  exact mulVec_restrict nativeWholeIndex sourceEMClockForce P inactive_force

private theorem complete_contraction (P : Matrix (Fin 289) (Fin 289) ((ℂ[X])[X]))
    (c : (ℂ[X])[X]) :
    dotProduct sourceEMClockForce (c • (P*ᵥsourceEMClockForce))=
      c*dotProduct sourceSchur97Force
        (P.submatrix (Subtype.val : NativeActive → Fin 289) Subtype.val*ᵥsourceSchur97Force) := by
  rw [dotProduct_smul,smul_eq_mul,force_dot_restrict,force_mulVec_restrict]

attribute [local irreducible] Matrix.det Matrix.adjugate Matrix.mulVec sourceClockEval
  sourceMatterClockPencil sourceEMClockForce sourceSchur97Force

private theorem full_source_pairing (event : DressedEvent) (n : PhysicalMomentum) :
    dotProduct sourceEMClockForce
      (sourceAuxiliaryClockFactor event n • ((sourceMatterClockPencil event n).adjugate*ᵥsourceEMClockForce))=
    sourceAuxiliaryClockFactor event n*dotProduct sourceSchur97Force
      ((sourceMatterClockPencil event n).adjugate.submatrix
        (Subtype.val : NativeActive → Fin 289) Subtype.val*ᵥsourceSchur97Force) := by
  exact complete_contraction ((sourceMatterClockPencil event n).adjugate)
    (sourceAuxiliaryClockFactor event n)

private theorem source_principal (event : DressedEvent) (n : PhysicalMomentum) :
    sourceMatterClockBalanceNumerator event n+C (C (3/4:ℂ))*sourceMatterClockDeterminant event n=
      C (C (2*(lapse:ℂ)*(spatialSquare n:ℂ)))*(C (X:ℂ[X]))^4*
        (sourceAuxiliaryClockFactor event n*dotProduct sourceSchur97Force
          ((sourceMatterClockPencil event n).adjugate.submatrix
            (Subtype.val : NativeActive → Fin 289) Subtype.val*ᵥsourceSchur97Force)) := by
  exact (source_matter_clock_balance_principal event n).trans
    (congrArg (fun z : (ℂ[X])[X] =>
      C (C (2*(lapse:ℂ)*(spatialSquare n:ℂ)))*(C (X:ℂ[X]))^4*z)
      (full_source_pairing event n))

-- Keep the literal polynomial multiplication instance while contracting source matrices.
private theorem weighted_cross
    (h D a t c d x q y B g : (ℂ[X])[X])
    (principal : B+g*D=h*t*(c*y)) (cross : (d*D)*x=q*y) :
    h*D*(a*t*((c*d)*x))=a*q*(B+g*D) := by
  calc
    h*D*(a*t*((c*d)*x))=(a*h*t*c)*((d*D)*x) := by ring
    _=(a*h*t*c)*(q*y) := by rw [cross]
    _=a*q*(h*t*(c*y)) := by ring
    _=a*q*(B+g*D) := by rw [principal]

attribute [local irreducible] sourceSchur97Polynomial

/-- The complete Noether numerator and original full balance are restrictions
of the same bivariate source fraction, before either IR coordinate is fixed. -/
theorem source_schur97_full_balance_cross (event : DressedEvent) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) :
    C (C (2*(lapse:ℂ)*(spatialSquare n:ℂ)))*sourceMatterClockDeterminant event n*
      ((C (C (noetherPairScale^2))*(C (X:ℂ[X]))^4)*
        ((sourceAuxiliaryClockFactor event n*nativeClockDenominator n)*
          dotProduct sourceSchur97Force
            ((sourceSchur97Polynomial event n).adjugate*ᵥsourceSchur97Force)))=
    C (C (noetherPairScale^2))*(sourceSchur97Polynomial event n).det*
      (sourceMatterClockBalanceNumerator event n+
        C (C (3/4:ℂ))*sourceMatterClockDeterminant event n) := by
  exact weighted_cross (C (C (2*(lapse:ℂ)*(spatialSquare n:ℂ)))) (sourceMatterClockDeterminant event n)
    (C (C (noetherPairScale^2))) ((C (X:ℂ[X]))^4)
    (sourceAuxiliaryClockFactor event n) (nativeClockDenominator n)
    (dotProduct sourceSchur97Force ((sourceSchur97Polynomial event n).adjugate*ᵥsourceSchur97Force))
    ((sourceSchur97Polynomial event n).det)
    (dotProduct sourceSchur97Force ((sourceMatterClockPencil event n).adjugate.submatrix
      (Subtype.val : NativeActive → Fin 289) Subtype.val*ᵥsourceSchur97Force))
    (sourceMatterClockBalanceNumerator event n) (C (C (3/4:ℂ)))
    (source_principal event n) (source_schur97_em_scalar_cofactor_cross event n unit)

end LowEnergy.GaussComposite.ActualSourcePreparedSchur97CommonPrincipal
