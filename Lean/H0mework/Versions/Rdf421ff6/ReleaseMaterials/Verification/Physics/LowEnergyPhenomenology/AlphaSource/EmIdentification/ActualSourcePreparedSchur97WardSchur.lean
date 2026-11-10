import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedSchur97WardRow

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedSchur97WardSchur
open Polynomial CanonicalGradedSpatialSource PreparationVacuumPhysicalCharacteristic
open ActualDressedFullCoulomb ActualSourcePreparedClockReducedPencil
open ActualSourcePreparedEMClockEquation ActualSourcePreparedTemporalEMConstraint
open ActualSourcePreparedAuxiliaryClockReduction ActualPreparedMatterSupport ActualPreparedMatterClock
open ActualSourcePreparedInactiveNativeInverse ActualSourcePreparedSchur97Polynomial
open ActualSourcePreparedSchur97Cofactor ActualSourcePreparedSchur97RatioTail
open ActualDressedNoetherCoulombUnit ActualSourcePreparedFourClockCarrier
open ActualSourcePreparedSchur97WardRow
open scoped Matrix BigOperators

attribute [local irreducible] sourceClockReducedPencil sourceEMClockReducedRow sourceEMClockForce
  sourceSchur97Polynomial nativeClockInverseNumerator Matrix.det Matrix.adjugate
  sourceSchur97Force sourceFourClockDenominator sourceMatterClockPencil

/-- The original Ward row keeps every active/inactive right reconstruction. -/
def sourceSchur97WardRow (event : DressedEvent) (n : PhysicalMomentum) :
    NativeActive → (ℂ[X])[X] :=
  nativeClockDenominator n • (sourceEMClockReducedRow event n ∘ Subtype.val) -
    ((sourceEMClockReducedRow event n ∘ (Subtype.val : NativeInactive → Fin 289)) ᵥ*
      nativeClockInverseNumerator n) ᵥ*
      (sourceMatterClockPencil event n).submatrix
        (Subtype.val : NativeInactive → Fin 289) (Subtype.val : NativeActive → Fin 289)

private theorem schur_row {A I : Type*} [Fintype A] [Fintype I]
    (PAA : Matrix A A ((ℂ[X])[X])) (PAI : Matrix A I ((ℂ[X])[X]))
    (PIA : Matrix I A ((ℂ[X])[X])) (N : Matrix I I ((ℂ[X])[X]))
    (E RA : A → (ℂ[X])[X]) (RI : I → (ℂ[X])[X]) (d x : (ℂ[X])[X])
    (active : E ᵥ* PAA = x • RA) (inactive : E ᵥ* PAI = x • RI) :
    E ᵥ* (d • PAA - PAI*N*PIA) = x • (d • RA-(RI ᵥ* N) ᵥ* PIA) := by
  rw [Matrix.vecMul_sub,Matrix.vecMul_smul,←Matrix.vecMul_vecMul,←Matrix.vecMul_vecMul,
    active,inactive,Matrix.smul_vecMul,Matrix.smul_vecMul]
  funext j
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

private theorem schur_views {A I : Type*} [Fintype A] [Fintype I]
    (PAA : Matrix A A ((ℂ[X])[X])) (PAI : Matrix A I ((ℂ[X])[X]))
    (PIA : Matrix I A ((ℂ[X])[X])) (N : Matrix I I ((ℂ[X])[X]))
    (E RA : A → (ℂ[X])[X]) (RI : I → (ℂ[X])[X]) (d x : (ℂ[X])[X])
    (Q : Matrix A A ((ℂ[X])[X])) (R : A → (ℂ[X])[X])
    (pencil : Q = d • PAA-PAI*N*PIA) (row : R = d • RA-(RI ᵥ* N) ᵥ* PIA)
    (active : E ᵥ* PAA = x • RA) (inactive : E ᵥ* PAI = x • RI) :
    E ᵥ* Q = x • R := by
  rw [pencil,row]
  exact schur_row PAA PAI PIA N E RA RI d x active inactive

attribute [local irreducible] sourceSchur97WardRow

private theorem source_pencil_view (event : DressedEvent) (n : PhysicalMomentum) :
    sourceSchur97Polynomial event n =
      nativeClockDenominator n • (sourceMatterClockPencil event n).submatrix Subtype.val Subtype.val -
      (sourceMatterClockPencil event n).submatrix
        (Subtype.val : NativeActive → Fin 289) (Subtype.val : NativeInactive → Fin 289) *
      nativeClockInverseNumerator n * (sourceMatterClockPencil event n).submatrix
        (Subtype.val : NativeInactive → Fin 289) (Subtype.val : NativeActive → Fin 289) := by
  unfold sourceSchur97Polynomial
  rfl

private theorem source_row_view (event : DressedEvent) (n : PhysicalMomentum) :
    sourceSchur97WardRow event n =
      nativeClockDenominator n • (sourceEMClockReducedRow event n ∘ (Subtype.val : NativeActive → Fin 289)) -
      ((sourceEMClockReducedRow event n ∘ (Subtype.val : NativeInactive → Fin 289)) ᵥ*
        nativeClockInverseNumerator n) ᵥ*
      (sourceMatterClockPencil event n).submatrix
        (Subtype.val : NativeInactive → Fin 289) (Subtype.val : NativeActive → Fin 289) := by
  unfold sourceSchur97WardRow
  rfl

theorem source_schur97_em_ward_row (event : DressedEvent) (n : PhysicalMomentum) :
    sourceSchur97Force ᵥ* sourceSchur97Polynomial event n =
      (X : (ℂ[X])[X])^2 • sourceSchur97WardRow event n := by
  exact @schur_views NativeActive NativeInactive inferInstance inferInstance
    ((sourceMatterClockPencil event n).submatrix Subtype.val Subtype.val)
    ((sourceMatterClockPencil event n).submatrix
      (Subtype.val : NativeActive → Fin 289) (Subtype.val : NativeInactive → Fin 289))
    ((sourceMatterClockPencil event n).submatrix
      (Subtype.val : NativeInactive → Fin 289) (Subtype.val : NativeActive → Fin 289))
    (nativeClockInverseNumerator n) sourceSchur97Force
    (sourceEMClockReducedRow event n ∘ (Subtype.val : NativeActive → Fin 289))
    (sourceEMClockReducedRow event n ∘ (Subtype.val : NativeInactive → Fin 289))
    (nativeClockDenominator n) (X^2)
    (sourceSchur97Polynomial event n) (sourceSchur97WardRow event n)
    (source_pencil_view event n) (source_row_view event n)
    (source_schur97_active_em_row (I := NativeActive) event n (Subtype.val : NativeActive → Fin 289))
    (source_schur97_active_em_row (I := NativeInactive) event n (Subtype.val : NativeInactive → Fin 289))

end LowEnergy.GaussComposite.ActualSourcePreparedSchur97WardSchur
