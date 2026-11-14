import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.ConnectingExact
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDRationalKummerCohomology

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.UniversalBSDRationalKummerCokernel

open UniversalBSDGeometricGalois UniversalBSDRationalKummerCohomology
open UniversalBSDRationalKummerCohomology.RationalKummerBoundaryCochainData
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion

private def level (p : Nat.Primes) (j : Nat) : Nat := p.1^(j+1)

private theorem level_pos (p : Nat.Primes) (j : Nat) : 0 < level p j :=
  pow_pos p.property.pos _

private theorem power_is_nsmul {A : Type} [AddCommGroup A]
    (p : Nat.Primes) (j : Nat) (value : A) :
    powerMultiplication p j value = level p j • value := by
  change (p.1 : ℤ)^(j+1) • value = _
  rw [← Nat.cast_pow]
  exact Nat.cast_smul_eq_nsmul ℤ _ _

abbrev pointEvaluation (source : RationalEllipticCurveSource) :=
  (rationalPointToGeometric source).toIntLinearMap

private theorem point_evaluation_injective (source : RationalEllipticCurveSource) :
    Function.Injective (pointEvaluation source) := rationalPointToGeometric_injective source

private abbrev receipt (source : RationalEllipticCurveSource) (p : Nat.Primes) (j : Nat)
    (point : RationalPoints source) :=
  sourceGeneratedRationalKummerBoundaryCochain source (level p j) (level_pos p j) point

private theorem receipt_division (source : RationalEllipticCurveSource) (p : Nat.Primes) (j : Nat)
    (point : RationalPoints source) :
    powerMultiplication p j (receipt source p j point).divisionPoint = pointEvaluation source point :=
  (power_is_nsmul p j _).trans (receipt source p j point).divides

/-- The actual Kummer division point supplies the torsion class of the same curve and source point. -/
def divisionCokernelClass (source : RationalEllipticCurveSource) (p : Nat.Primes) (j : Nat)
    (point : RationalPoints source) : CokernelTorsion (pointEvaluation source) p j :=
  cokernelTorsionClassOfDivision (pointEvaluation source) p j point
    (receipt source p j point).divisionPoint (receipt_division source p j point)

theorem actual_kummer_division_reads_source (source : RationalEllipticCurveSource)
    (p : Nat.Primes) (j : Nat) (point : RationalPoints source) :
    stageCokernelConnecting (pointEvaluation source) (point_evaluation_injective source) p j
      (divisionCokernelClass source p j point) = stageProjection p j point :=
  stage_cokernel_connecting_of_paid (pointEvaluation source) (point_evaluation_injective source)
    p j point (receipt source p j point).divisionPoint (receipt_division source p j point)

theorem actual_kummer_connecting_surjective (source : RationalEllipticCurveSource)
    (p : Nat.Primes) (j : Nat) :
    Function.Surjective (stageCokernelConnecting (pointEvaluation source) (point_evaluation_injective source) p j) :=
  cokernel_connecting_surjective_of_source_division (pointEvaluation source)
    (point_evaluation_injective source) p j fun point =>
      ⟨(receipt source p j point).divisionPoint, receipt_division source p j point⟩

private abbrev kummerLinear (source : RationalEllipticCurveSource) (p : Nat.Primes) (j : Nat) :=
  (rationalKummerAddHom source (level p j) (level_pos p j)).toIntLinearMap

private theorem kummer_kernel (source : RationalEllipticCurveSource) (p : Nat.Primes) (j : Nat) :
    powerRange (L := RationalPoints source) p j = LinearMap.ker (kummerLinear source p j) := by
  ext point
  rw [LinearMap.mem_ker]
  change (∃ previous, powerMultiplication p j previous = point) ↔
    sourceGeneratedRationalKummerClass source (level p j) (level_pos p j) point = 0
  rw [sourceGeneratedRationalKummerClass_eq_zero_iff]
  constructor
  · rintro ⟨previous, same⟩
    exact ⟨previous, (power_is_nsmul p j previous).symm.trans same⟩
  · rintro ⟨previous, same⟩
    exact ⟨previous, (power_is_nsmul p j previous).trans same⟩

private def stageKummer (source : RationalEllipticCurveSource) (p : Nat.Primes) (j : Nat) :=
  (powerRange (L := RationalPoints source) p j).liftQ (kummerLinear source p j) (kummer_kernel source p j).le

/-- The original Kummer class consumes the source stage read from the geometric cokernel. -/
def cokernelKummer (source : RationalEllipticCurveSource) (p : Nat.Primes) (j : Nat) :
    CokernelTorsion (pointEvaluation source) p j →ₗ[ℤ] GlobalKummerH1 source (level p j) :=
  (stageKummer source p j).comp
    (stageCokernelConnecting (pointEvaluation source) (point_evaluation_injective source) p j)

theorem actual_kummer_cokernel_class (source : RationalEllipticCurveSource)
    (p : Nat.Primes) (j : Nat) (point : RationalPoints source) :
    cokernelKummer source p j (divisionCokernelClass source p j point) =
      sourceGeneratedRationalKummerClass source (level p j) (level_pos p j) point :=
  congrArg (stageKummer source p j) (actual_kummer_division_reads_source source p j point)

theorem actual_kummer_cokernel_kernel (source : RationalEllipticCurveSource) (p : Nat.Primes) (j : Nat) :
    LinearMap.ker (cokernelKummer source p j) =
      LinearMap.range (ambientToCokernelTorsion (pointEvaluation source) p j) := by
  have faithful : LinearMap.ker (stageKummer source p j) = ⊥ :=
    Submodule.ker_liftQ_eq_bot' _ _ (kummer_kernel source p j)
  rw [cokernelKummer, LinearMap.ker_comp_of_ker_eq_bot _ faithful]
  exact (cokernel_connecting_kernel (pointEvaluation source) (point_evaluation_injective source) p j).symm

end SaturationMonoid.UniversalBSDRationalKummerCokernel
