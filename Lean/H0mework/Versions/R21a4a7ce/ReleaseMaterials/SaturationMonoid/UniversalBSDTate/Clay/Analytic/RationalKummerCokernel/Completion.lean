import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentLift
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDTate.Clay.Analytic.RationalKummerCokernel

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.UniversalBSDRationalKummerCokernel

open UniversalBSDGeometricDivisibility UniversalBSDGeometricGalois
open UniversalBSDRationalKummerCohomology
open UniversalBSDRationalKummerCohomology.RationalKummerBoundaryCochainData
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion

open private level level_pos point_evaluation_injective stageKummer from
  H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDTate.Clay.Analytic.RationalKummerCokernel

private theorem geometric_prime_surjective (source : RationalEllipticCurveSource) (p : Nat.Primes) :
    Function.Surjective (fun point : GeometricPoints source => (p.1 : ℤ) • point) := by
  intro point
  obtain ⟨divided, paid⟩ := exists_actual_nsmul_eq (GeometricCurve source) p.1 p.property.pos point
  exact ⟨divided, (Nat.cast_smul_eq_nsmul ℤ p.1 divided).trans paid⟩

/-- The source-generated geometric division lifts the entire rational completion. -/
theorem actual_kummer_completion_lifts (source : RationalEllipticCurveSource) (p : Nat.Primes) :
    Function.Surjective (cokernelConnectingAtLimit (pointEvaluation source)
      (point_evaluation_injective source) p) :=
  cokernel_connecting_limit_surjective (pointEvaluation source) (point_evaluation_injective source) p
    (geometric_prime_surjective source p)

/-- Each restriction of the same coherent cokernel lift has the original Kummer readout. -/
theorem actual_kummer_completion_read (source : RationalEllipticCurveSource)
    (p : Nat.Primes) (j : Nat)
    (lift : PrimePowerTorsionCompletion (GeometricPoints source ⧸ LinearMap.range (pointEvaluation source)) p)
    (point : RationalPoints source)
    (present : stageProjection p j point =
      (restriction (L := RationalPoints source) p j).hom
        (cokernelConnectingAtLimit (pointEvaluation source) (point_evaluation_injective source) p lift)) :
    cokernelKummer source p j
      ((torsionCompletionRestriction (GeometricPoints source ⧸ LinearMap.range (pointEvaluation source))
        p j).hom lift) =
      sourceGeneratedRationalKummerClass source (level p j) (level_pos p j) point :=
  congrArg (stageKummer source p j)
    ((cokernel_connecting_limit_restriction (pointEvaluation source) (point_evaluation_injective source)
      p j lift).symm.trans present.symm)

end SaturationMonoid.UniversalBSDRationalKummerCokernel
