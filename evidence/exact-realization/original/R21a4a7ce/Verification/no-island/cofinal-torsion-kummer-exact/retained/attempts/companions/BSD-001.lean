import SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentKernel.Noetherian
import SaturationMonoid.UniversalBSDTate.Clay.Analytic.RationalKummerCokernel.Completion

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.UniversalBSDRationalKummerCokernel

open UniversalBSDGeometricGalois
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion

open private point_evaluation_injective from
  SaturationMonoid.UniversalBSDTate.Clay.Analytic.RationalKummerCokernel

private theorem rational_torsion_finite (source : RationalEllipticCurveSource) :
    Finite (Submodule.torsion ℤ (RationalPoints source)) := by
  obtain ⟨_, parallelogram⟩ :=
    UniversalBSDRationalMordellWeilHeight.rationalNaiveHeight_approx_parallelogram source
  have finite : Finite (AddCommGroup.torsion (RationalPoints source)) :=
    AddCommGroup.finite_torsion_of_descent' parallelogram
  change Finite ((Submodule.torsion ℤ (RationalPoints source)).toAddSubgroup)
  rwa [Submodule.torsion_int]

/-- The actual cofinal Kummer kernel is the image of the entire geometric torsion tower. -/
theorem actual_kummer_completion_kernel (source : RationalEllipticCurveSource) (p : Nat.Primes) :
    LinearMap.range (ambientToCokernelAtLimit (pointEvaluation source) p) =
      LinearMap.ker (cokernelConnectingAtLimit (pointEvaluation source)
        (point_evaluation_injective source) p) := by
  letI := rational_torsion_finite source
  exact cokernel_connecting_limit_kernel _ (point_evaluation_injective source) p

/-- The original Kummer read determines a unique geometric torsion difference of two lifts. -/
theorem actual_kummer_completion_same_read (source : RationalEllipticCurveSource) (p : Nat.Primes)
    (left right : PrimePowerTorsionCompletion (GeometricPoints source ⧸ LinearMap.range (pointEvaluation source)) p)
    (same : cokernelConnectingAtLimit (pointEvaluation source) (point_evaluation_injective source) p left =
      cokernelConnectingAtLimit (pointEvaluation source) (point_evaluation_injective source) p right) :
    ∃! difference : PrimePowerTorsionCompletion (GeometricPoints source) p,
      ambientToCokernelAtLimit (pointEvaluation source) p difference = left - right := by
  letI := rational_torsion_finite source
  have inKernel : left - right ∈ LinearMap.ker
      (cokernelConnectingAtLimit (pointEvaluation source) (point_evaluation_injective source) p) := by
    rw [LinearMap.mem_ker, map_sub, same, sub_self]
  rw [← actual_kummer_completion_kernel source p] at inKernel
  obtain ⟨difference, computes⟩ := inKernel
  refine ⟨difference, computes, fun other reads => ?_⟩
  exact ambient_to_cokernel_limit_injective _ (point_evaluation_injective source) p (reads.trans computes.symm)

end SaturationMonoid.UniversalBSDRationalKummerCokernel
