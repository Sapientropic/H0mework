import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentKernel.Noetherian
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDTate.Clay.Analytic.RationalKummerCokernel.Completion

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.UniversalBSDRationalKummerCokernel

open CategoryTheory CategoryTheory.Limits
open UniversalBSDGeometricGalois UniversalBSDRationalKummerCohomology
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion

open private point_evaluation_injective stageKummer kummer_kernel from
  H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDTate.Clay.Analytic.RationalKummerCokernel

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
  let : Finite (Submodule.torsion ℤ (RationalPoints source)) := rational_torsion_finite source
  exact cokernel_connecting_limit_kernel _ (point_evaluation_injective source) p

private theorem same_read_fibre (source : RationalEllipticCurveSource) (p : Nat.Primes)
    (left right : PrimePowerTorsionCompletion (GeometricPoints source ⧸ LinearMap.range (pointEvaluation source)) p)
    (same : cokernelConnectingAtLimit (pointEvaluation source) (point_evaluation_injective source) p left =
      cokernelConnectingAtLimit (pointEvaluation source) (point_evaluation_injective source) p right) :
    ∃! difference : PrimePowerTorsionCompletion (GeometricPoints source) p,
      ambientToCokernelAtLimit (pointEvaluation source) p difference = left - right := by
  let : Finite (Submodule.torsion ℤ (RationalPoints source)) := rational_torsion_finite source
  have inKernel : left - right ∈ LinearMap.ker
      (cokernelConnectingAtLimit (pointEvaluation source) (point_evaluation_injective source) p) := by
    rw [LinearMap.mem_ker, map_sub, same, sub_self]
  rw [← actual_kummer_completion_kernel source p] at inKernel
  obtain ⟨difference, computes⟩ := inKernel
  refine ⟨difference, computes, fun other reads => ?_⟩
  exact ambient_to_cokernel_limit_injective _ (point_evaluation_injective source) p (reads.trans computes.symm)

/-- All original Kummer classes agree exactly along a unique coherent geometric torsion difference. -/
theorem actual_kummer_completion_class_fibre (source : RationalEllipticCurveSource) (p : Nat.Primes)
    (left right : PrimePowerTorsionCompletion (GeometricPoints source ⧸ LinearMap.range (pointEvaluation source)) p) :
    (∀ j, cokernelKummer source p j
        ((torsionCompletionRestriction (GeometricPoints source ⧸ LinearMap.range (pointEvaluation source)) p j).hom left) =
      cokernelKummer source p j
        ((torsionCompletionRestriction (GeometricPoints source ⧸ LinearMap.range (pointEvaluation source)) p j).hom right)) ↔
    ∃! difference : PrimePowerTorsionCompletion (GeometricPoints source) p,
      ambientToCokernelAtLimit (pointEvaluation source) p difference = left - right := by
  let evaluate := pointEvaluation source
  let read := cokernelConnectingAtLimit evaluate (point_evaluation_injective source) p
  let C := GeometricPoints source ⧸ LinearMap.range evaluate
  have stage (value : PrimePowerTorsionCompletion C p) (j : Nat) :
      cokernelKummer source p j ((torsionCompletionRestriction C p j).hom value) =
        stageKummer source p j ((restriction (L := RationalPoints source) p j).hom (read value)) :=
    congrArg (stageKummer source p j)
      (cokernel_connecting_limit_restriction evaluate (point_evaluation_injective source) p j value).symm
  constructor
  · intro equal
    apply same_read_fibre source p left right
    apply Concrete.limit_ext (tower (L := RationalPoints source) p)
    rintro ⟨j⟩
    have injective : Function.Injective (stageKummer source p j) :=
      LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' _ _ (kummer_kernel source p j))
    exact injective ((stage left j).symm.trans ((equal j).trans (stage right j)))
  · rintro ⟨difference, written, _⟩ j
    have silent : left - right ∈ LinearMap.ker read := by
      rw [show LinearMap.ker read = _ from (actual_kummer_completion_kernel source p).symm]
      exact ⟨difference, written⟩
    have same : read left = read right := sub_eq_zero.mp
      ((map_sub read left right).symm.trans (LinearMap.mem_ker.mp silent))
    exact (stage left j).trans
      ((congrArg (fun value => stageKummer source p j ((restriction p j).hom value)) same).trans (stage right j).symm)

end SaturationMonoid.UniversalBSDRationalKummerCokernel
