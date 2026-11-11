import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Finite.RestrictedKernel
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.FiniteRestriction

open SourceGeneratedActionObservationHistory

universe u

variable {H G : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- Keep every ambient observation in the prefix, with its Hilbert norm. -/
def hilbertPrefix (action : H →L[ℂ] H) (observation : H →L[ℂ] G) (last : ℕ) :
    H →L[ℂ] PiLp 2 (fun _ : Fin (last+1) => G) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (last+1) => G)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => observation.comp (action ^ i.val))

theorem hilbertPrefix_read (action : H →L[ℂ] H) (observation : H →L[ℂ] G)
    (last : ℕ) (v : H) (i : Fin (last+1)) :
    hilbertPrefix action observation last v i = observation ((action ^ i.val) v) := rfl

/-- A finite restriction of a faithful cofinal observer generates a bounded inverse on its
actual Hilbert prefix. The inverse also reads a perturbed prefix with its own operator budget. -/
theorem bounded_prefix_inverse (action : H →L[ℂ] H) (observation : H →L[ℂ] G)
    (source : Submodule ℂ H) [FiniteDimensional ℂ source]
    (faithful : Function.Injective (sourceMap action.toLinearMap observation.toLinearMap)) :
    ∃ last : ℕ, ∃ decode : PiLp 2 (fun _ : Fin (last+1) => G) →L[ℂ] source,
      (∀ x : source, decode (hilbertPrefix action observation last x) = x) ∧
      ∀ (x : source) y, ‖decode y - x‖ ≤
        ‖decode‖ * ‖y - hilbertPrefix action observation last x‖ := by
  obtain ⟨last, paid⟩ := restricted_kernel_attained action.toLinearMap observation.toLinearMap source
  let input := (hilbertPrefix action observation last).comp source.subtypeL
  have exactInput : Function.Injective input := by
    intro x y same
    apply sub_eq_zero.mp
    have fibre : x-y ∈ LinearMap.ker
        ((prefixEvaluator action.toLinearMap observation.toLinearMap last).comp source.subtype) := by
      change prefixEvaluator action.toLinearMap observation.toLinearMap last ((x-y : source) : H) = 0
      rw [Submodule.coe_sub, map_sub, sub_eq_zero]
      funext i
      have read := congrArg (fun field : PiLp 2 (fun _ : Fin (last+1) => G) => field i) same
      change hilbertPrefix action observation last (x : H) i =
        hilbertPrefix action observation last (y : H) i at read
      rw [hilbertPrefix_read, hilbertPrefix_read] at read
      change observation ((action.toLinearMap ^ i.val) (x : H)) =
        observation ((action.toLinearMap ^ i.val) (y : H))
      rw [← ContinuousLinearMap.toLinearMap_pow]
      exact read
    rw [paid] at fibre
    change sourceMap action.toLinearMap observation.toLinearMap ((x-y : source) : H) = 0 at fibre
    apply Subtype.ext
    change ((x-y : source) : H) = 0
    apply faithful
    rwa [map_zero]
  let image := LinearMap.range input.toLinearMap
  let fit : source ≃ₗ[ℂ] image := LinearEquiv.ofInjective input.toLinearMap exactInput
  have : FiniteDimensional ℂ image := LinearMap.finiteDimensional_range input.toLinearMap
  have : CompleteSpace image := FiniteDimensional.complete ℂ image
  let decode := fit.symm.toLinearMap.toContinuousLinearMap.comp image.orthogonalProjectionOnto
  have exactRead (x : source) : decode (input x) = x := by
    change fit.symm (image.orthogonalProjectionOnto (↑(fit x))) = x
    rw [image.orthogonalProjectionOnto_mem_subspace_eq_self, fit.symm_apply_apply]
  refine ⟨last, decode, exactRead, ?_⟩
  intro x y
  have bound := decode.le_opNorm (y - input x)
  rwa [map_sub, exactRead] at bound

end SourceGeneratedActionObservationHistory.FiniteRestriction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
