import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ResponseCountingLimit
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.JointCounting

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.ResponseCounting

open Complex Filter MeasureTheory
open scoped Topology InnerProductSpace
noncomputable section

theorem joint_pairing_tendsto (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (side : Bool) :
    Tendsto (fun N : ℕ => inner ℂ (JointCounting.value coordinate zero) (finite side N)) atTop
      (𝓝 (inner ℂ (JointCounting.value coordinate zero) (value side))) :=
  ((innerSL ℂ (JointCounting.value coordinate zero)).continuous.tendsto _).comp (finite_tendsto side)

/-- The same finite independent adjoint reads the original joint output after the full forward source action. -/
theorem joint_forward_pairing (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (side : Bool) (N : ℕ) :
    inner ℂ (FiniteForcing.source N (JointCounting.value coordinate zero))
      (burnolQuarterZeroExtension (ResponseProfile.state side : BurnolQuarterIntervalL2)) =
        inner ℂ (JointCounting.value coordinate zero) (finite side N) :=
  CountingDual.source_pairing N _ _

theorem joint_forward_pairing_tendsto (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (side : Bool) :
    Tendsto (fun N : ℕ => inner ℂ (FiniteForcing.source N (JointCounting.value coordinate zero))
      (burnolQuarterZeroExtension (ResponseProfile.state side : BurnolQuarterIntervalL2))) atTop
        (𝓝 (inner ℂ (JointCounting.value coordinate zero) (value side))) := by
  exact (joint_pairing_tendsto coordinate zero side).congr'
    (Eventually.of_forall (fun N => (joint_forward_pairing coordinate zero side N).symm))

end
end OriginalRieszFinitePairing.CoPoisson.Ward.ResponseCounting
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
