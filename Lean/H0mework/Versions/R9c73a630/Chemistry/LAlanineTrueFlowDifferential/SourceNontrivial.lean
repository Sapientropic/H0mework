import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceTimeColumn
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceEvolution

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferential

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel ContinuousGradient TrueTubeActual TrueTubeWholeActual WholeCellPartition
noncomputable section

theorem parameter_domain_nonempty : Set.Nonempty fullDomain := ⟨fullLower, source_corner_inside⟩

theorem sourceResponse_ne_zero (p : BandPoint) : sourceResponse p ≠ 0 := by
  intro erased
  have preserved := sourceResponse_starts p (Pi.single (0 : Fin 3) 1)
  have axis := congrArg (fun x : Space => x 0) preserved
  rw [erased] at axis
  norm_num at axis

theorem time_column_positive_at_seed (p : BandPoint) (atSeed : p.val 2 = 0) :
    0 < trueJacobian p (Pi.single 2 1) 2 := by
  rw [trueJacobian_time_column, trueParameterMap_is_actual, atSeed, fullFlow_starts]
  exact TrueTubeMatrix.source_gradient_third_positive 0 _
    ((TrueTubeChecks.initial_field_eq 0).symm ▸ actual_seed_initial 0 p.val p.property)

theorem trueJacobian_ne_zero_at_seed (p : BandPoint) (atSeed : p.val 2 = 0) :
    trueJacobian p ≠ 0 := by
  intro erased
  have positive := time_column_positive_at_seed p atSeed
  rw [erased] at positive
  exact lt_irrefl (0 : ℝ) positive

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
