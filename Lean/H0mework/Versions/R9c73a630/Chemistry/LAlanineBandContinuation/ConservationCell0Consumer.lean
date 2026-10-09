import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.ConservationOrientation
import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell0.ConservationOrientation
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandRegression.ContinuationPaid

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandConservation

open WholeBandActual WholeBandContinuation WholeBandCell0Differential WholeBandCell0Conservation
noncomputable section

theorem cell0_evolving_source_same (p : Cell0Point) : cell0_evolvingJacobian p = evolvingJacobian 0 p.val := rfl
theorem cell0_volume_rate_same (p : Cell0Point) : cell0_signedVolumeRate p = signedVolumeRate 0 p.val := rfl

theorem cell0_determinant_evolution_from_shared : type_of% cell0_evolvingJacobian_determinant_evolution :=
  fun p s => evolvingJacobian_determinant_evolution 0 cell0_source_fields cell0_analytic_bounds p.val p.property s

theorem cell0_time_integral_from_shared : type_of% cell0_actual_time_integral_eq_det_difference :=
  fun p => actual_time_integral_eq_det_difference 0 cell0_source_fields cell0_analytic_bounds p.val p.property

theorem cell0_positive_orientation_from_shared : type_of% cell0_trueJacobian_det_pos :=
  fun p => actualJacobian_det_pos 0 cell0_source_fields cell0_analytic_bounds cell0_positive_reports p.val p.property

end
end LAlanine40K2025.BasinRefinement.WholeBandConservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
