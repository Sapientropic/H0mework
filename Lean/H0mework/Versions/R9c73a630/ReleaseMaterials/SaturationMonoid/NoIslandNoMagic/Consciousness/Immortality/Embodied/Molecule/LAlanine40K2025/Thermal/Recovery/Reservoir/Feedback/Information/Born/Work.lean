import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.Recovery
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.Marginal

/-! The optimal pointer readback's actual mean change is the original feedback work. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Born

open Collision

noncomputable section

def pointerMean (observable : Current.FullJoint) (hermitian : observable.IsHermitian) (current : Live.State) : ℝ :=
  zeroRead current.joint * (bestDecoder observable hermitian current 0).re +
    oneRead current.joint * (bestDecoder observable hermitian current 1).re

theorem pointerMean_energy (observable : Current.FullJoint) (hermitian : observable.IsHermitian)
    (current : Live.State) : pointerMean observable hermitian current = energy observable (bodyRead current.joint) := by
  have mean := bestDecoder_mean observable hermitian current
  rw [Fin.sum_univ_two, pointer_zero_read, pointer_one_read] at mean
  exact mean

theorem actual_optimal_mean_work :
    pointerMean Physical.baselineHamiltonian oldBaseline_hermitian firstState -
      pointerMean Physical.baselineHamiltonian oldBaseline_hermitian receivedState = responseWork receivedState := by
  rw [pointerMean_energy, pointerMean_energy]
  exact (responseWork_body receivedState).symm

theorem actual_optimal_mean_net_account :
    (Live.freeEnergy firstState - Live.freeEnergy receivedState) +
      (Live.entropyProduction firstState - Live.entropyProduction receivedState) =
        pointerMean Physical.baselineHamiltonian oldBaseline_hermitian firstState -
          pointerMean Physical.baselineHamiltonian oldBaseline_hermitian receivedState :=
  (respondNext_netAccount receivedState).trans actual_optimal_mean_work.symm

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Born
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
