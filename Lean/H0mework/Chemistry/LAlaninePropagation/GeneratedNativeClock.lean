import H0mework.Chemistry.LAlaninePropagation.GeneratedElectronicPropagation
import H0mework.Chemistry.LAlaninePropagation.GeneratedNativeDuration

/-! # The actual molecular source generates its own responding clock -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Propagation.Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Dynamics
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Dynamics.NativeDuration

noncomputable section

def nativeClockStep : ℚ := sourceNativeDuration electronicSource

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem sourceEntryMagnitude_exact :
    sourceEntryMagnitude electronicSource = 578404441888455408 := by
  decide

theorem nativeClockStep_exact :
    nativeClockStep = 15625000000000 / 36212777618028463 := by
  simp only [nativeClockStep, sourceNativeDuration, sourceOperatorBound, sourceEntryMagnitude_exact]
  norm_num

theorem nativeClockStep_positive : 0 < nativeClockStep :=
  sourceNativeDuration_positive electronicSource

theorem nativeElectronicStep_changes (time : ℝ) :
    densityEvolution electronicSource (time + (nativeClockStep : ℝ)) ≠
      densityEvolution electronicSource time :=
  sourceNativeDuration_allTimes_response electronicSource 0 1 firstCommutator_nonzero time

theorem nativeElectronicStep_commutes (time : ℝ) :
    densityEvolution electronicSource (time + (nativeClockStep : ℝ)) =
      propagator electronicSource (nativeClockStep : ℝ) *
        densityEvolution electronicSource time * propagator electronicSource (-(nativeClockStep : ℝ)) := by
  rw [add_comm, densityEvolution_translate]

theorem firstNativeClockTarget_exact :
    (1 : ℚ) + nativeClockStep = 36228402618028463 / 36212777618028463 := by
  rw [nativeClockStep_exact]
  norm_num

end

end LAlanine40K2025.Propagation.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
