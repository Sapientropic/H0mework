import H0mework.Chemistry.LAlanineTrueTubeWhole.SourceReuse
import H0mework.Chemistry.LAlanineTrueTube.ChecksReadout

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeWholeChecks

open TrueTubeSource TrueTubeWholeSource TrueTubeTrace SourceGaussianModel SourceSignedEvaluator IntervalParameterMap
noncomputable section

def signedTubeGradient (d : Direction) (i : Step) : VectorPair :=
  signedGradientPair (sign d) (recordedCallField (tubeCallAt d i))
def signedInitialGradient (d : Direction) (i : Step) : VectorPair :=
  signedGradientPair (sign d) (recordedCallField (initialCallAt d i))
def rowAcceleration (d : Direction) (i : Step) : VectorPair :=
  accelerationPair (recordedCallField (tubeCallAt d i))

def picardImage (d : Direction) (i : Step) : VectorPair :=
  vectorAdd (initialBox d i) (vectorScale (0, stepSize) (signedTubeGradient d i))
def eulerEndpoint (d : Direction) (i : Step) : VectorPair :=
  vectorAdd (initialBox d i) (vectorScale (point stepSize) (signedTubeGradient d i))
def secondEndpoint (d : Direction) (i : Step) : VectorPair :=
  vectorAdd (vectorAdd (initialBox d i) (vectorScale (point stepSize) (signedInitialGradient d i)))
    (vectorScale (point (stepSize ^ 2 / 2)) (rowAcceleration d i))
def intersectEndpoints (d : Direction) (i : Step) : VectorPair := fun axis =>
  (max (eulerEndpoint d i axis).1 (secondEndpoint d i axis).1,
   min (eulerEndpoint d i axis).2 (secondEndpoint d i axis).2)

theorem step_one_selfmap : ∀ d : Direction, ∀ axis : Fin 3,
    (tubeBox d 1 axis).1 ≤ (picardImage d 1 axis).1 ∧
      (picardImage d 1 axis).2 ≤ (tubeBox d 1 axis).2 := by decide +kernel

theorem step_one_endpoint : ∀ d : Direction, ∀ axis : Fin 3,
    intersectEndpoints d 1 axis = endpointBox d 1 axis := by decide +kernel

theorem zero_initial_field (d : Direction) :
    recordedCallField (initialCallAt d 0) = recordedField 0 := by
  fin_cases d
  · exact prepaid_field 0
  · exact prepaid_field 1

theorem zero_tube_field (d : Direction) :
    recordedCallField (tubeCallAt d 0) = recordedField (firstTubeField d) := by
  fin_cases d
  · exact prepaid_field 2
  · exact prepaid_field 3

theorem zero_initial_gradient (d : Direction) :
    signedInitialGradient d 0 = TrueTubeChecks.signedInitialGradient d := by
  unfold signedInitialGradient TrueTubeChecks.signedInitialGradient
  rw [zero_initial_field]
theorem zero_tube_gradient (d : Direction) :
    signedTubeGradient d 0 = TrueTubeChecks.signedTubeGradient d := by
  unfold signedTubeGradient TrueTubeChecks.signedTubeGradient
  rw [zero_tube_field]
theorem zero_acceleration (d : Direction) :
    rowAcceleration d 0 = accelerationPair (recordedField (firstTubeField d)) := by
  unfold rowAcceleration
  rw [zero_tube_field]
theorem zero_picard (d : Direction) : picardImage d 0 = TrueTubeChecks.picardImage d := by
  simp only [picardImage, TrueTubeChecks.picardImage, zero_tube_gradient]
theorem zero_euler (d : Direction) : eulerEndpoint d 0 = TrueTubeChecks.eulerEndpoint d := by
  simp only [eulerEndpoint, TrueTubeChecks.eulerEndpoint, zero_tube_gradient]
theorem zero_second (d : Direction) : secondEndpoint d 0 = TrueTubeChecks.secondEndpoint d := by
  simp only [secondEndpoint, TrueTubeChecks.secondEndpoint, zero_initial_gradient, zero_acceleration]
theorem zero_meet (d : Direction) : intersectEndpoints d 0 = TrueTubeChecks.intersectEndpoints d := by
  funext axis
  change (max (eulerEndpoint d 0 axis).1 (secondEndpoint d 0 axis).1,
    min (eulerEndpoint d 0 axis).2 (secondEndpoint d 0 axis).2) = _
  rw [zero_euler, zero_second]
  rfl

theorem remaining_selfmaps : ∀ d : Direction, ∀ i : Fin 15, ∀ axis : Fin 3,
    (tubeBox d i.succ axis).1 ≤ (picardImage d i.succ axis).1 ∧
      (picardImage d i.succ axis).2 ≤ (tubeBox d i.succ axis).2 := by decide +kernel

theorem all_picard_selfmaps (d : Direction) (i : Step) : ∀ axis : Fin 3,
    (tubeBox d i axis).1 ≤ (picardImage d i axis).1 ∧
      (picardImage d i axis).2 ≤ (tubeBox d i axis).2 := by
  refine Fin.cases ?_ (remaining_selfmaps d) i
  intro axis
  rw [zero_picard]
  exact TrueTubeChecks.first_picard_selfmap d axis

theorem remaining_meets : ∀ d : Direction, ∀ i : Fin 15, ∀ axis : Fin 3,
    intersectEndpoints d i.succ axis = endpointBox d i.succ axis := by decide +kernel

theorem all_meets (d : Direction) (i : Step) : ∀ axis : Fin 3,
    intersectEndpoints d i axis = endpointBox d i axis := by
  refine Fin.cases ?_ (remaining_meets d) i
  intro axis
  rw [zero_meet]
  exact TrueTubeChecks.first_endpoint_recomputed d axis

theorem second_strictly_selected : ∀ d : Direction, ∀ i : Step, ∀ axis : Fin 3,
    (eulerEndpoint d i axis).1 < (secondEndpoint d i axis).1 ∧
      (secondEndpoint d i axis).2 < (eulerEndpoint d i axis).2 := by decide +kernel

theorem second_endpoint_eq (d : Direction) (i : Step) : secondEndpoint d i = endpointBox d i := by
  funext axis
  rw [← all_meets d i axis]
  simp only [intersectEndpoints, max_eq_right (second_strictly_selected d i axis).1.le,
    min_eq_right (second_strictly_selected d i axis).2.le]

theorem signed_tube_ordered : ∀ d : Direction, ∀ i : Step, ∀ axis : Fin 3,
    (signedTubeGradient d i axis).1 ≤ (signedTubeGradient d i axis).2 := by decide +kernel

theorem acceleration_ordered : ∀ d : Direction, ∀ i : Step, ∀ axis : Fin 3,
    (rowAcceleration d i axis).1 ≤ (rowAcceleration d i axis).2 := by decide +kernel

end
end LAlanine40K2025.BasinRefinement.TrueTubeWholeChecks
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
