import H0mework.Chemistry.LAlanineTrueTubeWhole.ActualStepAssembly
import H0mework.Chemistry.LAlanineTrueTubeWhole.ChecksSupport
import H0mework.Chemistry.LAlanineBandCall002.TubeMatrixComplete
import H0mework.Chemistry.LAlanineBandCall003.TubeMatrixComplete
import H0mework.Chemistry.LAlanineBandCall034.TubeMatrixComplete
import H0mework.Chemistry.LAlanineBandCall035.TubeMatrixComplete
import H0mework.Chemistry.LAlanineTrueTube.ActualRealization

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeWholeActual

open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap TrueTubeSource
open TrueTubeWholeSource TrueTubeWholeChecks TrueTubeActual Set
noncomputable section

theorem second_initial_field (d : Direction) (x : Point) (inside : InRectangle (initialBox d 1) x) :
    FieldHolds (recordedCallField (initialCallAt d 1)) x := by
  have source := (initial_call_box d 1).symm ▸ inside
  fin_cases d
  · exact TrueTubeWholeMatrix.C2.actual_field x source
  · exact TrueTubeWholeMatrix.C34.actual_field x source

theorem second_tube_field (d : Direction) (x : Point) (inside : InRectangle (tubeBox d 1) x) :
    FieldHolds (recordedCallField (tubeCallAt d 1)) x := by
  have source := (tube_call_box d 1).symm ▸ inside
  fin_cases d
  · exact TrueTubeWholeMatrix.C3.actual_field x source
  · exact TrueTubeWholeMatrix.C35.actual_field x source

theorem actual_second_step (d : Direction) : LocalStepLaw d 1 :=
  step_from_source_fields d 1 (second_initial_field d) (second_tube_field d)

theorem installed_target_reenters (d : Direction) (initial : InitialAt d) :
    ∃ curve : ℝ → Point, curve 0 = (firstTarget d initial).val ∧
      (∀ t ∈ Icc 0 (stepSize : ℝ),
        HasDerivWithinAt curve (TrueTubeTrace.signedGradient (sign d) (curve t))
          (Icc 0 (stepSize : ℝ)) t ∧ InRectangle (tubeBox d 1) (curve t)) ∧
      InRectangle (endpointBox d 1) (curve stepSize) ∧
      InRectangle (initialBox d 2) (curve stepSize) := by
  obtain ⟨curve, starts, evolves, endpoint⟩ := actual_second_step d _ (firstTarget d initial).property
  refine ⟨curve, starts, evolves, endpoint, ?_⟩
  have next : endpointBox d 1 = initialBox d 2 := by
    convert TrueTubeChecks.endpoint_next_initial d (1 : Fin 15) using 1 <;> rfl
  rw [← next]
  exact endpoint

end
end LAlanine40K2025.BasinRefinement.TrueTubeWholeActual
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
