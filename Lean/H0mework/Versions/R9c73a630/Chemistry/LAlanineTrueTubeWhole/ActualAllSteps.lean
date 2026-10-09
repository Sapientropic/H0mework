import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.ActualStepAssembly
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.ActualSecondStep
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.MatrixAllFields
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.ChecksSupport
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTube.ActualRealization

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeWholeActual

open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap TrueTubeSource
open TrueTubeWholeSource TrueTubeWholeChecks TrueTubeTrace Set
noncomputable section

theorem actual_initial_field (d : Direction) (i : Step) (x : Point) (inside : InRectangle (initialBox d i) x) :
    FieldHolds (recordedCallField (initialCallAt d i)) x :=
  TrueTubeWholeMatrix.all_actual_call_fields _ x ((initial_call_box d i).symm ▸ inside)

theorem actual_tube_field (d : Direction) (i : Step) (x : Point) (inside : InRectangle (tubeBox d i) x) :
    FieldHolds (recordedCallField (tubeCallAt d i)) x :=
  TrueTubeWholeMatrix.all_actual_call_fields _ x ((tube_call_box d i).symm ▸ inside)

theorem actual_step (d : Direction) (i : Step) : LocalStepLaw d i := by
  by_cases first : i = 0
  · subst i
    intro initial inside
    let sourceInitial : TrueTubeActual.InitialAt d := ⟨initial, inside⟩
    have paid := TrueTubeActual.firstCurve_spec d sourceInitial
    exact ⟨TrueTubeActual.firstCurve d sourceInitial, paid.1, paid.2.1, paid.2.2.1⟩
  · by_cases second : i = 1
    · subst i
      exact actual_second_step d
    · exact step_from_source_fields d i (actual_initial_field d i) (actual_tube_field d i)

end
end LAlanine40K2025.BasinRefinement.TrueTubeWholeActual
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
