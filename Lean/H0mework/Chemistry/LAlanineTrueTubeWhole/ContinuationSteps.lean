import H0mework.Chemistry.LAlanineTrueTubeWhole.ActualStepAssembly
import H0mework.Chemistry.LAlanineTrueTubeWhole.ContinuationWindow
import H0mework.Chemistry.LAlanineTrueTubeWhole.ChecksTiming
import H0mework.Chemistry.LAlanineTrueTubeWhole.ChecksSupport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeContinuation

open SourceGaussianModel SourceSignedEvaluator TrueTubeSource TrueTubeTrace ContinuousGradient
open TrueTubeWholeChecks TrueTubeWholeActual Set
noncomputable section

theorem window_step_from_local (d : Direction) (initial : Point) (i : Step) (localLaw : LocalStepLaw d i)
    (atInitial : InRectangle (initialBox d i) (windowCurve d initial (stepOffset i))) :
    (∀ t ∈ Icc 0 (stepSize : ℝ), InRectangle (tubeBox d i) (windowCurve d initial (t + stepOffset i))) ∧
      InRectangle (endpointBox d i) (windowCurve d initial (stepOffset i + stepSize)) := by
  obtain ⟨curve, starts, evolves, endpoint⟩ := localLaw _ atInitial
  have identification := windowCurve_local_identification d initial curve (stepOffset i) stepSize
    (stepOffset_nonneg i) (stepOffset_end_le i)
    (fun t ht => (evolves t ht).1)
    (fun t ht => tube_in_sourceCube d i _ (evolves t ht).2) starts
  constructor
  · intro t ht
    have same : curve t = windowCurve d initial (t + stepOffset i) := identification ht
    rw [← same]
    exact (evolves t ht).2
  · have he := identification (show (stepSize : ℝ) ∈ Icc 0 (stepSize : ℝ) from
      ⟨Rat.cast_nonneg.mpr TrueTubeChecks.step_positive.le, le_rfl⟩)
    change curve stepSize = windowCurve d initial ((stepSize : ℝ) + stepOffset i) at he
    rw [add_comm (stepOffset i), ← he]
    exact endpoint

theorem window_all_initials (d : Direction) (initial : Point)
    (inside : InRectangle (initialBox d 0) initial) (localLaws : ∀ i, LocalStepLaw d i) :
    ∀ i : Step, InRectangle (initialBox d i) (windowCurve d initial (stepOffset i)) := by
  intro i
  induction i using Fin.induction with
  | zero => simpa only [stepOffset_zero, windowCurve_starts] using inside
  | succ prior ih =>
    have endpoint := (window_step_from_local d initial prior.castSucc (localLaws prior.castSucc) ih).2
    rw [TrueTubeChecks.endpoint_next_initial d prior] at endpoint
    rw [stepOffset_succ]
    exact endpoint

theorem window_all_tubes (d : Direction) (initial : Point)
    (inside : InRectangle (initialBox d 0) initial) (localLaws : ∀ i, LocalStepLaw d i) :
    ∀ i : Step, ∀ t ∈ Icc 0 (stepSize : ℝ),
      InRectangle (tubeBox d i) (windowCurve d initial (t + stepOffset i)) :=
  fun i => (window_step_from_local d initial i (localLaws i) (window_all_initials d initial inside localLaws i)).1

theorem window_all_endpoints (d : Direction) (initial : Point)
    (inside : InRectangle (initialBox d 0) initial) (localLaws : ∀ i, LocalStepLaw d i) :
    ∀ i : Step, InRectangle (endpointBox d i) (windowCurve d initial (stepOffset i + stepSize)) :=
  fun i => (window_step_from_local d initial i (localLaws i) (window_all_initials d initial inside localLaws i)).2

theorem window_stays_source (d : Direction) (initial : Point)
    (inside : InRectangle (initialBox d 0) initial) (localLaws : ∀ i, LocalStepLaw d i)
    (t : ℝ) (time : t ∈ Icc (0 : ℝ) (1 / 2)) : windowCurve d initial t ∈ sourceCube := by
  obtain ⟨i, hi⟩ := sixteen_intervals_cover t time
  have localTime : t - stepOffset i ∈ Icc 0 (stepSize : ℝ) := by constructor <;> linarith [hi.1, hi.2]
  have bounded := window_all_tubes d initial inside localLaws i (t - stepOffset i) localTime
  rw [sub_add_cancel] at bounded
  exact tube_in_sourceCube d i _ bounded

theorem window_is_original_flow (d : Direction) (initial : Point)
    (inside : InRectangle (initialBox d 0) initial) (localLaws : ∀ i, LocalStepLaw d i) :
    IsIntegralCurveOn (windowCurve d initial) (fun _ => signedGradient (sign d)) (Icc (0 : ℝ) (1 / 2)) :=
  fun t ht => windowCurve_original_at d initial t ht (window_stays_source d initial inside localLaws t ht)

theorem window_final_endpoint (d : Direction) (initial : Point)
    (inside : InRectangle (initialBox d 0) initial) (localLaws : ∀ i, LocalStepLaw d i) :
    InRectangle (endpointBox d 15) (windowCurve d initial (1 / 2)) := by
  have final := window_all_endpoints d initial inside localLaws 15
  rwa [stepOffset_last_end] at final

end
end LAlanine40K2025.BasinRefinement.TrueTubeContinuation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
