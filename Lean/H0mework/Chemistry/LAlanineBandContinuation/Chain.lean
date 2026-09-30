import H0mework.Chemistry.LAlanineBandContinuation.Step
import H0mework.Chemistry.LAlanineBandFlowReplay.Arithmetic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuation

open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap WholeBandSource WholeBandReplay
open TrueTubeContinuation TrueTubeWholeChecks Set
noncomputable section

def DirectionFields (c : FullBandCell) (d : Direction) : Prop := ∀ i : Step, ∀ role : CallRole, ∀ x : Point,
  InRectangle (callBox (callAt c d i role)) x → FieldHolds (recordedCallField (callAt c d i role)) x

structure WindowChain (c : FullBandCell) (d : Direction) (initial : Point) : Prop where
  initials : ∀ i : Step, InRectangle (initialBox c d i) (windowCurve d initial (stepOffset i))
  tubes : ∀ i : Step, ∀ t ∈ Icc 0 (stepSize : ℝ),
    InRectangle (tubeBox c d i) (windowCurve d initial (t + stepOffset i))
  endpoints : ∀ i : Step,
    InRectangle (endpointBox c d i) (windowCurve d initial (stepOffset i + stepSize))
  residence : ∀ t ∈ Icc (0 : ℝ) (1/2), windowCurve d initial t ∈ ContinuousGradient.sourceCube
  original : IsIntegralCurveOn (windowCurve d initial)
    (fun _ => TrueTubeTrace.signedGradient (sign d)) (Icc (0 : ℝ) (1/2))
  fields : ∀ i : Step, ∀ t ∈ Icc 0 (stepSize : ℝ),
    FieldHolds (recordedCallField (tubeCallAt c d i)) (windowCurve d initial (t + stepOffset i))

private theorem initials_from_fields (c : FullBandCell) (d : Direction) (fields : DirectionFields c d)
    (initial : Point) (inside : InRectangle (initialBox c d 0) initial) :
    ∀ i : Step, InRectangle (initialBox c d i) (windowCurve d initial (stepOffset i)) := by
  intro i
  induction i using Fin.induction with
  | zero => simpa only [stepOffset_zero, windowCurve_starts] using inside
  | succ prior ih =>
    have endpoint := (step_on_source_window c d initial prior.castSucc (all_row_arithmetic c d prior.castSucc)
      (fields prior.castSucc .initial) (fields prior.castSucc .tube) ih).2
    rw [endpoint_next_initial c d prior] at endpoint
    rw [stepOffset_succ]
    simpa only [source_step_and_sign.1] using endpoint

/-- The common finite-source consumer has analytic field inputs, never future curves or endpoints. -/
theorem window_chain_from_fields (c : FullBandCell) (d : Direction) (fields : DirectionFields c d)
    (initial : Point) (inside : InRectangle (initialBox c d 0) initial) : WindowChain c d initial := by
  have initials := initials_from_fields c d fields initial inside
  have steps := fun i => step_on_source_window c d initial i (all_row_arithmetic c d i)
    (fields i .initial) (fields i .tube) (initials i)
  have residence (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (1/2)) :
      windowCurve d initial t ∈ ContinuousGradient.sourceCube := by
    obtain ⟨i, hi⟩ := sixteen_intervals_cover t ht
    have localTime : t - stepOffset i ∈ Icc 0 (stepSize : ℝ) := by
      rw [source_step_and_sign.1]
      constructor <;> linarith [hi.1, hi.2]
    have bound := (steps i).1 (t - stepOffset i) localTime
    rw [sub_add_cancel] at bound
    exact WholeBandReplay.tube_in_sourceCube (all_row_arithmetic c d i) _ bound
  refine ⟨initials, fun i => (steps i).1, fun i => (steps i).2, residence, ?_, ?_⟩
  · intro t ht
    simpa only [source_step_and_sign.2] using
      windowCurve_original_at d initial t ht (residence t ht)
  · intro i t ht
    apply fields i .tube
    have join : callBox (tubeCallAt c d i) = tubeBox c d i := funext (all_row_arithmetic c d i).tube_join
    change InRectangle (callBox (tubeCallAt c d i)) _
    rw [join]
    exact (steps i).1 t ht

theorem WindowChain.next_initial {c : FullBandCell} {d : Direction} {initial : Point} (chain : WindowChain c d initial)
    (i : Fin 15) :
    InRectangle (initialBox c d i.succ) (windowCurve d initial (stepOffset i.castSucc + stepSize)) :=
  (endpoint_next_initial c d i) ▸ chain.endpoints i.castSucc

theorem WindowChain.final_endpoint {c : FullBandCell} {d : Direction} {initial : Point} (chain : WindowChain c d initial) :
    InRectangle (endpointBox c d 15) (windowCurve d initial (1/2)) := by
  have final := chain.endpoints 15
  rw [source_step_and_sign.1, stepOffset_last_end] at final
  exact final

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
