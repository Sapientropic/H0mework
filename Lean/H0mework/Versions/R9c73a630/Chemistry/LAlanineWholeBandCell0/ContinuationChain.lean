import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.Chain
import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell0.ContinuationStep
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.BlocksCell00

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Continuation

open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap WholeBandSource WholeBandReplay
open TrueTubeContinuation TrueTubeWholeChecks Set
noncomputable section

def DirectionFields (d : Direction) : Prop := ∀ i : Step, ∀ role : CallRole, ∀ x : Point,
  InRectangle (callBox (callAt 0 d i role)) x → FieldHolds (recordedCallField (callAt 0 d i role)) x

structure WindowChain (d : Direction) (initial : Point) : Prop where
  initials : ∀ i : Step, InRectangle (initialBox 0 d i) (windowCurve d initial (stepOffset i))
  tubes : ∀ i : Step, ∀ t ∈ Icc 0 (stepSize : ℝ),
    InRectangle (tubeBox 0 d i) (windowCurve d initial (t + stepOffset i))
  endpoints : ∀ i : Step,
    InRectangle (endpointBox 0 d i) (windowCurve d initial (stepOffset i + stepSize))
  residence : ∀ t ∈ Icc (0 : ℝ) (1/2), windowCurve d initial t ∈ ContinuousGradient.sourceCube
  original : IsIntegralCurveOn (windowCurve d initial)
    (fun _ => TrueTubeTrace.signedGradient (sign d)) (Icc (0 : ℝ) (1/2))
  fields : ∀ i : Step, ∀ t ∈ Icc 0 (stepSize : ℝ),
    FieldHolds (recordedCallField (tubeCallAt 0 d i)) (windowCurve d initial (t + stepOffset i))

/-- The common finite-source consumer has analytic field inputs, never future curves or endpoints. -/
theorem window_chain_from_fields (d : Direction) (fields : DirectionFields d)
    (initial : Point) (inside : InRectangle (initialBox 0 d 0) initial) : WindowChain d initial := by
  have generated := WholeBandContinuation.window_chain_from_fields 0 d fields initial inside
  exact ⟨generated.initials, generated.tubes, generated.endpoints,
    generated.residence, generated.original, generated.fields⟩

theorem WindowChain.next_initial {d : Direction} {initial : Point} (chain : WindowChain d initial)
    (i : Fin 15) :
    InRectangle (initialBox 0 d i.succ) (windowCurve d initial (stepOffset i.castSucc + stepSize)) :=
  (cellAdjacency0 d i) ▸ chain.endpoints i.castSucc

theorem WindowChain.final_endpoint {d : Direction} {initial : Point} (chain : WindowChain d initial) :
    InRectangle (endpointBox 0 d 15) (windowCurve d initial (1/2)) := by
  have final := chain.endpoints 15
  rw [source_step_and_sign.1, stepOffset_last_end] at final
  exact final

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Continuation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
