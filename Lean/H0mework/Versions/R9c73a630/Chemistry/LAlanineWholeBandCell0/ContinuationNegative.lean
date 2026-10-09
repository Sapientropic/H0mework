import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell0.ContinuationChain
import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell0.FieldsDirection0
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceRawPath

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Continuation

open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap WholeBandSource WholeBandReplay
open TrueTubeContinuation TrueTubeWholeChecks ContinuousGradient Set
noncomputable section

theorem negative_window_chain (initial : Point) (inside : InRectangle (initialBox 0 0 0) initial) :
    WindowChain 0 initial :=
  window_chain_from_fields 0 WholeBandCell0Fields.direction0_actual_field initial inside

theorem raw_negative_eq_window (initial : Point) (t : ℝ) (time : t ≤ 0) :
    TrueFlowDifferential.rawFlow initial t = windowCurve 0 initial (-t) :=
  LAlanineTrueTube.Signed.full_left _ _ _ time

theorem negative_raw_tubes (initial : Point) (inside : InRectangle (initialBox 0 0 0) initial)
    (i : Step) (t : ℝ) (time : t ∈ Icc 0 (stepSize : ℝ)) :
    InRectangle (tubeBox 0 0 i) (TrueFlowDifferential.rawFlow initial (-(t + stepOffset i))) := by
  rw [raw_negative_eq_window _ _ (by linarith [stepOffset_nonneg i, time.1]), neg_neg]
  exact (negative_window_chain initial inside).tubes i t time

theorem negative_raw_fields (initial : Point) (inside : InRectangle (initialBox 0 0 0) initial)
    (i : Step) (t : ℝ) (time : t ∈ Icc 0 (stepSize : ℝ)) :
    FieldHolds (recordedCallField (tubeCallAt 0 0 i))
      (TrueFlowDifferential.rawFlow initial (-(t + stepOffset i))) := by
  rw [raw_negative_eq_window _ _ (by linarith [stepOffset_nonneg i, time.1]), neg_neg]
  exact (negative_window_chain initial inside).fields i t time

theorem negative_raw_endpoints (initial : Point) (inside : InRectangle (initialBox 0 0 0) initial)
    (i : Step) : InRectangle (endpointBox 0 0 i)
      (TrueFlowDifferential.rawFlow initial (-(stepOffset i + (stepSize : ℝ)))) := by
  have stepPositive : 0 < (stepSize : ℝ) := Rat.cast_pos.mpr (cellArithmetic0 0 i).positive_step
  rw [raw_negative_eq_window _ _ (by linarith [stepOffset_nonneg i]), neg_neg]
  exact (negative_window_chain initial inside).endpoints i

theorem negative_raw_next_initial (initial : Point) (inside : InRectangle (initialBox 0 0 0) initial)
    (i : Fin 15) : InRectangle (initialBox 0 0 i.succ)
      (TrueFlowDifferential.rawFlow initial (-(stepOffset i.castSucc + (stepSize : ℝ)))) :=
  (cellAdjacency0 0 i) ▸ negative_raw_endpoints initial inside i.castSucc

theorem negative_raw_residence (initial : Point) (inside : InRectangle (initialBox 0 0 0) initial)
    (t : ℝ) (time : t ∈ Icc (-(1/2 : ℝ)) 0) : TrueFlowDifferential.rawFlow initial t ∈ sourceCube := by
  rw [raw_negative_eq_window _ _ time.2]
  exact (negative_window_chain initial inside).residence (-t) ⟨by linarith [time.2], by linarith [time.1]⟩

theorem negative_raw_original (initial : Point) (inside : InRectangle (initialBox 0 0 0) initial) :
    IsIntegralCurveOn (TrueFlowDifferential.rawFlow initial) (fun _ => sourceGradient) (Icc (-(1/2 : ℝ)) 0) := by
  intro t ht
  have extended := TrueFlowDifferential.rawFlow_extended initial t ⟨ht.1, ht.2.trans (by norm_num)⟩
  change HasDerivWithinAt (TrueFlowDifferential.rawFlow initial)
    (globalField 1 (TrueFlowDifferential.rawFlow initial t)) (Icc (-(1/2 : ℝ)) (1/2)) t at extended
  have fieldAt : globalField 1 (TrueFlowDifferential.rawFlow initial t) =
      sourceGradient (TrueFlowDifferential.rawFlow initial t) := by
    rw [globalField_eq_original 1 _ (negative_raw_residence initial inside t ht)]
    simp only [TrueTubeTrace.signedGradient, TrueTubeChecks.directions.2, Rat.cast_one, one_smul]
  rw [fieldAt] at extended
  exact extended.mono (Icc_subset_Icc le_rfl (by norm_num))

theorem negative_raw_final (initial : Point) (inside : InRectangle (initialBox 0 0 0) initial) :
    InRectangle (endpointBox 0 0 15) (TrueFlowDifferential.rawFlow initial (-(1/2 : ℝ))) := by
  rw [raw_negative_eq_window _ _ (by norm_num), neg_neg]
  exact (negative_window_chain initial inside).final_endpoint

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Continuation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
