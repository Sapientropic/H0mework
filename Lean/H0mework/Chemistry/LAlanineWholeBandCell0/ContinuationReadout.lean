import H0mework.Chemistry.LAlanineWholeBandCell0.ContinuationNegative
import H0mework.Chemistry.LAlanineBandFlow.SeedEnclosure
import H0mework.Chemistry.LAlanineBandFlow.ActualCanonical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Continuation

open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap WholeBandSource WholeBandReplay
open WholeBandGeometry TrueTubeContinuation TrueTubeWholeChecks Set
noncomputable section

theorem negative_elapsed_start (i : Step) : (elapsedStart 0 0 i : ℝ) = -stepOffset i := by
  have value : elapsedStart 0 0 i = sign 0 * (i.val : ℚ) * stepSize := (cellArithmetic0 0 i).time_start
  rw [value]
  simp only [Rat.cast_mul, Rat.cast_natCast, source_step_and_sign.2, TrueTubeChecks.directions.1,
    Rat.cast_neg, neg_one_mul, stepOffset, source_step_and_sign.1]
  ring

theorem negative_elapsed_stop (i : Step) :
    (elapsedStop 0 0 i : ℝ) = -(stepOffset i + (stepSize : ℝ)) := by
  have value : elapsedStop 0 0 i = sign 0 * ((i.val : ℚ) + 1) * stepSize := (cellArithmetic0 0 i).time_stop
  rw [value]
  simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_natCast, source_step_and_sign.2, TrueTubeChecks.directions.1,
    Rat.cast_neg, Rat.cast_one, neg_one_mul, stepOffset, source_step_and_sign.1]
  ring

theorem negative_source_endpoints (p : WholeBandActual.Cell0Point) (i : Step) :
    InRectangle (endpointBox 0 0 i)
      (TrueFlowDifferential.rawFlow (cellSeed 0 p.val) (elapsedStop 0 0 i)) := by
  rw [negative_elapsed_stop]
  exact negative_raw_endpoints _ (WholeBandSeed.cell_seed_in_initial 0 p.val p.property) i

theorem negative_source_next_initial (p : WholeBandActual.Cell0Point) (i : Fin 15) :
    InRectangle (initialBox 0 0 i.succ)
      (TrueFlowDifferential.rawFlow (cellSeed 0 p.val) (elapsedStop 0 0 i.castSucc)) :=
  (cellAdjacency0 0 i) ▸ negative_source_endpoints p i.castSucc

theorem negative_source_initials (p : WholeBandActual.Cell0Point) (i : Step) :
    InRectangle (initialBox 0 0 i)
      (TrueFlowDifferential.rawFlow (cellSeed 0 p.val) (elapsedStart 0 0 i)) := by
  rw [negative_elapsed_start, raw_negative_eq_window _ _ (neg_nonpos.mpr (stepOffset_nonneg i)), neg_neg]
  exact (negative_window_chain _ (WholeBandSeed.cell_seed_in_initial 0 p.val p.property)).initials i

theorem cell0_negative_original (p : WholeBandActual.Cell0Point) :
    IsIntegralCurveOn (TrueFlowDifferential.rawFlow (cellSeed 0 p.val))
      (fun _ => ContinuousGradient.sourceGradient) (Icc (-(1/2 : ℝ)) 0) :=
  negative_raw_original _ (WholeBandSeed.cell_seed_in_initial 0 p.val p.property)

theorem cell0_negative_sourceCube (p : WholeBandActual.Cell0Point) (t : ℝ)
    (time : t ∈ Icc (-(1/2 : ℝ)) 0) :
    TrueFlowDifferential.rawFlow (cellSeed 0 p.val) t ∈ ContinuousGradient.sourceCube :=
  negative_raw_residence _ (WholeBandSeed.cell_seed_in_initial 0 p.val p.property) t time

theorem cell0_negative_fields (p : WholeBandActual.Cell0Point) (i : Step) (t : ℝ)
    (time : t ∈ Icc 0 (stepSize : ℝ)) :
    FieldHolds (recordedCallField (tubeCallAt 0 0 i))
      (TrueFlowDifferential.rawFlow (cellSeed 0 p.val) (-(t + stepOffset i))) :=
  negative_raw_fields _ (WholeBandSeed.cell_seed_in_initial 0 p.val p.property) i t time

theorem cell0_negative_final (p : WholeBandActual.Cell0Point) :
    InRectangle (endpointBox 0 0 15) (TrueFlowDifferential.rawFlow (cellSeed 0 p.val) (-(1/2 : ℝ))) :=
  negative_raw_final _ (WholeBandSeed.cell_seed_in_initial 0 p.val p.property)

theorem negative_agrees_with_first (p : WholeBandActual.Cell0Point) :
    EqOn (WholeBandActual.fullFlow p) (TrueFlowDifferential.rawFlow (cellSeed 0 p.val))
      (Icc (-(stepSize : ℝ)) 0) := by
  intro t ht
  exact WholeBandActual.fullFlow_eq_sourceRaw p
    ⟨ht.1, ht.2.trans (Rat.cast_pos.mpr (cellArithmetic0 0 0).positive_step).le⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Continuation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
