import H0mework.Chemistry.LAlanineBandContinuation.Chain
import H0mework.Chemistry.LAlanineTrueFlowDifferential.SourceRawPath
import H0mework.Chemistry.LAlanineBandFlow.SeedEnclosure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuation

open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap WholeBandSource WholeBandReplay
open WholeBandGeometry TrueTubeContinuation TrueTubeWholeChecks TrueFlowDifferential ContinuousGradient Set
noncomputable section

private theorem sign_zero : (sign 0 : ℝ) = -1 := by
  norm_num [source_step_and_sign.2, TrueTubeChecks.directions.1]

private theorem sign_one : (sign 1 : ℝ) = 1 := by
  norm_num [source_step_and_sign.2, TrueTubeChecks.directions.2]

theorem raw_signed_eq_window (d : Direction) (initial : Point) (t : ℝ) (time : 0 ≤ t) :
    rawFlow initial ((sign d : ℝ) * t) = windowCurve d initial t := by
  fin_cases d
  · change rawFlow initial ((sign 0 : ℝ) * t) = windowCurve 0 initial t
    rw [sign_zero, neg_one_mul]
    change LAlanineTrueTube.Signed.full _ _ (-t) = _
    rw [LAlanineTrueTube.Signed.full_left _ _ _ (neg_nonpos.mpr time), neg_neg]
  · change rawFlow initial ((sign 1 : ℝ) * t) = windowCurve 1 initial t
    rw [sign_one, one_mul]
    apply LAlanineTrueTube.Signed.full_right
    · rw [windowCurve_starts, windowCurve_starts]
    · exact time

theorem seed_in_direction_initial (c : FullBandCell) (d : Direction) (p : Point)
    (inside : p ∈ cellDomain c) : InRectangle (initialBox c d 0) (cellSeed c p) := by
  have source := WholeBandSeed.cell_seed_in_initial c p inside
  fin_cases d
  · exact source
  · exact common_initial c ▸ source

theorem source_window_chain (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (p : Point) (inside : p ∈ cellDomain c) (d : Direction) : WindowChain c d (cellSeed c p) :=
  window_chain_from_fields c d (fields d) _ (seed_in_direction_initial c d p inside)

theorem elapsed_start_signed (c : FullBandCell) (d : Direction) (i : Step) :
    (elapsedStart c d i : ℝ) = (sign d : ℝ) * stepOffset i := by
  have value : elapsedStart c d i = sign d * (i.val : ℚ) * stepSize :=
    (all_row_arithmetic c d i).time_start
  rw [value]
  simp only [Rat.cast_mul, Rat.cast_natCast, stepOffset, source_step_and_sign.1]
  ring

theorem elapsed_stop_signed (c : FullBandCell) (d : Direction) (i : Step) :
    (elapsedStop c d i : ℝ) = (sign d : ℝ) * (stepOffset i + (stepSize : ℝ)) := by
  have value : elapsedStop c d i = sign d * ((i.val : ℚ) + 1) * stepSize :=
    (all_row_arithmetic c d i).time_stop
  rw [value]
  simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_natCast, Rat.cast_one, stepOffset, source_step_and_sign.1]
  ring

theorem full_starts (c : FullBandCell) (p : Point) : rawFlow (cellSeed c p) 0 = cellSeed c p :=
  rawFlow_starts _

theorem full_tubes (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (p : Point) (inside : p ∈ cellDomain c) (d : Direction) (i : Step) (t : ℝ)
    (time : t ∈ Icc 0 (stepSize : ℝ)) :
    InRectangle (tubeBox c d i) (rawFlow (cellSeed c p) ((sign d : ℝ) * (t + stepOffset i))) := by
  rw [raw_signed_eq_window d _ _ (add_nonneg time.1 (stepOffset_nonneg i))]
  exact (source_window_chain c fields p inside d).tubes i t time

theorem full_fields (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (p : Point) (inside : p ∈ cellDomain c) (d : Direction) (i : Step) (t : ℝ)
    (time : t ∈ Icc 0 (stepSize : ℝ)) :
    FieldHolds (recordedCallField (tubeCallAt c d i))
      (rawFlow (cellSeed c p) ((sign d : ℝ) * (t + stepOffset i))) := by
  rw [raw_signed_eq_window d _ _ (add_nonneg time.1 (stepOffset_nonneg i))]
  exact (source_window_chain c fields p inside d).fields i t time

private theorem side_field_cover (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (p : Point) (inside : p ∈ cellDomain c) (d : Direction) (u : ℝ)
    (time : u ∈ Icc (0 : ℝ) (1/2)) : ∃ i : Step,
    InRectangle (tubeBox c d i) (rawFlow (cellSeed c p) ((sign d : ℝ) * u)) ∧
    FieldHolds (recordedCallField (tubeCallAt c d i)) (rawFlow (cellSeed c p) ((sign d : ℝ) * u)) := by
  obtain ⟨i, hi⟩ := sixteen_intervals_cover u time
  have localTime : u - stepOffset i ∈ Icc 0 (stepSize : ℝ) := by
    rw [source_step_and_sign.1]
    constructor <;> linarith [hi.1, hi.2]
  refine ⟨i, ?_, ?_⟩
  · simpa only [sub_add_cancel] using full_tubes c fields p inside d i (u - stepOffset i) localTime
  · simpa only [sub_add_cancel] using full_fields c fields p inside d i (u - stepOffset i) localTime

theorem full_field_cover (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (p : Point) (inside : p ∈ cellDomain c) (t : ℝ) (time : t ∈ Icc (-(1/2 : ℝ)) (1/2)) :
    ∃ d : Direction, ∃ i : Step,
      InRectangle (tubeBox c d i) (rawFlow (cellSeed c p) t) ∧
      FieldHolds (recordedCallField (tubeCallAt c d i)) (rawFlow (cellSeed c p) t) := by
  by_cases nonpositive : t ≤ 0
  · refine ⟨0, ?_⟩
    have result := side_field_cover c fields p inside 0 (-t) ⟨by linarith, by linarith [time.1]⟩
    simpa only [sign_zero, neg_one_mul, neg_neg] using result
  · refine ⟨1, ?_⟩
    have result := side_field_cover c fields p inside 1 t ⟨by linarith, time.2⟩
    simpa only [sign_one, one_mul] using result

theorem full_sourceCube (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (p : Point) (inside : p ∈ cellDomain c) (t : ℝ) (time : t ∈ Icc (-(1/2 : ℝ)) (1/2)) :
    rawFlow (cellSeed c p) t ∈ sourceCube := by
  obtain ⟨d, i, tube, _⟩ := full_field_cover c fields p inside t time
  exact WholeBandReplay.tube_in_sourceCube (all_row_arithmetic c d i) _ tube

theorem full_original (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (p : Point) (inside : p ∈ cellDomain c) :
    IsIntegralCurveOn (rawFlow (cellSeed c p)) (fun _ => sourceGradient) (Icc (-(1/2 : ℝ)) (1/2)) := by
  intro t ht
  have derivative := rawFlow_extended (cellSeed c p) t ht
  change HasDerivWithinAt (rawFlow (cellSeed c p)) (globalField 1 (rawFlow (cellSeed c p) t))
    (Icc (-(1/2 : ℝ)) (1/2)) t at derivative
  rw [globalField_eq_original 1 _ (full_sourceCube c fields p inside t ht)] at derivative
  simpa only [TrueTubeTrace.signedGradient, TrueTubeChecks.directions.2, Rat.cast_one, one_smul] using derivative

theorem full_initials (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (p : Point) (inside : p ∈ cellDomain c) (d : Direction) (i : Step) :
    InRectangle (initialBox c d i) (rawFlow (cellSeed c p) (elapsedStart c d i)) := by
  rw [elapsed_start_signed, raw_signed_eq_window d _ _ (stepOffset_nonneg i)]
  exact (source_window_chain c fields p inside d).initials i

theorem full_endpoints (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (p : Point) (inside : p ∈ cellDomain c) (d : Direction) (i : Step) :
    InRectangle (endpointBox c d i) (rawFlow (cellSeed c p) (elapsedStop c d i)) := by
  have stepPositive : 0 < (stepSize : ℝ) := Rat.cast_pos.mpr (all_row_arithmetic c d i).positive_step
  rw [elapsed_stop_signed, raw_signed_eq_window d _ _
    (add_nonneg (stepOffset_nonneg i) stepPositive.le)]
  exact (source_window_chain c fields p inside d).endpoints i

theorem full_next_initial (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (p : Point) (inside : p ∈ cellDomain c) (d : Direction) (i : Fin 15) :
    InRectangle (initialBox c d i.succ) (rawFlow (cellSeed c p) (elapsedStop c d i.castSucc)) :=
  (endpoint_next_initial c d i) ▸ full_endpoints c fields p inside d i.castSucc

theorem full_final (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (p : Point) (inside : p ∈ cellDomain c) (d : Direction) :
    InRectangle (endpointBox c d 15) (rawFlow (cellSeed c p) ((sign d : ℝ) * (1/2))) := by
  rw [raw_signed_eq_window d _ _ (by norm_num)]
  exact (source_window_chain c fields p inside d).final_endpoint

theorem full_actual_caps (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (p : Point) (inside : p ∈ cellDomain c) :
    InRectangle (endpointBox c 0 15) (rawFlow (cellSeed c p) (-(1/2 : ℝ))) ∧
    InRectangle (endpointBox c 1 15) (rawFlow (cellSeed c p) (1/2 : ℝ)) := by
  constructor
  · simpa only [sign_zero, neg_one_mul] using full_final c fields p inside 0
  · simpa only [sign_one, one_mul] using full_final c fields p inside 1

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
