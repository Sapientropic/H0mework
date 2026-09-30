import H0mework.Realization.Topology.CompressedUnitaryDefectPort
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false
open scoped Topology ENNReal InnerProductSpace

namespace SaturationMonoid.NavierStokes.NativeTemporalActionCompression

open Set Filter MeasureTheory
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedCompressedUnitaryDefectPort

noncomputable section

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

abbrev Ambient : Type _ := Lp E 2 (volume : Measure ℝ)

def translation (advance : ℝ) : Ambient E →ₗᵢ[ℂ] Ambient E :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun time : ℝ => time + advance)
    (measurePreserving_add_right volume advance)

def negativeRestriction : Ambient E →L[ℂ] Lp E 2 (volume.restrict (Iio (0 : ℝ))) :=
  LpToLpRestrictCLM ℝ E ℂ volume 2 (Iio (0 : ℝ))

def futureSpace : ClosedSubmodule ℂ (Ambient E) :=
  ⟨(negativeRestriction E).ker, (negativeRestriction E).isClosed_ker⟩

omit [CompleteSpace E] in
theorem mem_future_iff (field : Ambient E) : field ∈ futureSpace E ↔
    ∀ᵐ time : ℝ, time < 0 → field time = 0 := by
  change negativeRestriction E field = 0 ↔ _
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have actual := LpToLpRestrictCLM_coeFn (𝕜 := ℂ) (Iio (0 : ℝ)) field
  constructor
  · intro zero
    exact (ae_restrict_iff' measurableSet_Iio).mp (actual.symm.trans zero)
  · intro zero
    exact actual.trans ((ae_restrict_iff' measurableSet_Iio).mpr zero)

def cut (support : Set ℝ) (measurable : MeasurableSet support) (field : Ambient E) : Ambient E :=
  ((Lp.memLp field).indicator measurable).toLp (support.indicator field)

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
theorem cut_ae (support : Set ℝ) (measurable : MeasurableSet support) (field : Ambient E) :
    cut E support measurable field =ᵐ[volume] support.indicator field :=
  MemLp.coeFn_toLp _

omit [CompleteSpace E] in
theorem future_cut_mem (field : Ambient E) : cut E (Ici 0) measurableSet_Ici field ∈ futureSpace E := by
  rw [mem_future_iff]
  filter_upwards [cut_ae E (Ici 0) measurableSet_Ici field] with time same negative
  rw [same, indicator_of_notMem (by simpa using not_le.mpr negative)]

local instance : CompleteSpace (futureSpace E).toSubmodule :=
  (futureSpace E).isClosed.isComplete.completeSpace_coe

theorem future_projection (field : Ambient E) :
    (futureSpace E).toSubmodule.starProjection field = cut E (Ici 0) measurableSet_Ici field := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (future_cut_mem E field)
  intro test member
  have supported := (mem_future_iff E test).mp member
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [Lp.coeFn_sub field (cut E (Ici 0) measurableSet_Ici field),
    cut_ae E (Ici 0) measurableSet_Ici field, supported] with time difference same zero
  simp only [difference, Pi.sub_apply, Pi.zero_apply]
  rw [same]
  by_cases nonnegative : 0 ≤ time
  · rw [indicator_of_mem (show time ∈ Ici (0 : ℝ) from nonnegative), sub_self, inner_zero_left]
  · rw [zero (lt_of_not_ge nonnegative), inner_zero_right]

def port (advance : ℝ) := defectPort (futureSpace E) (translation E advance)

theorem compression_eq_cut (advance : ℝ) (field : (futureSpace E).toSubmodule) :
    (compression (futureSpace E) (translation E advance) field : Ambient E) =
      cut E (Ici 0) measurableSet_Ici (translation E advance field) :=
  future_projection E _

theorem external_eq_sub (advance : ℝ) (field : (futureSpace E).toSubmodule) :
    (externalDefect (futureSpace E) (translation E advance) field : Ambient E) =
      translation E advance field - cut E (Ici 0) measurableSet_Ici (translation E advance field) := by
  have split := compression_add_externalDefect (futureSpace E) (translation E advance) field
  rw [compression_eq_cut] at split
  exact eq_sub_of_add_eq' split

omit [CompleteSpace E] in
theorem translation_ae (advance : ℝ) (field : Ambient E) :
    translation E advance field =ᵐ[volume] fun time => field (time + advance) :=
  Lp.coeFn_compMeasurePreserving field (measurePreserving_add_right volume advance)

/-- The first port is the actual future, with the original physical time shift. -/
theorem compression_ae (advance : ℝ) (field : (futureSpace E).toSubmodule) :
    (compression (futureSpace E) (translation E advance) field : Ambient E) =ᵐ[volume]
      fun time => if 0 ≤ time then (field : Ambient E) (time + advance) else 0 := by
  rw [compression_eq_cut]
  filter_upwards [cut_ae E (Ici 0) measurableSet_Ici (translation E advance field),
    translation_ae E advance field] with time cutSame shifted
  rw [cutSame]
  by_cases nonnegative : 0 ≤ time
  · rw [indicator_of_mem (show time ∈ Ici (0 : ℝ) from nonnegative), shifted, if_pos nonnegative]
  · rw [indicator_of_notMem (show time ∉ Ici (0 : ℝ) from nonnegative), if_neg nonnegative]

/-- The external port retains the whole shifted past; it is not a zero residual. -/
theorem external_ae (advance : ℝ) (field : (futureSpace E).toSubmodule) :
    (externalDefect (futureSpace E) (translation E advance) field : Ambient E) =ᵐ[volume]
      fun time => if time < 0 then (field : Ambient E) (time + advance) else 0 := by
  rw [external_eq_sub]
  filter_upwards [Lp.coeFn_sub (translation E advance field)
      (cut E (Ici 0) measurableSet_Ici (translation E advance field)),
    cut_ae E (Ici 0) measurableSet_Ici (translation E advance field),
    translation_ae E advance field] with time difference cutSame shifted
  simp only [difference, Pi.sub_apply]
  rw [cutSame]
  by_cases nonnegative : 0 ≤ time
  · rw [indicator_of_mem (show time ∈ Ici (0 : ℝ) from nonnegative), sub_self, if_neg (not_lt.mpr nonnegative)]
  · rw [indicator_of_notMem (show time ∉ Ici (0 : ℝ) from nonnegative), sub_zero, shifted, if_pos (lt_of_not_ge nonnegative)]

theorem norm_account (advance : ℝ) (field : (futureSpace E).toSubmodule) :
    ‖compression (futureSpace E) (translation E advance) field‖ ^ 2 +
      ‖externalDefect (futureSpace E) (translation E advance) field‖ ^ 2 = ‖field‖ ^ 2 :=
  norm_sq_compression_add_externalDefect _ _ _

/-- A source-generated tail identity is consumed as equality of the actual compressed profile. -/
theorem compression_eq_next (advance : ℝ) (field next : (futureSpace E).toSubmodule)
    (same : ∀ᵐ time : ℝ, 0 ≤ time → (field : Ambient E) (time + advance) = (next : Ambient E) time) :
    compression (futureSpace E) (translation E advance) field = next := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [compression_ae E advance field, (mem_future_iff E next).mp next.2, same]
    with time compressed zero actual
  rw [compressed]
  by_cases nonnegative : 0 ≤ time
  · rw [if_pos nonnegative, actual nonnegative]
  · rw [if_neg nonnegative, zero (lt_of_not_ge nonnegative)]

/-- Undoing the physical shift reads the original complete prefix, including every fiber coordinate. -/
theorem restored_external_eq_prefix (advance : ℝ) (field : (futureSpace E).toSubmodule) :
    translation E (-advance) (externalDefect (futureSpace E) (translation E advance) field : Ambient E) =
      cut E (Ico 0 advance) measurableSet_Ico field := by
  apply Lp.ext
  have pulled := (measurePreserving_add_right volume (-advance)).quasiMeasurePreserving.ae
    (external_ae E advance field)
  filter_upwards [translation_ae E (-advance)
      (externalDefect (futureSpace E) (translation E advance) field), pulled,
    cut_ae E (Ico 0 advance) measurableSet_Ico field, (mem_future_iff E field).mp field.2]
    with time shifted trace prefixRead zero
  rw [shifted, trace, prefixRead]
  rw [show time + -advance + advance = time by ring]
  by_cases nonnegative : 0 ≤ time
  · by_cases before : time < advance
    · rw [if_pos (by linarith : time + -advance < 0),
        indicator_of_mem (show time ∈ Ico (0 : ℝ) advance from ⟨nonnegative, before⟩)]
    · rw [if_neg (by linarith : ¬ time + -advance < 0),
        indicator_of_notMem (show time ∉ Ico (0 : ℝ) advance from fun member => before member.2)]
  · rw [zero (lt_of_not_ge nonnegative),
      indicator_of_notMem (show time ∉ Ico (0 : ℝ) advance from fun member => nonnegative member.1)]
    split_ifs <;> rfl

theorem norm_account_prefix (advance : ℝ) (field : (futureSpace E).toSubmodule) :
    ‖compression (futureSpace E) (translation E advance) field‖ ^ 2 +
      ‖cut E (Ico 0 advance) measurableSet_Ico field‖ ^ 2 = ‖field‖ ^ 2 := by
  have traceNorm : ‖cut E (Ico 0 advance) measurableSet_Ico field‖ =
      ‖externalDefect (futureSpace E) (translation E advance) field‖ := by
    rw [← restored_external_eq_prefix E advance field, (translation E (-advance)).norm_map]
    rfl
  rw [traceNorm]
  exact norm_account E advance field

theorem compression_add (first second : ℝ) (second_nonnegative : 0 ≤ second)
    (field : (futureSpace E).toSubmodule) :
    compression (futureSpace E) (translation E second)
        (compression (futureSpace E) (translation E first) field) =
      compression (futureSpace E) (translation E (first + second)) field := by
  apply compression_eq_next E second
  have pulled := (measurePreserving_add_right volume second).quasiMeasurePreserving.ae
    (compression_ae E first field)
  filter_upwards [pulled, compression_ae E (first + second) field] with time firstRead fullRead nonnegative
  rw [firstRead, fullRead, if_pos (add_nonneg nonnegative second_nonnegative), if_pos nonnegative]
  congr 1
  ring

def ofHalfline (field : ℝ → E) (paid : MemLp field 2 (volume.restrict (Ici (0 : ℝ)))) :
    (futureSpace E).toSubmodule :=
  let full : MemLp ((Ici (0 : ℝ)).indicator field) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Ici).mpr paid
  ⟨full.toLp _, (mem_future_iff E _).mpr (by
    filter_upwards [MemLp.coeFn_toLp full] with time same negative
    rw [same, indicator_of_notMem (show time ∉ Ici (0 : ℝ) from not_le.mpr negative)])⟩

omit [CompleteSpace E] in
theorem ofHalfline_ae (field : ℝ → E) (paid : MemLp field 2 (volume.restrict (Ici (0 : ℝ)))) :
    (ofHalfline E field paid : Ambient E) =ᵐ[volume] (Ici (0 : ℝ)).indicator field := by
  have full : MemLp ((Ici (0 : ℝ)).indicator field) 2 (volume : Measure ℝ) :=
    (memLp_indicator_iff_restrict measurableSet_Ici).mpr paid
  exact MemLp.coeFn_toLp full

theorem ofHalfline_compression_next (advance : ℝ) (nonnegative : 0 ≤ advance)
    (field next : ℝ → E)
    (fieldPaid : MemLp field 2 (volume.restrict (Ici (0 : ℝ))))
    (nextPaid : MemLp next 2 (volume.restrict (Ici (0 : ℝ))))
    (sourceShift : ∀ time : ℝ, 0 ≤ time → field (time + advance) = next time) :
    compression (futureSpace E) (translation E advance) (ofHalfline E field fieldPaid) =
      ofHalfline E next nextPaid := by
  apply compression_eq_next E advance
  have shifted := (measurePreserving_add_right volume advance).quasiMeasurePreserving.ae
    (ofHalfline_ae E field fieldPaid)
  filter_upwards [shifted, ofHalfline_ae E next nextPaid] with time original target positive
  rw [original, target,
    indicator_of_mem (show time + advance ∈ Ici (0 : ℝ) from add_nonneg positive nonnegative),
    indicator_of_mem (show time ∈ Ici (0 : ℝ) from positive)]
  exact sourceShift time positive

end
end SaturationMonoid.NavierStokes.NativeTemporalActionCompression
