import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.HMellin
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.KCounting

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.HMellin

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "K" => burnolCompletedMellinRieszVector

private theorem H_even (x : ℝ) : ConstantDual.sawtoothRaw (-x) = ConstantDual.sawtoothRaw x := by
  simp only [ConstantDual.sawtoothRaw, abs_neg]

private theorem H_real (x : ℝ) : star (ConstantDual.sawtoothRaw x) = ConstantDual.sawtoothRaw x := by
  rw [ConstantDual.sawtoothRaw, star_neg]
  exact congrArg Neg.neg (Complex.conj_ofReal _)

private def wholePower (s : ℂ) (x : ℝ) : ℂ := ((|x| : ℝ) : ℂ) ^ (-s) * ConstantDual.sawtoothRaw x

private theorem wholePower_even (s : ℂ) (x : ℝ) : wholePower s (-x) = wholePower s x := by
  simp only [wholePower, abs_neg, H_even]

theorem whole_integrable (s : ℂ) (positive : 0 < s.re) (below : s.re < 1) : Integrable (wholePower s) := by
  have first : IntegrableOn (wholePower s) (Ioi 0) := by
    apply (integrable s positive below).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [wholePower, abs_of_pos (show 0 < x from hx)]
  have second : IntegrableOn (wholePower s) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let embedding : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [embedding.integrableOn_map_iff]
    simp_rw [Function.comp_def, wholePower_even, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi first
  have entire := second.union first
  rwa [Iic_union_Ioi, integrableOn_univ] at entire

theorem whole_zero (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0) :
    (∫ x : ℝ, ((|x| : ℝ) : ℂ) ^ (-star coordinate.value) * ConstantDual.sawtoothRaw x) = 0 := by
  have positive : 0 < (star coordinate.value).re := by
    simp only [star_def, conj_re]
    linarith [coordinate.rightHalf]
  have below : (star coordinate.value).re < 1 := by simpa only [star_def, conj_re] using coordinate.belowOne
  have complete := whole_integrable (star coordinate.value) positive below
  have first : (∫ x : ℝ in Ioi 0, wholePower (star coordinate.value) x) = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx =>
      show wholePower (star coordinate.value) x = (x : ℂ) ^ (-star coordinate.value) * ConstantDual.sawtoothRaw x by
        simp only [wholePower, abs_of_pos (show 0 < x from hx)]), original_zero coordinate zero]
  have second : (∫ x : ℝ in Iic 0, wholePower (star coordinate.value) x) = 0 := by
    rw [setIntegral_congr_fun measurableSet_Iic (fun x _ => (wholePower_even (star coordinate.value) x).symm),
      integral_comp_neg_Iic, neg_zero, first]
  have split := setIntegral_union (Iic_disjoint_Ioi (a := (0 : ℝ)) le_rfl) measurableSet_Ioi
    complete.integrableOn complete.integrableOn
  rw [Iic_union_Ioi, setIntegral_univ, first, second, add_zero] at split
  exact split

private theorem pairing_read (value : BurnolL2) :
    inner ℂ ConstantDual.value value = ∫ x : ℝ, ConstantDual.sawtoothRaw x * value x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ConstantDual.value_coeFn] with x read
  rw [read]
  simp only [RCLike.inner_apply, starRingEnd_apply]
  rw [H_real]
  ring

private theorem pairing_integrable (value : BurnolL2) :
    Integrable (fun x : ℝ => ConstantDual.sawtoothRaw x * value x) := by
  apply (L2.integrable_inner (𝕜 := ℂ) ConstantDual.value value).congr
  filter_upwards [ConstantDual.value_coeFn] with x read
  rw [read]
  simp only [RCLike.inner_apply, starRingEnd_apply]
  rw [H_real]
  ring

/-- The position/H term is an actual full L¹ pairing; a is never promoted to an L² input. -/
theorem position_integrable (coordinate : BurnolCompletedMellinCoordinate) :
    Integrable (fun x : ℝ => ConstantDual.sawtoothRaw x * PositionCounting.seedRaw coordinate x) := by
  have actual := (PositionEuler.seed_integrable coordinate).mul_bdd ConstantDual.sawtooth_measurable.aestronglyMeasurable
    (Eventually.of_forall (fun x => (ConstantDual.sawtooth_bounds x).1))
  exact actual.congr (Eventually.of_forall (fun x => mul_comm _ _))

/-- The newly paid full Mellin zero is consumed by the unchanged original K source. -/
theorem original_kernel_pair (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0) :
    inner ℂ ConstantDual.value (K coordinate : BurnolL2) =
      -(∫ x : ℝ, ConstantDual.sawtoothRaw x * PositionCounting.seedRaw coordinate x) -
        inner ℂ (fourierL2 ConstantDual.value) (burnolQuarterZeroExtension
          (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) := by
  let b := burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
  have positive : 0 < (star coordinate.value).re := by
    simp only [star_def, conj_re]
    linarith [coordinate.rightHalf]
  have below : (star coordinate.value).re < 1 := by simpa only [star_def, conj_re] using coordinate.belowOne
  have powerInt : Integrable (fun x : ℝ => (1 / 2 : ℂ) * wholePower (star coordinate.value) x) :=
    (whole_integrable (star coordinate.value) positive below).const_mul (1 / 2 : ℂ)
  have source : inner ℂ ConstantDual.value (K coordinate : BurnolL2) =
      (1 / 2 : ℂ) * (∫ x : ℝ, wholePower (star coordinate.value) x) -
        (∫ x : ℝ, ConstantDual.sawtoothRaw x * PositionCounting.seedRaw coordinate x) -
        inner ℂ ConstantDual.value (fourierL2 b) := by
    rw [pairing_read, pairing_read]
    calc
      _ = ∫ x : ℝ, (1 / 2 : ℂ) * wholePower (star coordinate.value) x -
          ConstantDual.sawtoothRaw x * PositionCounting.seedRaw coordinate x -
          ConstantDual.sawtoothRaw x * fourierL2 b x := by
        apply integral_congr_ae
        filter_upwards [KCounting.original_kernel_raw coordinate] with x read
        rw [read]
        unfold wholePower
        change ConstantDual.sawtoothRaw x * ((1 / 2 : ℂ) * ((|x| : ℝ) : ℂ) ^ (-star coordinate.value) -
          PositionCounting.seedRaw coordinate x - fourierL2 b x) = _
        ring
      _ = _ := by
        have split := integral_sub (powerInt.sub (position_integrable coordinate)) (pairing_integrable (fourierL2 b))
        simp only [Pi.sub_apply] at split
        rw [split, integral_sub powerInt (position_integrable coordinate), integral_const_mul]
  have even : reflectL2 b = b := by
    change reflectL2 (burnolRadiusZeroExtension q (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) = _
    rw [burnolRadiusZeroExtension_reflect, burnolRieszSingleFourierSource_reflection_fixed]
    rfl
  have fourier := fourierL2.inner_map_map ConstantDual.value (fourierL2 b)
  rw [fourierL2_fourierL2, even] at fourier
  rw [source, show (∫ x : ℝ, wholePower (star coordinate.value) x) = 0 from whole_zero coordinate zero,
    mul_zero, zero_sub, ← fourier]

/-- The conjugate orientation retains the complete original a/H and b/FH terms. -/
theorem original_kernel_pair_right (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0) :
    inner ℂ (K coordinate : BurnolL2) ConstantDual.value =
      -(∫ x : ℝ, star (PositionCounting.seedRaw coordinate x) * ConstantDual.sawtoothRaw x) -
        inner ℂ (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))
          (fourierL2 ConstantDual.value) := by
  have actual := congrArg (star : ℂ → ℂ) (original_kernel_pair coordinate zero)
  have conjugate : star (∫ x : ℝ, ConstantDual.sawtoothRaw x * PositionCounting.seedRaw coordinate x) =
      ∫ x : ℝ, star (PositionCounting.seedRaw coordinate x) * ConstantDual.sawtoothRaw x := by
    rw [star_def, ← integral_conj]
    apply integral_congr_ae
    filter_upwards with x
    change star (ConstantDual.sawtoothRaw x * PositionCounting.seedRaw coordinate x) = _
    rw [star_mul, H_real]
    simp only [star_def]
  rw [star_sub, star_neg, conjugate] at actual
  simpa only [star_def, inner_conj_symm] using actual

end
end OriginalRieszFinitePairing.CoPoisson.Ward.HMellin
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
