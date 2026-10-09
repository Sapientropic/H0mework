import H0mework.Versions.V2.Arithmetic.RiemannWholeWard.FirstContact
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! The full original Pa correction has the same finite source-contact profile. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def firstContactRead (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    BurnolPaAmbientCarrier →L[ℂ] ℂ :=
  if inside : (1 / 4 : ℝ) ≤ |x| ∧ |x| < 4 then
    burnolPaSourceContact coordinate |x| (lt_of_lt_of_le (by norm_num) inside.1)
  else 0

private def correctionRead (coordinate : BurnolCompletedMellinCoordinate) :
    BurnolPaAmbientCarrier →L[ℂ] BurnolL2 :=
  burnolTateReciprocalL2.comp (burnolMobiusSourceL2.comp
    ((burnolPaSourceCorrection coordinate).comp
      burnolCompactCoPoissonClosedRange.toSubmodule.orthogonalProjectionOnto))

private theorem compact_correction_read (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) :
    (correctionRead coordinate (burnolCompactAdditivePhysicalState source) : ℝ → ℂ) =ᵐ[volume]
      fun x => firstContactRead coordinate x (burnolCompactAdditivePhysicalState source) := by
  have inside : burnolCompactAdditivePhysicalState source ∈ burnolCompactCoPoissonClosedRange := by
    simpa only [burnolCompactCoPoissonGenerator, Fin.isValue, ↓reduceIte] using
      burnolCompactCoPoissonGenerator_mem_closedRange (source, (0 : Fin 2))
  have projected :=
    burnolCompactCoPoissonClosedRange.toSubmodule.orthogonalProjectionOnto_mem_subspace_eq_self
      ⟨burnolCompactAdditivePhysicalState source, inside⟩
  change (burnolTateReciprocalL2 (burnolMobiusSourceL2 (burnolPaSourceCorrection coordinate
    (burnolCompactCoPoissonClosedRange.toSubmodule.orthogonalProjectionOnto
      (burnolCompactAdditivePhysicalState source)))) : ℝ → ℂ) =ᵐ[volume] _
  rw [projected]
  filter_upwards [burnolPaSourceCorrection_compact_tate coordinate source] with x read
  rw [read]
  by_cases hx : (1 / 4 : ℝ) ≤ |x| ∧ |x| < 4
  · simp only [if_pos hx, firstContactRead, dif_pos hx]
    exact (burnolPaSourceContact_compact coordinate source ⟨hx.1, hx.2.le⟩).symm
  · simp only [if_neg hx, firstContactRead, dif_neg hx, zero_apply]

private theorem correction_profile_closed (coordinate : BurnolCompletedMellinCoordinate) :
    IsClosed {p : BurnolPaAmbientCarrier |
      (correctionRead coordinate p : ℝ → ℂ) =ᵐ[volume] fun x => firstContactRead coordinate x p} := by
  apply IsSeqClosed.isClosed
  intro sequence p inProfile converges
  have sourceLimit := (correctionRead coordinate).continuous.tendsto p |>.comp converges
  obtain ⟨subsequence, strictly, almost⟩ :=
    (tendstoInMeasure_of_tendsto_Lp sourceLimit).exists_seq_tendsto_ae
  filter_upwards [almost, ae_all_iff.mpr (fun n => inProfile (subsequence n))] with x actual contact
  have pointwise := (firstContactRead coordinate x).continuous.tendsto p |>.comp
    (converges.comp strictly.tendsto_atTop)
  apply tendsto_nhds_unique actual
  exact pointwise.congr (fun n => (contact n).symm)

theorem pa_correction_contact_profile (coordinate : BurnolCompletedMellinCoordinate)
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    (burnolTateReciprocalL2 (burnolMobiusSourceL2
      (burnolPaSourceCorrection coordinate ⟨p, inside⟩)) : ℝ → ℂ) =ᵐ[volume]
        fun x => firstContactRead coordinate x p := by
  let equations : Submodule ℂ BurnolPaAmbientCarrier :=
    { carrier := {p | (correctionRead coordinate p : ℝ → ℂ) =ᵐ[volume]
          fun x => firstContactRead coordinate x p}
      zero_mem' := by
        change (correctionRead coordinate 0 : ℝ → ℂ) =ᵐ[volume] _
        simp only [map_zero]
        exact Lp.coeFn_zero _ _ _
      add_mem' := by
        intro a b ha hb
        change (correctionRead coordinate (a + b) : ℝ → ℂ) =ᵐ[volume] _
        rw [map_add]
        filter_upwards [Lp.coeFn_add (correctionRead coordinate a) (correctionRead coordinate b), ha, hb]
          with x sumRead first second
        rw [sumRead, Pi.add_apply, first, second, map_add]
      smul_mem' := by
        intro c a ha
        change (correctionRead coordinate (c • a) : ℝ → ℂ) =ᵐ[volume] _
        rw [map_smul]
        filter_upwards [Lp.coeFn_smul c (correctionRead coordinate a), ha] with x scaleRead read
        rw [scaleRead, Pi.smul_apply, read, map_smul] }
  have generator (i : BurnolCompactCoPoissonGeneratorIndex) :
      burnolCompactCoPoissonGenerator i ∈ equations := by
    rcases i with ⟨source, parity⟩
    fin_cases parity
    · exact compact_correction_read coordinate source
    · have same : burnolCompactCoPoissonGenerator (source, (1 : Fin 2)) =
          burnolCompactAdditivePhysicalState (burnolCompactTateReciprocalSource source) := by
        apply Subtype.ext
        exact burnolCompactFourierL2_eq_reciprocalL2 source
      change burnolCompactCoPoissonGenerator (source, (1 : Fin 2)) ∈ equations
      rw [same]
      exact compact_correction_read coordinate _
  have sourceRead (input : BurnolCompactCoPoissonLinearSource) :
      burnolCompactCoPoissonLanding input ∈ equations := by
    induction input using Finsupp.induction_linear with
    | zero => simpa only [map_zero] using equations.zero_mem
    | add a b ha hb => rw [map_add]; exact equations.add_mem ha hb
    | single i c => rw [burnolCompactCoPoissonLanding_single]; exact equations.smul_mem c (generator i)
  have included : LinearMap.range burnolCompactCoPoissonLanding ≤ equations := by
    rintro _ ⟨input, rfl⟩
    exact sourceRead input
  have generated := (LinearMap.range burnolCompactCoPoissonLanding).topologicalClosure_minimal
    included (correction_profile_closed coordinate) inside
  change (correctionRead coordinate p : ℝ → ℂ) =ᵐ[volume] _ at generated
  have projected :=
    burnolCompactCoPoissonClosedRange.toSubmodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨p, inside⟩
  simpa only [correctionRead, ContinuousLinearMap.comp_apply, projected] using generated

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
