import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.AnnulusExt
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Physical.Shell.Raw
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Synthesis.ShellContinuity

/-! Finite Volterra synthesis from the original source density and actual power shells. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

def volterraSourceDensity (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (u : ℝ) : ℂ :=
  -(2 : ℂ) * (u : ℂ) ^ (-coordinate.value) * value u

def sourceVolterraBandKernel (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (u t : ℝ) : ℂ :=
  volterraSourceDensity coordinate value u *
    if |t| ∈ Ico (1 / 4 : ℝ) u then ((|t| : ℝ) : ℂ) ^ (coordinate.value - 1) else 0

private theorem negativeShell_tate_source_raw (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (admitted : radius ∈ Icc (1 / 4 : ℝ) 4) :
    (burnolTateReciprocalL2
      (burnolMobiusSourceL2 (-closedShellState coordinate radius admitted)) : ℝ → ℂ) =ᵐ[volume]
      fun t => if |t| ∈ Ico (1 / 4 : ℝ) radius⁻¹ then
        ((|t| : ℝ) : ℂ) ^ (coordinate.value - 1) else 0 := by
  have same : burnolTateReciprocalL2
      (burnolMobiusSourceL2 (-closedShellState coordinate radius admitted)) =
        burnolMobiusSourceL2 (negativeFourierShellState coordinate radius admitted) := by
    simp only [negativeFourierShellState, map_neg,
      burnolMobiusSource_fourier _ (closedShellState_mem coordinate radius admitted)]
  rw [same]
  exact negativeFourierShellState_source_raw coordinate radius admitted

theorem volterraPhysicalShell_tate_source_raw (coordinate : BurnolCompletedMellinCoordinate)
    (u : ℝ) (inside : u ∈ Icc (1 / 4 : ℝ) 4) :
    (burnolTateReciprocalL2 (burnolMobiusSourceL2 (volterraPhysicalShell coordinate u)) : ℝ → ℂ)
      =ᵐ[volume] fun t => if |t| ∈ Ico (1 / 4 : ℝ) u then
        ((|t| : ℝ) : ℂ) ^ (coordinate.value - 1) else 0 := by
  rw [volterraPhysicalShell, dif_pos inside]
  simpa only [inv_inv] using negativeShell_tate_source_raw coordinate u⁻¹
    (volterraShell_reciprocal_admitted u inside)

theorem volterraSourceDensity_integrableOn
    (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    IntegrableOn (volterraSourceDensity coordinate value) (Icc (1 / 4 : ℝ) 4) := by
  have native := burnolRadiusMellinWeight_integrableOn_tail (1 / 4) (by norm_num)
    coordinate.value coordinate.rightHalf value
  have extended := (integrableOn_Ici_iff_integrableOn_Ioi).mpr native
  have restricted := extended.mono_set
    (show Icc (1 / 4 : ℝ) 4 ⊆ Ici (1 / 4 : ℝ) from fun _ h => h.1)
  change Integrable (fun u : ℝ => -(2 : ℂ) * (u : ℂ) ^ (-coordinate.value) * value u)
    (volume.restrict (Icc (1 / 4 : ℝ) 4))
  simpa only [mul_assoc] using restricted.const_mul (-(2 : ℂ))

theorem sourceVolterraBandKernel_integral_positive
    (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (t : ℝ) (inside : t ∈ Icc (1 / 4 : ℝ) 4) :
    (∫ u : ℝ in Icc (1 / 4 : ℝ) 4, sourceVolterraBandKernel coordinate value u t) =
      -(2 : ℂ) * (t : ℂ) ^ (coordinate.value - 1) *
        (burnolRadiusMellinTailEvaluator t (by linarith [inside.1])
            coordinate.value coordinate.rightHalf value -
          burnolRadiusMellinTailEvaluator 4 (by norm_num)
            coordinate.value coordinate.rightHalf value) := by
  have positive : 0 < t := by linarith [inside.1]
  have reads (u : ℝ) : sourceVolterraBandKernel coordinate value u t =
      (Ioi t).indicator (fun u : ℝ =>
        -(2 : ℂ) * (t : ℂ) ^ (coordinate.value - 1) *
          ((u : ℂ) ^ (-coordinate.value) * value u)) u := by
    simp only [sourceVolterraBandKernel, abs_of_pos positive, mem_Ico, inside.1, true_and,
      volterraSourceDensity, Set.indicator_apply, mem_Ioi]
    split_ifs <;> ring
  simp_rw [reads]
  rw [setIntegral_indicator measurableSet_Ioi]
  have domain : Ioi t ∩ Icc (1 / 4 : ℝ) 4 = Ioc t 4 := by
    ext u
    simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · exact fun h => ⟨h.1, le_trans inside.1 h.1.le, h.2⟩
  rw [inter_comm, domain, integral_const_mul]
  congr 1
  simp only [burnolRadiusMellinTailEvaluator_eq_integral]
  rw [intervalIntegral.integral_Ioi_sub_Ioi
    (burnolRadiusMellinWeight_integrableOn_tail t positive coordinate.value
      coordinate.rightHalf value) inside.2,
    intervalIntegral.integral_of_le inside.2]

theorem sourceVolterraBandKernel_integral_outside
    (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (t : ℝ) (outside : |t| ∉ Ico (1 / 4 : ℝ) 4) :
    (∫ u : ℝ in Icc (1 / 4 : ℝ) 4, sourceVolterraBandKernel coordinate value u t) = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro u hu
  have out : |t| ∉ Ico (1 / 4 : ℝ) u := fun h => outside ⟨h.1, h.2.trans_le hu.2⟩
  simp only [sourceVolterraBandKernel, if_neg out, mul_zero]

theorem sourceVolterraBandKernel_measurable
    (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    Measurable (fun point : ℝ × ℝ => sourceVolterraBandKernel coordinate value point.1 point.2) := by
  have density : Measurable (volterraSourceDensity coordinate value) := by
    unfold volterraSourceDensity
    fun_prop
  have band : MeasurableSet {point : ℝ × ℝ | |point.2| ∈ Ico (1 / 4 : ℝ) point.1} := by
    have absolute : Measurable (fun point : ℝ × ℝ => |point.2|) := by fun_prop
    simp only [mem_Ico]
    exact (measurableSet_le measurable_const absolute).inter
      (measurableSet_lt absolute measurable_fst)
  exact (density.comp measurable_fst).mul
    (Measurable.ite band
      (by fun_prop) measurable_const)

/-- The original even, annulus-supported source determines the full-line scalar synthesis. -/
theorem sourceVolterraWindow_band_integral_profile
    (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (even : reflectL2 value = value) (supported : sourceAnnulusCut value = value) :
    (sourceVolterraWindow coordinate value : ℝ → ℂ) =ᵐ[volume]
      fun t => ∫ u : ℝ in Icc (1 / 4 : ℝ) 4, sourceVolterraBandKernel coordinate value u t := by
  let output := sourceVolterraWindow coordinate value
  have reflected := Lp.coeFn_compMeasurePreserving output negMeasurePreserving
  change (reflectL2 output : ℝ → ℂ) =ᵐ[volume] (fun t => output (-t)) at reflected
  rw [show reflectL2 output = output from sourceVolterraWindow_even coordinate value even]
    at reflected
  have localRead := sourceVolterraWindow_annulus_profile coordinate value supported
  have outputRead := sourceAnnulusCut_coeFn (sourceVolterraResolvent coordinate value)
  filter_upwards [localRead, negMeasurePreserving.quasiMeasurePreserving.ae localRead,
    reflected, outputRead, volume.ae_ne (1 / 4 : ℝ), volume.ae_ne (-1 / 4 : ℝ),
    volume.ae_ne (4 : ℝ), volume.ae_ne (-4 : ℝ)]
      with t positiveRead negativeRead reflection cutoff notQuarter notNegQuarter notFour notNegFour
  have notAbsQuarter : |t| ≠ (1 / 4 : ℝ) := by
    intro equal
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 4)).mp equal with hp | hn
    · exact notQuarter hp
    · exact notNegQuarter (by simpa only [neg_div] using hn)
  have notAbsFour : |t| ≠ (4 : ℝ) := by
    intro equal
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 4)).mp equal with hp | hn
    · exact notFour hp
    · exact notNegFour hn
  by_cases band : |t| ∈ Ioo (1 / 4 : ℝ) 4
  · by_cases positive : 0 ≤ t
    · have admitted : t ∈ Ioo (1 / 4 : ℝ) 4 := by simpa only [abs_of_nonneg positive] using band
      rw [positiveRead admitted,
        sourceVolterraBandKernel_integral_positive coordinate value t ⟨admitted.1.le, admitted.2.le⟩]
    · have admitted : -t ∈ Ioo (1 / 4 : ℝ) 4 := by
        simpa only [abs_of_neg (lt_of_not_ge positive)] using band
      change output t = _
      rw [reflection, negativeRead admitted]
      have same : (fun u => sourceVolterraBandKernel coordinate value u t) =
          (fun u => sourceVolterraBandKernel coordinate value u (-t)) := by
        funext u
        simp only [sourceVolterraBandKernel, abs_neg]
      rw [same, sourceVolterraBandKernel_integral_positive coordinate value (-t)
        ⟨admitted.1.le, admitted.2.le⟩]
  · have cutOutside : ¬ ((1 / 4 : ℝ) < |t| ∧ |t| ≤ 4) := by
      intro h
      exact band ⟨h.1, lt_of_le_of_ne h.2 notAbsFour⟩
    have kernelOutside : |t| ∉ Ico (1 / 4 : ℝ) 4 := by
      intro h
      exact band ⟨lt_of_le_of_ne h.1 notAbsQuarter.symm, h.2⟩
    change sourceAnnulusCut (sourceVolterraResolvent coordinate value) t = _
    rw [cutoff, if_neg cutOutside,
      sourceVolterraBandKernel_integral_outside coordinate value t kernelOutside]

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
