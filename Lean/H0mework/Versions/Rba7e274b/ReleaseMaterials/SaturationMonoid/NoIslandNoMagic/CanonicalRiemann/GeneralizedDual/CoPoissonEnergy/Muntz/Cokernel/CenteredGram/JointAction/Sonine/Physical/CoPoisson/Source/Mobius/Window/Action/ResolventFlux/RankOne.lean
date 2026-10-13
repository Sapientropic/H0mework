import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.Outer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.Volterra.Window
import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.PowerSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FiniteMobiusResolventFlux
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace

def innerTailMoment (coordinate : BurnolCompletedMellinCoordinate) (value : Ambient) : ℂ :=
  burnolRadiusMellinTailEvaluator (1/4:ℝ) (by norm_num) coordinate.value coordinate.rightHalf
    (burnolTateReciprocalL2 (burnolMobiusSourceL2 value))
def exteriorBase (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolRadiusNormalizedUnitTail coordinate 4 (by norm_num)

-- Compact source support fixes one actual Tate-window moment for the entire exterior tail.
theorem tate_mobius_tail_fixed (coordinate : BurnolCompletedMellinCoordinate) (value : Ambient)
    (t : ℝ) (positive : 0<t) (small : t≤1/4) :
    burnolRadiusMellinTailEvaluator t positive coordinate.value coordinate.rightHalf
      (burnolTateReciprocalL2 (burnolMobiusSourceL2 value))=innerTailMoment coordinate value := by
  rw [burnolRadiusMellinTailEvaluator_eq_integral,innerTailMoment,burnolRadiusMellinTailEvaluator_eq_integral]
  rw [← integral_indicator measurableSet_Ioi,← integral_indicator measurableSet_Ioi]
  have gap := (ae_restrict_iff' (measurableSet_symmetricInterval (1/4:ℝ))).mp (burnolTateMobiusSource_innerGap value)
  apply integral_congr_ae
  filter_upwards [gap] with x zero
  by_cases outer : (1/4:ℝ)<x
  · rw [indicator_of_mem (show x∈Ioi (1/4:ℝ) from outer),indicator_of_mem (show x∈Ioi t from small.trans_lt outer)]
  · rw [indicator_of_notMem (show x∉Ioi (1/4:ℝ) from outer)]
    by_cases after : t<x
    · rw [indicator_of_mem (show x∈Ioi t from after),zero (show x∈symmetricInterval (1/4:ℝ) from ⟨by linarith,le_of_not_gt outer⟩),mul_zero]
    · rw [indicator_of_notMem (show x∉Ioi t from after)]

theorem R_tate_window_profile (coordinate : BurnolCompletedMellinCoordinate) (value : Ambient) :
    ∀ᵐ t : ℝ ∂volume, ∀ _positive : 0<t, ∀ _small : t≤1/4,
      burnolTateReciprocalL2 (burnolDirectRightResolvent (coordinate.value/2) (burnolMobiusSourceL2 value)) t=
      -(2:ℂ)*(t:ℂ)^(coordinate.value-1)*innerTailMoment coordinate value := by
  have actual := OriginalPaPhysicalGreen.sourceVolterraResolvent_positive_profile coordinate
    (burnolTateReciprocalL2 (burnolMobiusSourceL2 value))
  filter_upwards [actual] with t read positive small
  have same : OriginalPaPhysicalGreen.sourceVolterraResolvent coordinate
      (burnolTateReciprocalL2 (burnolMobiusSourceL2 value))=
      burnolTateReciprocalL2 (burnolDirectRightResolvent (coordinate.value/2) (burnolMobiusSourceL2 value)) := by
    change burnolTateReciprocalL2 (burnolDirectRightResolvent (coordinate.value/2)
      (burnolTateReciprocalL2 (burnolTateReciprocalL2 (burnolMobiusSourceL2 value))))=_
    rw [burnolTateReciprocalL2_involutive]
  rw [same] at read
  rw [read positive,tate_mobius_tail_fixed coordinate value t positive small]

-- Even source parity is paid by the finite programme, not inherited by arbitrary material.
theorem original_R_M_even (coordinate : BurnolCompletedMellinCoordinate) (value : Ambient) :
    reflectL2 (burnolDirectRightResolvent (coordinate.value/2) (burnolMobiusSourceL2 value))=
      burnolDirectRightResolvent (coordinate.value/2) (burnolMobiusSourceL2 value) := by
  unfold burnolDirectRightResolvent
  rw [map_neg,← reflectL2.integral_comp_comm (burnolDirectRightResolventIntegrand (coordinate.value/2) (burnolMobiusSourceL2 value))]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro tau _
  unfold burnolDirectRightResolventIntegrand
  dsimp only
  rw [map_smul,reflectL2_burnolMultiplicativeDilation,burnolMobiusSourceL2_even]

theorem original_tate_R_M_even (coordinate : BurnolCompletedMellinCoordinate) (value : Ambient) :
    reflectL2 (burnolTateReciprocalL2 (burnolDirectRightResolvent (coordinate.value/2) (burnolMobiusSourceL2 value)))=
      burnolTateReciprocalL2 (burnolDirectRightResolvent (coordinate.value/2) (burnolMobiusSourceL2 value)) := by
  rw [← burnolTateReciprocal_reflect,original_R_M_even]

theorem tate_R_M_inner_abs_profile (coordinate : BurnolCompletedMellinCoordinate) (value : Ambient) :
    (burnolTateReciprocalL2 (burnolDirectRightResolvent (coordinate.value/2) (burnolMobiusSourceL2 value)) : ℝ→ℂ) =ᵐ[
      volume.restrict (symmetricInterval (1/4:ℝ))]
      fun x => -(2:ℂ)*((|x|:ℝ):ℂ)^(coordinate.value-1)*innerTailMoment coordinate value := by
  let field := burnolTateReciprocalL2 (burnolDirectRightResolvent (coordinate.value/2) (burnolMobiusSourceL2 value))
  have reflected := Lp.coeFn_compMeasurePreserving field negMeasurePreserving
  have negativeRead := negMeasurePreserving.quasiMeasurePreserving.ae (R_tate_window_profile coordinate value)
  filter_upwards [ae_restrict_of_ae (R_tate_window_profile coordinate value),ae_restrict_of_ae negativeRead,
    ae_restrict_of_ae reflected,ae_restrict_mem (measurableSet_symmetricInterval (1/4:ℝ)),ae_restrict_of_ae (volume.ae_ne (0:ℝ))]
      with x direct negative reflected inside nonzero
  have parity : field (-x)=field x := by
    change reflectL2 field x=field (-x) at reflected
    rw [show reflectL2 field=field by exact original_tate_R_M_even coordinate value] at reflected
    exact reflected.symm
  rcases lt_or_gt_of_ne nonzero with neg | pos
  · rw [abs_of_neg neg,← parity]
    exact negative (by linarith) (by linarith [inside.1])
  · rw [abs_of_pos pos]
    exact direct pos inside.2

-- The full original forward cutoff flux is an actual rank-one exterior field.
theorem source_forward_flux_rank_one (coordinate : BurnolCompletedMellinCoordinate) (value : Ambient) :
    actualFlux (coordinate.value/2) (value : BurnolL2)=
      -(2*innerTailMoment coordinate value) • exteriorBase coordinate := by
  have rq : 1/4<(coordinate.value/2).re := by rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
  rw [source_forward_flux_outer (coordinate.value/2) rq value,lower_source_physical]
  let field := burnolDirectRightResolvent (coordinate.value/2) (burnolMobiusSourceL2 value)
  let dual := burnolTateReciprocalL2 field
  let raw : ℝ→ℂ := (symmetricInterval (1/4:ℝ)).indicator (dual : ℝ→ℂ)
  have localRead := (ae_restrict_iff' (measurableSet_symmetricInterval (1/4:ℝ))).mp
    (tate_R_M_inner_abs_profile coordinate value)
  have masked : raw =ᵐ[volume] (symmetricInterval (1/4:ℝ)).indicator
      (fun x => -(2:ℂ)*((|x|:ℝ):ℂ)^(coordinate.value-1)*innerTailMoment coordinate value) := by
    filter_upwards [localRead] with x read
    by_cases inside : x∈symmetricInterval (1/4:ℝ)
    · dsimp only [raw]
      rw [indicator_of_mem inside,indicator_of_mem inside,read inside]
    · dsimp only [raw]
      rw [indicator_of_notMem inside,indicator_of_notMem inside]
  have pulled := burnolTateReciprocalRaw_ae_congr ((Lp.memLp dual).indicator (measurableSet_symmetricInterval (1/4:ℝ)))
    (((Lp.memLp dual).indicator (measurableSet_symmetricInterval (1/4:ℝ))).ae_eq masked) masked
  have unmasked := burnolTateReciprocalL2_coeFn dual
  rw [burnolTateReciprocalL2_involutive] at unmasked
  apply Lp.ext
  filter_upwards [Lp.coeFn_neg (outerCut field),Lp.coeFn_sub field (cutoff 4 field),cutoff_read 4 field,
    Lp.coeFn_smul (-(2*innerTailMoment coordinate value)) (exteriorBase coordinate),burnolRadiusUnitTail_coeFn coordinate 4 (by norm_num),
    pulled,unmasked] with x negative subtraction cutRead scalar basis reciprocal whole
  change (-outerCut field : BurnolL2) x=(-(2*innerTailMoment coordinate value) • exteriorBase coordinate : BurnolL2) x
  rw [negative,scalar]
  change -(outerCut field : BurnolL2) x=(-(2*innerTailMoment coordinate value))*exteriorBase coordinate x
  unfold outerCut
  change -(field-cutoff 4 field : BurnolL2) x=_
  rw [subtraction]
  simp only [Pi.sub_apply]
  rw [cutRead]
  by_cases outer : (4:ℝ) < |x|
  · have notInside : x∉symmetricInterval 4 := fun inside=>not_le_of_gt outer (abs_le.mpr inside)
    rw [indicator_of_notMem notInside]
    have small : x⁻¹∈symmetricInterval (1/4:ℝ) := by
      apply abs_le.mp
      rw [abs_inv]
      have reciprocal : |x|⁻¹ < (4:ℝ)⁻¹ := (inv_lt_inv₀ (lt_trans (by norm_num) outer) (by norm_num)).mpr outer
      norm_num at reciprocal
      exact reciprocal.le
    unfold burnolTateReciprocalRaw at reciprocal whole
    simp only [indicator_of_mem small] at reciprocal
    have source : field x = ((|x|:ℝ):ℂ)⁻¹ *
        (-(2:ℂ)*((|x⁻¹|:ℝ):ℂ)^(coordinate.value-1)*innerTailMoment coordinate value) :=
      whole.trans reciprocal
    rw [source]
    change exteriorBase coordinate x=(if (4:ℝ) < |x| then -((|x|:ℝ):ℂ)^(-coordinate.value) else 0) at basis
    rw [basis,if_pos outer]
    simp only [abs_inv,Complex.ofReal_inv]
    rw [Complex.inv_cpow_ofReal_nonneg (abs_nonneg x),← Complex.cpow_neg]
    have xNe : ((|x|:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans (by norm_num) outer))
    rw [← Complex.cpow_neg_one]
    calc
      _ = (2*innerTailMoment coordinate value)*
          (((|x|:ℝ):ℂ)^(-(1:ℂ))*((|x|:ℝ):ℂ)^(-(coordinate.value-1))) := by ring
      _ = _ := by
        rw [← Complex.cpow_add _ _ xNe]
        rw [show -(1:ℂ)+(-(coordinate.value-1))=-coordinate.value by ring]
        ring
  · have inside : x∈symmetricInterval 4 := abs_le.mp (le_of_not_gt outer)
    rw [indicator_of_mem inside,sub_self,neg_zero]
    change exteriorBase coordinate x=(if (4:ℝ) < |x| then -((|x|:ℝ):ℂ)^(-coordinate.value) else 0) at basis
    rw [basis,if_neg outer,mul_zero]

end FiniteMobiusResolventFlux
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
