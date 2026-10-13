import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveRank.Support
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPrimitiveRankBalance
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace
namespace Cut
export FiniteMobiusResolventFlux (cutoff cutoff_read action_cutoff Rplus_integrable RplusIntegrand)
end Cut

-- Positive source dilation contracts the source-owned support before integration.
theorem cutoff_Rplus_source (radius : ℝ) (nonnegative : 0≤radius) (z : ℂ) (right : 1/4<z.re)
    (value : BurnolL2) : Cut.cutoff radius (Paid.Rplus z (Cut.cutoff radius value))=Paid.Rplus z (Cut.cutoff radius value) := by
  unfold FiniteMobiusResolventFlux.Rplus
  rw [map_neg,← (Cut.cutoff radius).integral_comp_comm (Cut.Rplus_integrable z right (Cut.cutoff radius value))]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro tau positive
  unfold Cut.RplusIntegrand
  dsimp only
  rw [map_smul,Cut.action_cutoff radius nonnegative]
  have bounded : radius*Real.exp (-(tau/2))≤radius := by
    have tauPositive : 0<tau := positive
    have scale : Real.exp (-(tau/2))≤1 := Real.exp_le_one_iff.mpr (by linarith)
    exact (mul_le_mul_of_nonneg_left scale nonnegative).trans_eq (mul_one _)
  congr 1
  apply Lp.ext
  filter_upwards [Cut.cutoff_read radius (Cut.cutoff (radius*Real.exp (-(tau/2))) (burnolMultiplicativeDilation (tau/2) value)),
    Cut.cutoff_read (radius*Real.exp (-(tau/2))) (burnolMultiplicativeDilation (tau/2) value)] with x twice once
  rw [twice]
  by_cases inside : x∈symmetricInterval radius
  · rw [indicator_of_mem inside]
  · rw [indicator_of_notMem inside,once,indicator_of_notMem]
    intro small
    exact inside ⟨by linarith [small.1],by linarith [small.2]⟩

 theorem tate_exterior_quarter (coordinate : BurnolCompletedMellinCoordinate) :
    Cut.cutoff (1/4:ℝ) (burnolTateReciprocalL2 (Paid.exteriorBase coordinate))=
      burnolTateReciprocalL2 (Paid.exteriorBase coordinate) := by
  apply Lp.ext
  have same : Paid.exteriorBase coordinate=burnolNormalizedFirstSourceUnitTail coordinate := rfl
  filter_upwards [Cut.cutoff_read (1/4:ℝ) (burnolTateReciprocalL2 (Paid.exteriorBase coordinate)),
    burnolNormalizedFirstSourceUnitTail_tate_coeFn coordinate] with x cutRead source
  rw [same] at cutRead ⊢
  rw [cutRead]
  by_cases inside : x∈symmetricInterval (1/4:ℝ)
  · rw [indicator_of_mem inside]
  · rw [indicator_of_notMem inside,source,if_neg]
    intro small
    exact inside (abs_le.mp small.le)

 theorem sampled_quarter_zero (column value : BurnolL2)
    (supported : Cut.cutoff (1/4:ℝ) value=value) : inner ℂ (burnolAnnulusSamplingL2 column 0) value=0 := by
  have source := Cut.cutoff_read (1/4:ℝ) value
  rw [supported] at source
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [burnolAnnulusSamplingL2_coeFn column 0,source] with x sample inside
  simp only [Pi.zero_apply]
  rw [sample,inside]
  unfold burnolAnnulusSamplingRaw
  simp only [Nat.cast_zero,zero_add,one_mul]
  by_cases annulus : x∈burnolSamplingAnnulus
  · rw [indicator_of_mem annulus,indicator_of_notMem (show x∉symmetricInterval (1/4:ℝ) from fun bound=>not_le_of_gt annulus.1 (abs_le.mpr bound)),inner_zero_right]
  · rw [indicator_of_notMem annulus,inner_zero_left]

 theorem source_contracted_tate_tail_zero (coordinate : BurnolCompletedMellinCoordinate) (z : ℂ)
    (right : 1/4<z.re) (column : BurnolL2) :
    inner ℂ (burnolAnnulusSamplingL2 column 0) (Paid.Rplus z (burnolTateReciprocalL2 (Paid.exteriorBase coordinate)))=0 := by
  apply sampled_quarter_zero
  have actual := cutoff_Rplus_source (1/4:ℝ) (by norm_num) z right (burnolTateReciprocalL2 (Paid.exteriorBase coordinate))
  rw [tate_exterior_quarter] at actual
  exact actual

 theorem paired_inverse_tate_tail_zero (coordinate : BurnolCompletedMellinCoordinate) (z w : ℂ)
    (rightW : 1/4<w.re) (h : ℝ) :
    inner ℂ (pairedColumn coordinate h) (inverseAction z w (burnolTateReciprocalL2 (Paid.exteriorBase coordinate)))=0 := by
  unfold inverseAction
  rw [inner_sub_right,inner_neg_right,paired_tate_tail_zero,inner_smul_right]
  have source : inner ℂ (pairedColumn coordinate h) (Paid.Rplus w (burnolTateReciprocalL2 (Paid.exteriorBase coordinate)))=0 := by
    rw [pairedColumn,inner_add_left,source_contracted_tate_tail_zero coordinate w rightW,
      source_contracted_tate_tail_zero coordinate w rightW,add_zero]
  rw [source,mul_zero,neg_zero,sub_zero]

end OriginalPrimitiveRankBalance
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
