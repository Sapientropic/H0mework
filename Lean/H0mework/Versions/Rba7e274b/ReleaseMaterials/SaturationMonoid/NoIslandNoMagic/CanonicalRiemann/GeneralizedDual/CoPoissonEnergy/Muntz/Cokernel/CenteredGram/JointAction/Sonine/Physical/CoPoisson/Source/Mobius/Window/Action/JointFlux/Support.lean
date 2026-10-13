import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.JointFlux.Response
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveRank.Contraction
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalJointFluxSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology BigOperators

theorem tate_outer_source_quarter (value : BurnolL2) :
    Paid.cutoff (1/4:ℝ) (burnolTateReciprocalL2 (Paid.outerCut value))=burnolTateReciprocalL2 (Paid.outerCut value) := by
  classical
  have raw : (Paid.outerCut value:ℝ→ℂ)=ᵐ[volume] (fun x=>if x∈symmetricInterval 4 then 0 else value x) := by
    filter_upwards [Lp.coeFn_sub value (Paid.cutoff 4 value),Paid.cutoff_read 4 value] with x subtraction cut
    unfold Paid.outerCut
    change (value-Paid.cutoff 4 value:BurnolL2) x=_
    rw [subtraction]
    change value x-Paid.cutoff 4 value x=_
    rw [cut]
    by_cases inside : x∈symmetricInterval 4
    · simp only [indicator_of_mem inside,if_pos inside,sub_self]
    · simp only [indicator_of_notMem inside,if_neg inside,sub_zero]
  have moved:=burnolTateReciprocalRaw_ae_congr (Lp.memLp (Paid.outerCut value))
    ((Lp.memLp (Paid.outerCut value)).ae_eq raw) raw
  apply Lp.ext
  filter_upwards [Paid.cutoff_read (1/4:ℝ) (burnolTateReciprocalL2 (Paid.outerCut value)),burnolTateReciprocalL2_coeFn (Paid.outerCut value),moved,volume.ae_ne (0:ℝ)] with x cut tate source nonzero
  rw [cut]
  by_cases inside : x∈symmetricInterval (1/4:ℝ)
  · rw [indicator_of_mem inside]
  · rw [indicator_of_notMem inside,tate,source]
    unfold burnolTateReciprocalRaw
    have outside : (1/4:ℝ) < |x| := lt_of_not_ge (fun h=>inside (abs_le.mp h))
    have reciprocal : x⁻¹∈symmetricInterval 4 := by
      apply abs_le.mp
      rw [abs_inv]
      have upper : |x|⁻¹<(1/4:ℝ)⁻¹ := (inv_lt_inv₀ (lt_trans (by norm_num) outside) (by norm_num)).mpr outside
      norm_num at upper
      exact upper.le
    dsimp only
    rw [if_pos reciprocal,mul_zero]

 theorem paired_tate_outer_zero (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) (h : ℝ) :
    inner ℂ (OriginalPrimitiveRankBalance.pairedColumn coordinate h) (burnolTateReciprocalL2 (Paid.outerCut value))=0 := by
  rw [OriginalPrimitiveRankBalance.pairedColumn,inner_add_left,
    OriginalPrimitiveRankBalance.sampled_quarter_zero _ _ (tate_outer_source_quarter value),
    OriginalPrimitiveRankBalance.sampled_quarter_zero _ _ (tate_outer_source_quarter value),add_zero]

 theorem paired_inverse_tate_outer_zero (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (z w : ℂ) (rightW : 1/4<w.re) (h : ℝ) :
    inner ℂ (OriginalPrimitiveRankBalance.pairedColumn coordinate h)
      (OriginalPrimitiveRankBalance.inverseAction z w (burnolTateReciprocalL2 (Paid.outerCut value)))=0 := by
  unfold OriginalPrimitiveRankBalance.inverseAction
  rw [inner_sub_right,inner_neg_right,paired_tate_outer_zero,inner_smul_right]
  have support := OriginalPrimitiveRankBalance.cutoff_Rplus_source (1/4:ℝ) (by norm_num) w rightW (burnolTateReciprocalL2 (Paid.outerCut value))
  rw [tate_outer_source_quarter] at support
  have read : inner ℂ (OriginalPrimitiveRankBalance.pairedColumn coordinate h)
      (Paid.Rplus w (burnolTateReciprocalL2 (Paid.outerCut value)))=0 := by
    rw [OriginalPrimitiveRankBalance.pairedColumn,inner_add_left,
      OriginalPrimitiveRankBalance.sampled_quarter_zero _ _ support,
      OriginalPrimitiveRankBalance.sampled_quarter_zero _ _ support,add_zero]
  rw [read,mul_zero,neg_zero,sub_zero]
end OriginalJointFluxSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
