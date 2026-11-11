import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Weight
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Seed
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Weight
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
open private small_cutoff_tendsto from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ReciprocalSeed

/-- The finite reciprocal weight is the literal original return seed with its small source interval removed. -/
theorem seed_eq_cutoff (c:BurnolCompletedMellinCoordinate) (upper:ℝ) (large:4≤upper) :
 burnolWeightedReciprocalStepSource 4 upper (weight c) (deriv (weight c))=
  E (Constructor.returnState c:Hq)-OriginalPaPhysicalGreen.originalPhysicalCutoff upper⁻¹ (E (Constructor.returnState c:Hq)) := by
 let original:=E (Constructor.returnState c:Hq)
 have source:=weighted_source_coeFn 4 upper (weight c) (deriv (weight c)) (by norm_num) large
  (fun u inside=>(weight_hasDerivAt c u ((by norm_num:(0:ℝ)<4).trans_le inside.1)).differentiableAt.hasDerivAt)
  ((weight_deriv_continuousOn c).mono (fun _ inside=>(by norm_num:(0:ℝ)<4).trans_le inside.1))
  (weight_deriv_measurable c)
 apply Lp.ext
 filter_upwards [source,Lp.coeFn_sub original (OriginalPaPhysicalGreen.originalPhysicalCutoff upper⁻¹ original),
  OriginalPaPhysicalGreen.originalPhysicalCutoff_coeFn upper⁻¹ original,ReturnCounting.seed_read c,volume.ae_ne (0:ℝ)]
  with x generated subAt cutAt originalAt nonzero
 change _=(original-OriginalPaPhysicalGreen.originalPhysicalCutoff upper⁻¹ original:BurnolL2) x
 rw [generated,subAt,Pi.sub_apply,cutAt]
 have absolute:0 < |x|:=abs_pos.mpr nonzero
 have positive:0<upper:=(by norm_num:(0:ℝ)<4).trans_le large
 have lower:4≤|x|⁻¹↔x∈symmetricInterval q:=by
  rw [le_inv_comm₀ (by norm_num:(0:ℝ)<4) absolute]
  change |x|≤(4:ℝ)⁻¹↔-q≤x∧x≤q
  norm_num only [inv_eq_one_div]
  exact abs_le
 have beyond:|x|⁻¹<upper↔x∉symmetricInterval upper⁻¹:=by
  rw [inv_lt_comm₀ absolute positive]
  exact lt_iff_not_ge.trans (not_congr abs_le)
 simp only [burnolReciprocalStepSourceRaw]
 by_cases small:x∈symmetricInterval upper⁻¹
 · rw [indicator_of_mem small,sub_self,if_neg (fun active=>(beyond.mp active.2) small),mul_zero]
 · rw [indicator_of_notMem small,sub_zero]
   by_cases inside:x∈symmetricInterval q
   · rw [if_pos ⟨lower.mpr inside,beyond.mpr small⟩]
     change _=E (Constructor.returnState c:Hq) x
     rw [originalAt,ReturnCounting.seedRaw,if_pos (abs_le.mpr inside)]
     simp only [weight,inv_inv,Complex.ofReal_inv,div_eq_mul_inv]
     rw [mul_inv_cancel_right₀ (Complex.ofReal_ne_zero.mpr absolute.ne')]
   · rw [if_neg (fun active=>inside (lower.mp active.1)),mul_zero]
     change _=E (Constructor.returnState c:Hq) x
     rw [originalAt,ReturnCounting.seedRaw,if_neg (fun h=>inside (abs_le.mp h))]

/-- The removed interval shrinks in the original L² source norm. -/
theorem seed_tendsto (c:BurnolCompletedMellinCoordinate) :
 Tendsto (fun upper:ℝ=>burnolWeightedReciprocalStepSource 4 upper (weight c) (deriv (weight c))) atTop
  (𝓝 (E (Constructor.returnState c:Hq))) := by
 have source:=(tendsto_const_nhds (x:=E (Constructor.returnState c:Hq))).sub
  (small_cutoff_tendsto (E (Constructor.returnState c:Hq)))
 simp only [sub_zero] at source
 apply source.congr'
 filter_upwards [eventually_ge_atTop (4:ℝ)] with upper large
 exact (seed_eq_cutoff c upper large).symm

end OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Seed
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
