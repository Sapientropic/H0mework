import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Seed
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Program
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Weight OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Seed
open scoped InnerProductSpace Topology SchwartzMap
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension

theorem actual_finite_source (c:BurnolCompletedMellinCoordinate) (N:ℕ) :
 FiniteForcing.source N (E (Constructor.returnState c:Hq))=
  InfiniteWeightedProgram.program (deriv (weight c)) (Prefix.primitiveL2 N) := by
 have sourceLimit:=((FiniteSourceContinuity.source_continuous N).tendsto _).comp (seed_tendsto c)
 have programmeLimit:=InfiniteWeightedProgram.finite_program_tendsto
  (weight c) (deriv (weight c)) (weight_deriv_measurable c) (derivative_weight_integrable c)
  (head_tendsto_zero c) (Prefix.primitiveL2 N)
 have sameLimit:=sourceLimit.congr' (show _=ᶠ[atTop]
  (fun upper:ℝ=>WeightedProgram.program 4 upper (weight c) (deriv (weight c)) (Prefix.primitiveL2 N)) from by
  filter_upwards [eventually_ge_atTop (4:ℝ)] with upper after
  exact (weighted_prefix_eq_finite_sub_continuous _ _ _ _ N (by norm_num) after
   (fun u inside=>(weight_hasDerivAt c u ((by norm_num:(0:ℝ)<4).trans_le inside.1)).differentiableAt.hasDerivAt)
   ((weight_deriv_continuousOn c).mono (fun _ inside=>(by norm_num:(0:ℝ)<4).trans_le inside.1))
   (weight_deriv_measurable c) (weight_measurable c)).symm)
 exact tendsto_nhds_unique sameLimit programmeLimit

/-- The entire original return forward programme is paid by its own actual reciprocal weight. -/
theorem actual_forward_program (c:BurnolCompletedMellinCoordinate) :
 ReturnCounting.forwardValue c=InfiniteWeightedProgram.program (deriv (weight c)) burnolUnitCountingPrimitiveL2 := by
 have programmeLimit:=InfiniteWeightedProgram.program_tendsto (deriv (weight c)) (weight_deriv_measurable c)
  (derivative_weight_integrable c) Prefix.primitiveL2 burnolUnitCountingPrimitiveL2 Prefix.primitive_tendsto
 have same:=programmeLimit.congr' (Eventually.of_forall (fun N=>(actual_finite_source c N).symm))
 exact tendsto_nhds_unique (ReturnCounting.forward_tendsto c) same

/-- The full co-Poisson source realization comes from these same finite heads and full tails. -/
theorem actual_forward_realizes (c:BurnolCompletedMellinCoordinate) (test:SchwartzMap ℝ ℂ) :
 burnolRemainderSourceRead (E (Constructor.returnState c:Hq)) test=
  (Lp.toTemperedDistributionCLM ℂ volume 2 (ReturnCounting.forwardValue c)) test := by
 have sourceLimit:=((burnolRemainderSourceReadCLM test).continuous.tendsto _).comp (seed_tendsto c)
 have continuousRead:Continuous (fun value:BurnolL2=>(Lp.toTemperedDistributionCLM ℂ volume 2 value) test):=by fun_prop
 have waveLimit:=(continuousRead.tendsto _).comp
  (InfiniteWeightedProgram.finite_program_tendsto (weight c) (deriv (weight c)) (weight_deriv_measurable c)
   (derivative_weight_integrable c) (head_tendsto_zero c) burnolUnitCountingPrimitiveL2)
 have actual:=sourceLimit.congr' (show _=ᶠ[atTop]
  (fun upper:ℝ=>(Lp.toTemperedDistributionCLM ℂ volume 2
   (burnolWeightedReciprocalStepWave 4 upper (weight c) (deriv (weight c)))) test) from by
  filter_upwards [eventually_ge_atTop (4:ℝ)] with upper large
  dsimp only [Function.comp_apply]
  rw [burnolRemainderSourceReadCLM_apply]
  exact AmbientFourier.weighted_realizes upper large _ _
   ((weight_deriv_continuousOn c).mono (fun _ inside=>(by norm_num:(0:ℝ)<4).trans_le inside.1)) test)
 simp only [WeightedProgram.program_original] at waveLimit
 rw [←actual_forward_program c] at waveLimit
 simpa only [burnolRemainderSourceReadCLM_apply] using tendsto_nhds_unique actual waveLimit

end OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Program
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
