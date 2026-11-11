import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.WholeResidual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactForward
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountingCut

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactForward
open scoped Topology InnerProductSpace
open private dual_dilation from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountingCut
open private seed_limit from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactForward
open private family_integrable from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.WeightedProgram
open private actual_forward_seed from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.FourierSource
local notation "q"=>(1/4:ℝ)
local notation "T"=>burnolTateReciprocalL2
local notation "F"=>fourierL2
local notation "D"=>burnolMultiplicativeDilation
local notation "E"=>burnolQuarterZeroExtension
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "μq"=>volume.restrict (symmetricInterval q)
local notation "H"=>burnolUnitCountingPrimitiveL2
local notation "P"=>burnolUnitReciprocalPrimitiveL2

def poissonPair:BurnolL2→L[ℂ]BurnolL2:=burnolTateReciprocalL2.comp fourierL2.toLinearIsometry.toContinuousLinearMap

private theorem poisson_scale (value:BurnolL2) (a:ℝ):
    poissonPair (burnolSourceScalePrimitive value a)=burnolSourceScalePrimitive (poissonPair value) a:=by
  change T (F (Real.sqrt a • D (Real.log a) value))=
    Real.sqrt a • D (Real.log a) (T (F value))
  simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  rw [map_smul,map_smul,fourierL2_burnolMultiplicativeDilation,
    burnolTateReciprocalL2_dilation_inverse]

private def dualCLM (N:ℕ):BurnolL2→L[ℂ]BurnolL2:=(CountingDual.sourceCLM N).adjoint
private theorem dual_apply (N:ℕ) (value:BurnolL2):dualCLM N value=DualSource.source N value:=
  (CountingDual.dual_eq_adjoint N value).symm

private theorem dual_tate (N:ℕ) (value:BurnolL2):
    DualSource.source N (T value)=T (FiniteForcing.source N value):=by
  have channel (a:ℝ):ContinuousChannels.channel 1 a (T value)=T (ContinuousChannels.channel (-1) a value):=by
    simp only [ContinuousChannels.channel,one_mul,neg_one_mul,map_smul,
      burnolTateReciprocalL2_dilation_inverse]
  have integer (n:ℕ):ContinuousChannels.channel 1 n (T value)=T (Channels.sourceChannel n value):=by
    simpa only [ContinuousChannels.channel,Channels.sourceChannel,one_mul,neg_one_mul] using channel n
  unfold DualSource.source FiniteForcing.source ContinuousChannels.normalization
  simp_rw [integer,channel]
  rw [map_sub,map_sum]
  congr 1
  exact burnolTateReciprocalL2.integral_comp_comm (ContinuousChannels.channel_integrable (-1) N value)

private theorem dual_scale (N:ℕ) (value:BurnolL2) (a:ℝ):
    dualCLM N (burnolSourceScalePrimitive value a)=burnolSourceScalePrimitive (dualCLM N value) a:=by
  simp only [burnolSourceScalePrimitive,RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul]
  simp_rw [dual_apply,dual_dilation]

private def undoQuarter (value:BurnolL2):BurnolL2:=
  (Real.sqrt q)⁻¹ • D (-Real.log q) value

private theorem undo_scale (value:BurnolL2):undoQuarter (burnolSourceScalePrimitive value q)=value:=by
  simp only [undoQuarter,burnolSourceScalePrimitive,RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  rw [map_smul,burnolMultiplicativeDilation_add,neg_add_cancel,burnolMultiplicativeDilation_zero,smul_smul]
  have root:Real.sqrt q=(1/2:ℝ):=by
    rw [show q=(1/2:ℝ)^2 by norm_num,Real.sqrt_sq (by norm_num)]
  rw [root]
  norm_num

/-- The reverse primitive is generated from the actual nonzero constant programme, including its normalization. -/
theorem actual_reverse_primitive:
    Tendsto (fun N:ℕ=>DualSource.source N P) atTop (𝓝 (poissonPair H)):=by
  have source:=(burnolTateReciprocalL2.continuous.tendsto ConstantForward.value).comp ConstantForward.original_tendsto
  have target:T ConstantForward.value=burnolSourceScalePrimitive (poissonPair H) q:=by
    rw [actual_forward_seed,ConstantFourier.reciprocal_value]
    exact poisson_scale H q
  have finite (N:ℕ):T (FiniteForcing.source N ConstantDual.seed)=
      burnolSourceScalePrimitive (DualSource.source N P) q:=by
    rw [←dual_tate,ConstantFourier.reciprocal_source,←dual_apply,dual_scale,dual_apply]
  rw [target] at source
  have scaled:=source.congr' (Eventually.of_forall (fun N=>finite N))
  have continuousUndo:Continuous undoQuarter:=by unfold undoQuarter;fun_prop
  have undone:=(continuousUndo.tendsto _).comp scaled
  change Tendsto (fun N=>undoQuarter (burnolSourceScalePrimitive (DualSource.source N P) q)) atTop
    (𝓝 (undoQuarter (burnolSourceScalePrimitive (poissonPair H) q))) at undone
  simpa only [undo_scale] using undone

private theorem dual_weighted (N:ℕ) (upper:ℝ) (_large:4≤upper) (f f':ℝ→ℂ)
    (regular:ContinuousOn f' (Icc 4 upper)):
    DualSource.source N (burnolWeightedReciprocalStepSource 4 upper f f')=
      WeightedProgram.program 4 upper f f' (DualSource.source N P):=by
  have family:IntegrableOn (fun u:ℝ=>f' u •
      (burnolSourceScalePrimitive P u-burnolSourceScalePrimitive P 4)) (Ioc 4 upper):=
    family_integrable 4 upper f' (by norm_num) regular P
  rw [←dual_apply]
  change dualCLM N (f upper • (burnolSourceScalePrimitive P upper-burnolSourceScalePrimitive P 4)-
    ∫u:ℝ in Ioc 4 upper,f' u • (burnolSourceScalePrimitive P u-burnolSourceScalePrimitive P 4))=
    f upper • (burnolSourceScalePrimitive (DualSource.source N P) upper-burnolSourceScalePrimitive (DualSource.source N P) 4)-
    ∫u:ℝ in Ioc 4 upper,f' u •
      (burnolSourceScalePrimitive (DualSource.source N P) u-burnolSourceScalePrimitive (DualSource.source N P) 4)
  rw [map_sub,map_smul,←(dualCLM N).integral_comp_comm family]
  congr 1
  · rw [map_sub,dual_scale,dual_scale]
    simp only [dual_apply]
  · apply integral_congr_ae
    filter_upwards with u
    change dualCLM N (f' u • (burnolSourceScalePrimitive P u-burnolSourceScalePrimitive P 4))=_
    rw [map_smul,map_sub,dual_scale,dual_scale]
    simp only [dual_apply]

private theorem poisson_program (derivative:ℝ→ℂ) (measured:Measurable derivative)
    (domain:IntegrableOn (InfiniteWeightedProgram.weight derivative) (Ioi 4)):
    InfiniteWeightedProgram.program derivative (poissonPair H)=
      poissonPair (InfiniteWeightedProgram.program derivative H):=by
  rw [InfiniteWeightedProgram.program,InfiniteWeightedProgram.program,map_neg,
    ←poissonPair.integral_comp_comm (InfiniteWeightedProgram.family_integrable derivative measured domain H)]
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  change derivative u • (burnolSourceScalePrimitive (poissonPair H) u-burnolSourceScalePrimitive (poissonPair H) 4)=
    poissonPair (derivative u • (burnolSourceScalePrimitive H u-burnolSourceScalePrimitive H 4))
  rw [map_smul,map_sub,poisson_scale,poisson_scale]

/-- Both complete counting graphs are generated by the same compact source programme and the actual Poisson primitive. -/
theorem actual_compact_reverse (state:Hq) (raw:ℝ→ℂ)
    (represents:(state:ℝ→ℂ)=ᵐ[μq]raw)
    (even:∀x∈symmetricInterval q,raw |x|=raw x)
    (weightDerivative:∀u:ℝ,4≤u→HasDerivAt (weight raw) (deriv (weight raw) u) u)
    (slopeContinuous:ContinuousOn (deriv (weight raw)) (Ici 4))
    (domain:IntegrableOn (InfiniteWeightedProgram.weight (deriv (weight raw))) (Ioi 4))
    (head:Tendsto (fun upper:ℝ=>Real.sqrt upper*‖weight raw upper‖) atTop (𝓝 0)):
    Tendsto (fun N:ℕ=>DualSource.source N (E state)) atTop
      (𝓝 (poissonPair (InfiniteWeightedProgram.program (deriv (weight raw)) H))):=by
  have finite (N:ℕ):DualSource.source N (E state)=
      InfiniteWeightedProgram.program (deriv (weight raw)) (DualSource.source N P):=by
    have seed:=((dualCLM N).continuous.tendsto (E state)).comp
      (seed_limit state raw represents even weightDerivative slopeContinuous)
    simp only [dual_apply] at seed
    have programme:=InfiniteWeightedProgram.finite_program_tendsto (weight raw) (deriv (weight raw))
      (measurable_deriv _) domain head (DualSource.source N P)
    have same:=seed.congr' (show _=ᶠ[atTop] (fun upper:ℝ=>
        WeightedProgram.program 4 upper (weight raw) (deriv (weight raw)) (DualSource.source N P)) from by
      filter_upwards [eventually_ge_atTop (4:ℝ)] with upper large
      dsimp only [Function.comp_apply]
      rw [dual_apply]
      exact dual_weighted N upper large _ _ (slopeContinuous.mono (fun _ inside=>inside.1)))
    exact tendsto_nhds_unique same programme
  have source:=InfiniteWeightedProgram.program_tendsto (deriv (weight raw)) (measurable_deriv _) domain
    (fun N=>DualSource.source N P) (poissonPair H) actual_reverse_primitive
  rw [poisson_program _ (measurable_deriv _) domain] at source
  exact source.congr' (Eventually.of_forall (fun N=>(finite N).symm))

/-- The common forward programme realizes the source on every original Schwartz test. -/
theorem actual_compact_realizes (state:Hq) (raw:ℝ→ℂ)
    (represents:(state:ℝ→ℂ)=ᵐ[μq]raw)
    (even:∀x∈symmetricInterval q,raw |x|=raw x)
    (weightDerivative:∀u:ℝ,4≤u→HasDerivAt (weight raw) (deriv (weight raw) u) u)
    (slopeContinuous:ContinuousOn (deriv (weight raw)) (Ici 4))
    (domain:IntegrableOn (InfiniteWeightedProgram.weight (deriv (weight raw))) (Ioi 4))
    (head:Tendsto (fun upper:ℝ=>Real.sqrt upper*‖weight raw upper‖) atTop (𝓝 0))
    (test:SchwartzMap ℝ ℂ):
    burnolRemainderSourceRead (E state) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (InfiniteWeightedProgram.program (deriv (weight raw)) H)) test:=by
  have seed:=((burnolRemainderSourceReadCLM test).continuous.tendsto (E state)).comp
    (seed_limit state raw represents even weightDerivative slopeContinuous)
  have continuousRead:Continuous (fun value:BurnolL2=>(Lp.toTemperedDistributionCLM ℂ volume 2 value) test):=by fun_prop
  have programme:=(continuousRead.tendsto _).comp
    (InfiniteWeightedProgram.finite_program_tendsto (weight raw) (deriv (weight raw))
      (measurable_deriv _) domain head H)
  have same:=seed.congr' (show _=ᶠ[atTop] (fun upper:ℝ=>
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (burnolWeightedReciprocalStepWave 4 upper (weight raw) (deriv (weight raw)))) test) from by
    filter_upwards [eventually_ge_atTop (4:ℝ)] with upper large
    dsimp only [Function.comp_apply]
    rw [burnolRemainderSourceReadCLM_apply]
    exact AmbientFourier.weighted_realizes upper large _ _
      (slopeContinuous.mono (fun _ inside=>inside.1)) test)
  simp only [WeightedProgram.program_original] at programme
  simpa only [burnolRemainderSourceReadCLM_apply] using tendsto_nhds_unique same programme

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
