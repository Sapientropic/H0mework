import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Realizer

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactForward
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalPaPhysicalGreen OriginalRieszFinitePairing.CoPoisson.Ward
open scoped Topology InnerProductSpace
open private small_cutoff_tendsto from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ReciprocalSeed
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "E" => burnolQuarterZeroExtension

def weight (raw:ℝ→ℂ) (u:ℝ):ℂ:=raw u⁻¹/(u:ℂ)

private theorem seed_cut (state:Hq) (raw:ℝ→ℂ)
    (represents:(state:ℝ→ℂ)=ᵐ[μq]raw)
    (even:∀x∈symmetricInterval q,raw |x|=raw x)
    (weightDerivative:∀u:ℝ,4≤u→HasDerivAt (weight raw) (deriv (weight raw) u) u)
    (slopeContinuous:ContinuousOn (deriv (weight raw)) (Ici 4)) (upper:ℝ) (large:4≤upper):
    burnolWeightedReciprocalStepSource 4 upper (weight raw) (deriv (weight raw))=
      E state-originalPhysicalCutoff upper⁻¹ (E state):=by
  have source:=weighted_source_coeFn 4 upper (weight raw) (deriv (weight raw)) (by norm_num) large
    (fun u inside=>weightDerivative u inside.1)
    (slopeContinuous.mono (fun _ inside=>inside.1)) (measurable_deriv _)
  have actual:∀ᵐx:ℝ∂volume,x∈symmetricInterval q→state x=raw x:=
    (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp represents
  apply Lp.ext
  filter_upwards [source,Lp.coeFn_sub (E state) (originalPhysicalCutoff upper⁻¹ (E state)),
    originalPhysicalCutoff_coeFn upper⁻¹ (E state),burnolQuarterZeroExtension_coe state,
    actual,volume.ae_ne (0:ℝ)] with x primitive difference cutoff extended rawAt nonzero
  rw [primitive,difference,Pi.sub_apply,cutoff]
  have absolute : 0 < |x| := abs_pos.mpr nonzero
  have positive:0<upper:=lt_of_lt_of_le (by norm_num) large
  have lower:4≤|x|⁻¹↔x∈symmetricInterval q:=by
    rw [le_inv_comm₀ (by norm_num : (0:ℝ)<4) absolute]
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
    · rw [if_pos ⟨lower.mpr inside,beyond.mpr small⟩,extended,indicator_of_mem inside,rawAt inside]
      simp only [weight,inv_inv,Complex.ofReal_inv,div_eq_mul_inv]
      rw [mul_inv_cancel_right₀ (Complex.ofReal_ne_zero.mpr absolute.ne'),even x inside]
    · rw [if_neg (fun active=>inside (lower.mp active.1)),mul_zero,extended,indicator_of_notMem inside]

private theorem seed_limit (state:Hq) (raw:ℝ→ℂ)
    (represents:(state:ℝ→ℂ)=ᵐ[μq]raw)
    (even:∀x∈symmetricInterval q,raw |x|=raw x)
    (weightDerivative:∀u:ℝ,4≤u→HasDerivAt (weight raw) (deriv (weight raw) u) u)
    (slopeContinuous:ContinuousOn (deriv (weight raw)) (Ici 4)):
    Tendsto (fun upper:ℝ=>burnolWeightedReciprocalStepSource 4 upper (weight raw) (deriv (weight raw)))
      atTop (𝓝 (E state)):=by
  have original:=(tendsto_const_nhds (x:=E state)).sub (small_cutoff_tendsto (E state))
  simp only [sub_zero] at original
  apply original.congr'
  filter_upwards [eventually_ge_atTop (4:ℝ)] with upper large
  exact (seed_cut state raw represents even weightDerivative slopeContinuous upper large).symm

/-- The existing infinite source engine supplies the full ambient strong graph of this exact compact source. -/
theorem actual_compact_forward (state:Hq) (raw:ℝ→ℂ)
    (represents:(state:ℝ→ℂ)=ᵐ[μq]raw)
    (even:∀x∈symmetricInterval q,raw |x|=raw x)
    (weightDerivative:∀u:ℝ,4≤u→HasDerivAt (weight raw) (deriv (weight raw) u) u)
    (slopeContinuous:ContinuousOn (deriv (weight raw)) (Ici 4))
    (measured:Measurable (weight raw))
    (domain:IntegrableOn (InfiniteWeightedProgram.weight (deriv (weight raw))) (Ioi 4))
    (head:Tendsto (fun upper:ℝ=>Real.sqrt upper*‖weight raw upper‖) atTop (𝓝 0)):
    Tendsto (fun N:ℕ=>FiniteForcing.source N (E state)) atTop
      (𝓝 (InfiniteWeightedProgram.program (deriv (weight raw)) burnolUnitCountingPrimitiveL2)):=by
  have finite (N:ℕ):FiniteForcing.source N (E state)=
      InfiniteWeightedProgram.program (deriv (weight raw)) (Prefix.primitiveL2 N):=by
    have source:=((FiniteSourceContinuity.source_continuous N).tendsto (E state)).comp
      (seed_limit state raw represents even weightDerivative slopeContinuous)
    have target:=InfiniteWeightedProgram.finite_program_tendsto (weight raw) (deriv (weight raw))
      (measurable_deriv _) domain head (Prefix.primitiveL2 N)
    have same:=source.congr' (show _=ᶠ[atTop](fun upper:ℝ=>WeightedProgram.program 4 upper (weight raw)
        (deriv (weight raw)) (Prefix.primitiveL2 N)) from by
      filter_upwards [eventually_ge_atTop (4:ℝ)] with upper large
      exact (weighted_prefix_eq_finite_sub_continuous 4 upper (weight raw) (deriv (weight raw)) N
        (by norm_num) large (fun u inside=>weightDerivative u inside.1)
        (slopeContinuous.mono (fun _ inside=>inside.1)) (measurable_deriv _) measured).symm)
    exact tendsto_nhds_unique same target
  have source:=InfiniteWeightedProgram.program_tendsto (deriv (weight raw)) (measurable_deriv _) domain
    Prefix.primitiveL2 burnolUnitCountingPrimitiveL2 Prefix.primitive_tendsto
  exact source.congr' (Eventually.of_forall (fun N=>(finite N).symm))

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactForward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
