import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Resolvent
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CompactPhysical

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Field
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalKCoefficientBFiniteAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Mellin
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CountedXi OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Resolvent
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CompactPhysical
open scoped Topology InnerProductSpace
local notation "q"=>(1/4:ℝ)
local notation "Rq"=>burnolQuarterRestriction
local notation "E"=>burnolQuarterZeroExtension
local notation "P"=>burnolEvenAmbientProjection
local notation "order"=>generatedRiemannXiZeroOrder ActualAnalyticOwner
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "bare"=>generatedRiemannBareZeroLocalizedSpectrum ActualAnalyticOwner
local instance physicalComplete:CompleteSpace BurnolPaAmbientCarrier:=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem native_exterior_jet (d:BurnolCompletedMellinCoordinate) (value:BurnolL2) (j:ℕ):
    iteratedDeriv j (fun z:ℂ=>exterior (burnolDirectRightResolvent (z/2) value)) d.value=
      ((j.factorial:ℂ)/(2:ℂ)^j) • exterior (((burnolDirectRightResolventCLM d)^(j+1)) value):=by
  have commute:iteratedDeriv j (fun z:ℂ=>exterior (burnolDirectRightResolvent (z/2) value)) d.value=
      exterior (iteratedDeriv j (fun z:ℂ=>burnolDirectRightResolvent (z/2) value) d.value):=by
    change (iteratedFDeriv ℂ j (exterior ∘ (fun z:ℂ=>burnolDirectRightResolvent (z/2) value))
      d.value) (fun _=>1)=_
    rw [exterior.iteratedFDeriv_comp_left
      ((OriginalRResolventParameterJet.parameter_analytic d value).contDiffAt (n:=j)) le_rfl]
    rfl
  rw [commute,OriginalRResolventParameterJet.parameter_jet,map_smul]

private theorem first_nonzero_product {f:ℂ→ℂ} {v:ℂ→BurnolL2} {s:ℂ}
    (hf:AnalyticAt ℂ f s) (hv:AnalyticAt ℂ v s) (j:ℕ)
    (lower:∀i<j,iteratedDeriv i f s=0):
    iteratedDeriv j (fun z=>f z • v z) s=iteratedDeriv j f s • v s:=by
  classical
  have expansion:iteratedDeriv j (fun z=>f z • v z) s=
      ∑i∈Finset.range (j+1),j.choose i •
        (iteratedDeriv i f s • iteratedDeriv (j-i) v s):=by
    simpa only [iteratedDerivWithin_univ,Pi.smul_apply,smul_assoc] using!
      iteratedDerivWithin_smul (Set.mem_univ s) uniqueDiffOn_univ
        (hf.contDiffAt.contDiffWithinAt (n:=j)) (hv.contDiffAt.contDiffWithinAt (n:=j))
  rw [expansion,Finset.sum_eq_single j]
  · simp only [Nat.choose_self,one_smul,Nat.sub_self,iteratedDeriv_zero]
  · intro i member different
    have before:i<j:=by have:=Finset.mem_range.mp member;omega
    rw [lower i before,zero_smul,smul_zero]
  · intro absent
    exact (absent (Finset.mem_range.mpr (by omega))).elim

private def boxFamily (z:ℂ):BurnolL2:=
  (z*(q:ℂ)^(-z)) • exterior (burnolDirectRightResolvent (z/2) ConstantDual.seed)

private theorem boxFamily_analytic (d:BurnolCompletedMellinCoordinate):
    AnalyticAt ℂ boxFamily d.value:=by
  have scalar:AnalyticAt ℂ (fun z:ℂ=>z*(q:ℂ)^(-z)) d.value:=
    (differentiable_id.mul ((differentiable_id.neg).const_cpow
      (Or.inl (by norm_num:(q:ℂ)≠0)))).analyticAt d.value
  have vector:AnalyticAt ℂ (fun z:ℂ=>exterior (burnolDirectRightResolvent (z/2) ConstantDual.seed))
      d.value:=(exterior.analyticAt _).comp
        (OriginalRResolventParameterJet.parameter_analytic d ConstantDual.seed)
  exact scalar.smul vector

private theorem source_exterior_germ (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    (fun z:ℂ=>exterior (burnolDirectRightResolvent (z/2) (fullFloorValue c zero)))=ᶠ[𝓝 (star c.value)]
      (fun z:ℂ=>mellin (fullFloorRaw c) z • boxFamily z):=by
  have right:∀ᶠz:ℂ in 𝓝 (star c.value),(1/2:ℝ)<z.re:=
    (continuous_re.tendsto (star c.value)).eventually (Ioi_mem_nhds
      (by simpa only [star_def,conj_re] using c.rightHalf))
  have below:∀ᶠz:ℂ in 𝓝 (star c.value),z.re<1:=
    (continuous_re.tendsto (star c.value)).eventually (Iio_mem_nhds
      (by simpa only [star_def,conj_re] using c.belowOne))
  filter_upwards [right,below] with z hr hb
  have source:=actual_exterior_resolvent c ⟨z,hr,hb⟩ zero
  change exterior (burnolDirectRightResolvent (z/2) (fullFloorValue c zero))=
    exteriorCoefficient c z • exterior (burnolDirectRightResolvent (z/2) ConstantDual.seed) at source
  rw [source,boxFamily,smul_smul,exteriorCoefficient]
  congr 1
  ring

def tailAmplitude (c:BurnolCompletedMellinCoordinate):ℂ:=
  (2:ℂ)^(order c.value-1)*bare (star c.value) (star c.value)/2*
    (star c.value*(q:ℂ)^(-star c.value))

/-- The original R power consumes the full genuine low-jet vanishing before its exterior is read. -/
theorem actual_power_exterior (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    exterior (((burnolDirectRightResolventCLM (barC c))^(order c.value)) (fullFloorValue c zero))=
      tailAmplitude c • exterior (burnolDirectRightResolvent (star c.value/2) ConstantDual.seed):=by
  have positive:0<order c.value:=generatedRiemannXiZeroOrder_pos
    (burnolPaZeroObservation c zero) (burnolPaZeroObservation_nontrivial c zero)
  have analytic:AnalyticAt ℂ (mellin (fullFloorRaw c)) (star c.value):=
    (((analyticAt_id.sub analyticAt_const).pow (order c.value-1)).mul
      (actual_complement_analytic c)).congr (actual_original_order_germ c zero).symm
  have product:=first_nonzero_product analytic (boxFamily_analytic (barC c))
    (order c.value-1) (actual_count_lower_jet c zero)
  have source:=(source_exterior_germ c zero).iteratedDeriv_eq (order c.value-1)
  have native:=native_exterior_jet (barC c) (fullFloorValue c zero) (order c.value-1)
  change iteratedDeriv (order c.value-1)
    (fun z:ℂ=>exterior (burnolDirectRightResolvent (z/2) (fullFloorValue c zero))) (star c.value)=_ at native
  rw [native,product,actual_count_top_jet c zero,
    show order c.value-1+1=order c.value by omega] at source
  have rescaled:=congrArg (fun v:BurnolL2=>((2:ℂ)^(order c.value-1)/
    ((order c.value-1).factorial:ℂ)) • v) source
  have factorial:((order c.value-1).factorial:ℂ)≠0:=by exact_mod_cast Nat.factorial_ne_zero _
  have cancel:(2:ℂ)^(order c.value-1)/((order c.value-1).factorial:ℂ)*
      (((order c.value-1).factorial:ℂ)/(2:ℂ)^(order c.value-1))=1:=by
    field_simp [factorial]
  rw [smul_smul,cancel,one_smul,boxFamily,smul_smul,smul_smul] at rescaled
  have coefficient:(2:ℂ)^(order c.value-1)/((order c.value-1).factorial:ℂ)*
      (((order c.value-1).factorial:ℂ)*bare (star c.value) (star c.value)/2)*
      (star c.value*(q:ℂ)^(-star c.value))=tailAmplitude c:=by
    unfold tailAmplitude
    field_simp [factorial]
  rw [coefficient] at rescaled
  exact rescaled

def rieszAmplitude (c:BurnolCompletedMellinCoordinate):ℂ:=
  -(2:ℂ)^(order c.value)*bare (star c.value) (star c.value)

private theorem elementary_exterior (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    exterior (((burnolDirectRightResolventCLM (barC c))^(order c.value)) (fullFloorValue c zero))=
      rieszAmplitude c • exterior (elementarySource c):=by
  have positive:0<order c.value:=generatedRiemannXiZeroOrder_pos
    (burnolPaZeroObservation c zero) (burnolPaZeroObservation_nontrivial c zero)
  have boxZero:exterior ConstantDual.seed=0:=by
    rw [actual_exterior_apply,ConstantDual.seed,burnolQuarterRestriction_zeroExtension,sub_self]
  have resolved:=congrArg exterior (actual_resolved_R_source c)
  rw [resolvedSource,map_sub,map_smul,boxZero,smul_zero,sub_zero,map_smul] at resolved
  rw [actual_power_exterior]
  rw [resolved,smul_smul]
  congr 1
  unfold tailAmplitude rieszAmplitude
  have power:(2:ℂ)^(order c.value)=(2:ℂ)^(order c.value-1)*2:=by
    conv_lhs=>rw [show order c.value=(order c.value-1)+1 by omega]
    rw [pow_succ]
  rw [power]
  ring

def powerValue (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):BurnolL2:=
  ((burnolDirectRightResolventCLM (barC c))^(order c.value)) (fullFloorValue c zero)

def compactCorrection (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):BurnolQuarterIntervalL2:=
  Rq (powerValue c zero-rieszAmplitude c • elementarySource c)

/-- The full original R iterate has the original elementary K tail and its actual compact correction. -/
theorem actual_power_full_field (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    powerValue c zero=rieszAmplitude c • elementarySource c+E (compactCorrection c zero):=by
  have source:=elementary_exterior c zero
  change exterior (powerValue c zero)=rieszAmplitude c • exterior (elementarySource c) at source
  simp only [actual_exterior_apply] at source
  unfold compactCorrection
  rw [map_sub,map_smul,map_sub,map_smul]
  linear_combination (norm:=module) source

private theorem elementary_projection (c:BurnolCompletedMellinCoordinate):
    P (elementarySource c)=burnolCompletedMellinRieszVector c:=by
  unfold elementarySource
  have odd:P (burnolAmbientCompletedMellinKernelFormula c-
      burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula c))=0:=by
    apply Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
    intro test membership
    rw [inner_eq_zero_symm]
    exact burnolAmbientOddResidual_inner_physical_eq_zero _ ⟨test,membership⟩
  rw [map_sub] at odd
  rw [←sub_eq_zero.mp odd]
  rw [←burnolAmbientCompletedMellinRieszVector_eq_kernelFormula,
    burnolCompletedMellinRieszVector_eq_ambientProjection]
  rfl

/-- Projection acts after R^m; the complete compact mass remains as the actual physical Unit. -/
theorem actual_power_physical_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    P (powerValue c zero)=rieszAmplitude c • burnolCompletedMellinRieszVector c+
      burnolQuarterMeanCoefficient (compactCorrection c zero) • P ConstantDual.seed:=by
  rw [actual_power_full_field,map_add,map_smul,elementary_projection,actual_compact_projection]
  rfl

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Field
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
