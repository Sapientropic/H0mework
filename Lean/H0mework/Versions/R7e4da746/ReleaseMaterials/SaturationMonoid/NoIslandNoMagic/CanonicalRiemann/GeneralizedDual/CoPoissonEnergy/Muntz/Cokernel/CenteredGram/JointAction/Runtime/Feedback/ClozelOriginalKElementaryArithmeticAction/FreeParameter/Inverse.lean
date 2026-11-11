import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.Position
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitResolvent
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.Inverse
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction OriginalKElementaryArithmeticAction.FreeParameter.Position
open scoped InnerProductSpace Topology
open private unit_source_continuous from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitResolvent

def nativeInverse (c:BurnolCompletedMellinCoordinate) : BurnolL2 :=
 unitResolventSource c ConstantDual.value+ReturnCounting.value c

/-- The full original K+b Fourier input has a free-parameter strong source limit. -/
theorem actual_native_inverse_limit (c:BurnolCompletedMellinCoordinate) :
 Tendsto (KCountingSource.finite c) atTop (𝓝 (nativeInverse c)) := by
 have unit:=((unit_source_continuous c).tendsto ConstantDual.value).comp ConstantDual.original_tendsto
 have executed:=unit.congr' (Eventually.of_forall (fun N=>(unit_resolvent_finite c N).symm))
 have complete:=executed.add (ReturnCounting.finite_tendsto c)
 apply complete.congr'
 apply Eventually.of_forall
 intro N
 have original:=elementary_reverse_finite c N
 change DualSource.source N (OriginalKCoefficientBFiniteAction.elementarySource c)+ReturnCounting.finite c N=
  KCountingSource.finite c N
 rw [original]
 module

/-- This limit uses the actual free same-N singular source identity, with its zeta term retained. -/
theorem actual_finite_raw_limit (c:BurnolCompletedMellinCoordinate) (x:ℝ) (nonzero:x≠0) :
 Tendsto (fun N:ℕ=>KCountingSource.raw c N x) atTop (𝓝 (-wholeRaw c x)) := by
 have positive:0<(star c.value).re:=by simp only [star_def,conj_re];linarith [c.rightHalf]
 have notOne:star c.value≠1:=by
  intro same
  have realPart:=congrArg Complex.re same
  simp only [star_def,conj_re,one_re] at realPart
  linarith [c.belowOne]
 have coefficient:=DirichletCoefficient.coefficient_tendsto_riemannZeta (star c.value) positive notOne
 have counted:Tendsto (fun N:ℕ=>PositionCounting.raw c N x) atTop (𝓝 (PositionCounting.eventRaw c x)):=
  tendsto_const_nhds.congr' (by
   filter_upwards [PositionCounting.raw_eventually c x nonzero] with N read
   exact read.symm)
 have complete:=(coefficient.const_mul ((1/2:ℂ)*((|x|:ℝ):ℂ)^(-star c.value))).sub counted
 have target:((1/2:ℂ)*((|x|:ℝ):ℂ)^(-star c.value))*riemannZeta (star c.value)-
    PositionCounting.eventRaw c x= -wholeRaw c x := by
  rw [actual_whole_raw_source]
  ring
 rw [target] at complete
 exact complete.congr' (Eventually.of_forall (fun N=>(KCountingSource.raw_synthesis c N x nonzero).symm))

/-- Independent strong and native raw limits identify the same entire original source. -/
theorem actual_native_inverse_eq (c:BurnolCompletedMellinCoordinate) : nativeInverse c= -wholeValue c := by
 let sequence:=KCountingSource.finite c
 obtain ⟨indices,strict,pointwise⟩:∃indices:ℕ→ℕ,StrictMono indices∧
   ∀ᵐ x:ℝ ∂volume,Tendsto (fun n=>sequence (indices n) x) atTop (𝓝 (nativeInverse c x)):=
  (tendstoInMeasure_of_tendsto_Lp (actual_native_inverse_limit c)).exists_seq_tendsto_ae
 have reads:∀ᵐ x:ℝ ∂volume,∀N:ℕ,sequence N x=KCountingSource.raw c N x:=
  ae_all_iff.mpr (KCountingSource.finite_coeFn c)
 apply Lp.ext
 filter_upwards [pointwise,reads,volume.ae_ne (0:ℝ),actual_whole_value_read c,
  Lp.coeFn_neg (wholeValue c)] with x converges read nonzero original negative
 have expected:=((actual_finite_raw_limit c x nonzero).comp strict.tendsto_atTop).congr'
  (Eventually.of_forall (fun n=>(read (indices n)).symm))
 have same:=tendsto_nhds_unique converges expected
 rw [negative,Pi.neg_apply,original]
 exact same

/-- Literal free-parameter P/b source; the original unit and full return count jointly generate it. -/
theorem actual_whole_inverse_source (c:BurnolCompletedMellinCoordinate) :
 wholeValue c= -unitResolventSource c ConstantDual.value-ReturnCounting.value c := by
 have paid:=congrArg (fun x:BurnolL2=> -x) (actual_native_inverse_eq c)
 simpa only [nativeInverse,neg_add_rev,neg_neg,sub_eq_add_neg,add_comm] using paid.symm

end OriginalKElementaryArithmeticAction.FreeParameter.Inverse
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
