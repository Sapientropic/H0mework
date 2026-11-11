import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Paired
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Raw

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Realized
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Paired OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.StrongIdentification
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Realizer OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountingCut OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.JointSource
open scoped Topology InnerProductSpace
open private dual_dilation from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountingCut
local notation "T"=>burnolTateReciprocalL2
local notation "F"=>fourierL2
local notation "D"=>burnolMultiplicativeDilation
local notation "A"=>sourceAnnulusCut
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate

/-- The complete same-N strong graph is the original joint field, including its actual Unit. -/
theorem actual_original_joint_forward_value (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    forwardValue c zero=jointValue c zero h positive:=by
  obtain ⟨B,_nonnegative,growth⟩:=OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Raw.actual_global_growth c zero
  have rawLp:MemLp (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Raw.raw c) 2 volume:=
    (Lp.memLp (jointSource c)).ae_eq (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Raw.actual_source c)
  have paired (test:SchwartzMap ℝ ℂ):
      Integrable (fun x:ℝ=>OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Raw.raw c x*coPoissonMuntzScaleRemainder test |x|):=
    rawLp.integrable_mul ((Lp.memLp (burnolRemainderL2Kernel test)).ae_eq (burnolRemainderL2Kernel_coeFn test))
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (μ:=volume))
  ext test
  have graph:=actual_strong_realizes (jointSource c) (forwardValue c zero)
    (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Raw.raw c) (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Raw.actual_source c)
    (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Raw.actual_measurable c) (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Raw.actual_origin c zero)
    (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Raw.actual_even c) B growth
    (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Raw.actual_reciprocal_domain c zero)
    (actual_joint_forward_graph c zero) test (paired test)
  exact graph.symm.trans (actual_joint_realizes c zero h positive test)

/-- Reverse and forward are now the same specified physical occurrence, beyond source-kernel ambiguity. -/
theorem actual_original_joint_reverse_value (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    reverseValue c=T (F (jointValue c zero h positive)):=by
  rw [actual_joint_paired_value c zero,actual_original_joint_forward_value c zero h positive]
  rfl

private theorem reverse_power (N:ℕ) (d:BurnolCompletedMellinCoordinate) (j:ℕ) (value:BurnolL2):
    DualSource.source N (((sourceVolterraResolvent d)^j) value)=
      ((sourceVolterraResolvent d)^j) (DualSource.source N value):=by
  induction j with
  | zero=>simp only [pow_zero,one_apply_eq_self]
  | succ j previous=>
    rw [pow_succ',mul_apply_eq_comp,actual_reverse_volterra,previous,mul_apply_eq_comp]

private theorem actual_outgoing_value (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h) (j:ℕ):
    ((sourceVolterraResolvent (barC c))^j) (reverseValue c)=T (directValue c zero h positive j):=by
  rw [actual_original_joint_reverse_value c zero h positive]
  induction j with
  | zero=>simp only [pow_zero,one_apply_eq_self,directValue]
  | succ j previous=>
    rw [pow_succ',mul_apply_eq_comp,previous]
    simp only [sourceVolterraResolvent,ContinuousLinearMap.comp_apply,burnolTateReciprocalL2_involutive,
      directValue,pow_succ',mul_apply_eq_comp]

/-- Original R acts on the complete actual field before either cut, at every finite order. -/
theorem actual_original_joint_reverse_graph (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h) (j:ℕ):
    Tendsto (fun N:ℕ=>DualSource.source N (tateSource c j)) atTop
      (𝓝 (T (directValue c zero h positive j))):=by
  have generated:=(((sourceVolterraResolvent (barC c))^j).continuous.tendsto _).comp
    (actual_joint_reverse_graph c zero)
  rw [actual_outgoing_value c zero h positive j] at generated
  have finite (N:ℕ):DualSource.source N (tateSource c j)=
      ((sourceVolterraResolvent (barC c))^j) (DualSource.source N (jointSource c)):=by
    rw [actual_tate_outgoing,reverse_power]
  exact generated.congr' (Eventually.of_forall (fun N=>(finite N).symm))

/-- The fixed source displacement is taken on the whole acted source before the physical cut. -/
theorem actual_fixed_joint_graph (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h) (j:ℕ):
    Tendsto (fun N:ℕ=>A (DualSource.source N
        (D (-Real.log stageZeroSonineQ) (tateSource c j)))) atTop
      (𝓝 (A (D (-Real.log stageZeroSonineQ) (T (directValue c zero h positive j))))):=by
  have generated:=((D (-Real.log stageZeroSonineQ)).continuous.tendsto _).comp
    (actual_original_joint_reverse_graph c zero h positive j)
  have moved:Tendsto (fun N:ℕ=>DualSource.source N (D (-Real.log stageZeroSonineQ) (tateSource c j))) atTop
      (𝓝 (D (-Real.log stageZeroSonineQ) (T (directValue c zero h positive j)))):=
    generated.congr' (Eventually.of_forall (fun N=>(dual_dilation N (-Real.log stageZeroSonineQ) (tateSource c j)).symm))
  exact (sourceAnnulusCut.continuous.tendsto _).comp moved

/-- The original owner, original Xi order and original fixed shift consume this complete field graph. -/
theorem actual_original_order_fixed_graph (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    let m:=generatedRiemannXiZeroOrder ActualAnalyticOwner c.value
    Tendsto (fun N:ℕ=>A (DualSource.source N
        (D (-Real.log stageZeroSonineQ) (tateSource c m)))) atTop
      (𝓝 (A (D (-Real.log stageZeroSonineQ) (T (directValue c zero h positive m))))):=
  actual_fixed_joint_graph c zero h positive _

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Realized
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
