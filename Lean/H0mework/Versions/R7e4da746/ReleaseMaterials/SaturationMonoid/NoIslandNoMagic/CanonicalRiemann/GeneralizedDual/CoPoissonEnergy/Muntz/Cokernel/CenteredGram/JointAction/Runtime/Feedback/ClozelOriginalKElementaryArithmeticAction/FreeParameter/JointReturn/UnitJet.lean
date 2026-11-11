import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.JointReturn.CrossJet
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.RadiusConsumer
import H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitShell.Difference
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.UnitJet
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.FreeParameter.Riesz OriginalKElementaryArithmeticAction.FreeParameter.UnitSplice OriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer
open OriginalKElementaryArithmeticAction.FreeParameter.RadiusConsumer OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.CrossContact OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.CrossJet
open scoped InnerProductSpace Topology
local notation "R" => burnolDirectRightResolventCLM
local notation "q" => (1/4:ℝ)

def normalizedUnit (base:BurnolCompletedMellinCoordinate) (s:ℂ) : BurnolL2 :=
 burnolUnitTailResponse base 4+((s-base.value)/2)•burnolDirectRightResolvent (s/2) (burnolUnitTailResponse base 4)

def unitJet (base:BurnolCompletedMellinCoordinate) (j:ℕ) : BurnolL2 :=
 ((R base)^j) (burnolUnitTailResponse base 4)

theorem normalized_unit_analytic (base:BurnolCompletedMellinCoordinate) :
 AnalyticAt ℂ (normalizedUnit base) base.value :=
 analyticAt_const.add (((analyticAt_id.sub analyticAt_const).div_const).smul
  (OriginalRResolventParameterJet.parameter_analytic base (burnolUnitTailResponse base 4)))

private theorem step_jet (b:ℂ) (j:ℕ) :
 iteratedDeriv j (fun s:ℂ=>(s-b)/2) b=if j=1 then (1/2:ℂ) else 0 := by
 have derivative:deriv (fun s:ℂ=>(s-b)/2)=fun _=>1/2:=by
  funext s
  exact (((hasDerivAt_id s).sub_const b).div_const (2:ℂ)).deriv
 rcases j with _|j
 · simp
 rcases j with _|j
 · simp only [Nat.zero_add,ite_true,iteratedDeriv_one,derivative]
 · rw [iteratedDeriv_succ',derivative]
   rw [iteratedDeriv_const]
   simp

/-- The true free Unit source supplies each resolvent word, including the original top word. -/
theorem normalized_unit_jet (base:BurnolCompletedMellinCoordinate) (j:ℕ) :
 iteratedDeriv j (normalizedUnit base) base.value=((j.factorial:ℂ)/(2:ℂ)^j)•unitJet base j := by
 rcases j with _|j
 · simp [normalizedUnit,unitJet]
 have regular:=OriginalRResolventParameterJet.parameter_analytic base (burnolUnitTailResponse base 4)
 have scalar:AnalyticAt ℂ (fun s:ℂ=>(s-base.value)/2) base.value:=
  (analyticAt_id.sub analyticAt_const).div_const
 have original:normalizedUnit base=(fun _=>burnolUnitTailResponse base 4)+
   (fun s:ℂ=>((s-base.value)/2)•burnolDirectRightResolvent (s/2) (burnolUnitTailResponse base 4)):=rfl
 rw [original]
 change iteratedDeriv (j+1) (fun s=>burnolUnitTailResponse base 4+
  ((s-base.value)/2)•burnolDirectRightResolvent (s/2) (burnolUnitTailResponse base 4)) base.value=_
 rw [iteratedDeriv_const_add (Nat.succ_pos j)]
 have scalarCD:ContDiffAt ℂ (j+1:ℕ) (fun s:ℂ=>(s-base.value)/2) base.value:=scalar.contDiffAt
 have regularCD:ContDiffAt ℂ (j+1:ℕ) (fun s:ℂ=>burnolDirectRightResolvent (s/2) (burnolUnitTailResponse base 4)) base.value:=regular.contDiffAt
 have word:=iteratedDerivWithin_smul (Set.mem_univ base.value) uniqueDiffOn_univ
  scalarCD.contDiffWithinAt regularCD.contDiffWithinAt
 simp only [iteratedDerivWithin_univ] at word
 change iteratedDeriv (j+1) (fun s:ℂ=>((s-base.value)/2)•
  burnolDirectRightResolvent (s/2) (burnolUnitTailResponse base 4)) base.value=_ at word
 rw [word]
 have singled:(∑i∈Finset.range (j+1+1),(j+1).choose i •
   (iteratedDeriv i (fun s:ℂ=>(s-base.value)/2) base.value •
    iteratedDeriv (j+1-i) (fun s:ℂ=>burnolDirectRightResolvent (s/2) (burnolUnitTailResponse base 4)) base.value))=
   (j+1) • ((1/2:ℂ)•iteratedDeriv j (fun s:ℂ=>burnolDirectRightResolvent (s/2) (burnolUnitTailResponse base 4)) base.value):=by
  rw [Finset.sum_eq_single 1]
  · rw [step_jet,if_pos rfl,Nat.choose_one_right,show j+1-1=j by omega]
  · intro i _ different
    rw [step_jet,if_neg different,zero_smul,smul_zero]
  · intro outside
    have inside:(1:ℕ)∈Finset.range (j+1+1):=by simp
    exact (outside inside).elim
 rw [singled,OriginalRResolventParameterJet.parameter_jet]
 rw [←Nat.cast_smul_eq_nsmul ℂ,smul_smul,smul_smul]
 congr 1
 rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
 field_simp

private def fourClock (c:BurnolCompletedMellinCoordinate) : ℂ := fullMellinTranslationCharacter c.value (-Real.log 4)
private theorem four_dilation (c:BurnolCompletedMellinCoordinate) :
 burnolMultiplicativeDilation (-Real.log 4) (burnolUnitTailResponse c 1)=fourClock c•burnolUnitTailResponse c 4 := by
 have source:=burnolUnitTailResponse_radius_dilation c 1 (by norm_num) (by norm_num)
  (-Real.log 4) (by norm_num [Real.exp_log])
 simpa only [fourClock,one_mul,neg_neg,Real.exp_log (by norm_num:(0:ℝ)<4)] using source

/-- This is the original free resolvent difference, transported by its actual radius clock. -/
theorem actual_normalized_unit_source (base probe:BurnolCompletedMellinCoordinate) :
 (fourClock probe/fourClock base)•burnolUnitTailResponse probe 4=normalizedUnit base probe.value := by
 have source:=congrArg (burnolMultiplicativeDilation (-Real.log 4))
  (burnolUnitTailResponse_difference_resolvent probe base)
 rw [map_sub,map_smul,←burnolDirectRightResolvent_dilation,four_dilation,four_dilation,
  burnolDirectRightResolvent_smul] at source
 have nonzero:fourClock base≠0:=Complex.exp_ne_zero _
 apply smul_right_injective BurnolL2 nonzero
 dsimp only
 have coefficient:fourClock base*(fourClock probe/fourClock base)=fourClock probe:=by field_simp [nonzero]
 unfold normalizedUnit
 rw [smul_smul,coefficient,smul_add,smul_smul]
 change fourClock probe•burnolUnitTailResponse probe 4=
  fourClock base•burnolUnitTailResponse base 4+
   (fourClock base*((probe.value-base.value)/2))•burnolDirectRightResolvent (probe.value/2) (burnolUnitTailResponse base 4)
 linear_combination (norm:=module) source

end OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.UnitJet
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
