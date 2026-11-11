import H0mework.Versions.R7e4da746.Arithmetic.RiemannFirstSource.GeneratorResolventOperator
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! The original R action generates its local analytic parameter jet by the paid resolvent identity. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex Filter
open scoped Topology
namespace OriginalRResolventParameterJet
local notation "End" => BurnolL2 →L[ℂ] BurnolL2
private theorem parameter_right (c : BurnolCompletedMellinCoordinate) :
    (1/4:ℝ)<(c.value/2).re := by
  rw [Complex.div_re]
  norm_num
  linarith [c.rightHalf]
private theorem actual_neumann (c : BurnolCompletedMellinCoordinate)
    (s:ℂ) (sr:(1/4:ℝ)<(s/2).re) (v:BurnolL2)
    (unit:IsUnit ((1:End)-((s-c.value)/2) • burnolDirectRightResolventCLM c)) :
    burnolDirectRightResolvent (s/2) v=
      (Ring.inverse ((1:End)-((s-c.value)/2) • burnolDirectRightResolventCLM c))
        ((burnolDirectRightResolventCLM c) v) := by
  let D:=burnolDirectRightResolventCLM c
  let value:=burnolDirectRightResolvent (s/2) v
  have generated:=burnolDirectRightResolvent_identity (c.value/2) (s/2) (parameter_right c) sr v
  change D v-value=(c.value/2-s/2) • D value at generated
  have scalar:c.value/2-s/2=-((s-c.value)/2):=by ring
  rw [scalar,neg_smul] at generated
  have equation:((1:End)-((s-c.value)/2) • D) value=D v := by
    change value-((s-c.value)/2) • D value=D v
    calc
      _=value+(D v-value) := by rw [generated]; module
      _=D v := by module
  have recovered:=congrArg
    (fun field:BurnolL2=>(Ring.inverse ((1:End)-((s-c.value)/2) • D)) field) equation
  have cancellation:=congrArg (fun operator:End=>operator value)
    (Ring.inverse_mul_cancel ((1:End)-((s-c.value)/2) • D) unit)
  change (Ring.inverse ((1:End)-((s-c.value)/2) • D))
    (((1:End)-((s-c.value)/2) • D) value)=value at cancellation
  exact cancellation.symm.trans recovered
private def parameterSeries (c:BurnolCompletedMellinCoordinate) (v:BurnolL2) :
    FormalMultilinearSeries ℂ ℂ BurnolL2 :=
  (ContinuousLinearMap.apply ℂ BurnolL2 ((burnolDirectRightResolventCLM c) v)).compFormalMultilinearSeries
    (fun j=>ContinuousMultilinearMap.mkPiRing ℂ (Fin j)
      (((1/2:ℂ) • burnolDirectRightResolventCLM c)^j))

private theorem parameter_series (c:BurnolCompletedMellinCoordinate) (v:BurnolL2) :
    HasFPowerSeriesAt (fun s:ℂ=>burnolDirectRightResolvent (s/2) v) (parameterSeries c v) c.value := by
  let D:=burnolDirectRightResolventCLM c
  let A:End:=(1/2:ℂ) • D
  have series:=spectrum.hasFPowerSeriesOnBall_inverse_one_sub_smul ℂ A
  have shifted:=series.comp_sub c.value
  have applied:=(ContinuousLinearMap.apply ℂ BurnolL2 (D v)).comp_hasFPowerSeriesOnBall shifted
  have computed:HasFPowerSeriesAt (fun s:ℂ=>Ring.inverse ((1:End)-(s-c.value) • A) (D v))
      (parameterSeries c v) c.value := by
    convert! applied.hasFPowerSeriesAt using 1
    simp only [zero_add]
  have rightNear:∀ᶠ s:ℂ in 𝓝 c.value,(1/4:ℝ)<(s/2).re :=
    (show ContinuousAt (fun s:ℂ=>(s/2).re) c.value from by fun_prop).eventually
      (eventually_gt_nhds (parameter_right c))
  have normNear:∀ᶠ s:ℂ in 𝓝 c.value,‖(s-c.value) • A‖<1 :=
    (show ContinuousAt (fun s:ℂ=>‖(s-c.value) • A‖) c.value from by fun_prop).eventually
      (eventually_lt_nhds (by simp))
  apply computed.congr
  filter_upwards [rightNear,normNear] with s right small
  have unit:=isUnit_one_sub_of_norm_lt_one small
  have scalar:((s-c.value)/2) • D=(s-c.value) • A := by
    dsimp only [A]
    rw [smul_smul]
    congr 1
    ring
  rw [←scalar] at unit ⊢
  exact (actual_neumann c s right v unit).symm

theorem parameter_analytic (c:BurnolCompletedMellinCoordinate) (v:BurnolL2) :
    AnalyticAt ℂ (fun s:ℂ=>burnolDirectRightResolvent (s/2) v) c.value :=
  (parameter_series c v).analyticAt

theorem parameter_jet (c:BurnolCompletedMellinCoordinate) (v:BurnolL2) (j:Nat) :
    iteratedDeriv j (fun s:ℂ=>burnolDirectRightResolvent (s/2) v) c.value=
      ((j.factorial:ℂ)/(2:ℂ)^j) • ((burnolDirectRightResolventCLM c)^(j+1)) v := by
  obtain ⟨radius,series⟩:=parameter_series c v
  have actual:=series.factorial_smul (1:ℂ) j
  rw [←iteratedDeriv_eq_iteratedFDeriv] at actual
  have coefficient:(parameterSeries c v j) (fun _=>1)=
      (1/2:ℂ)^j • ((burnolDirectRightResolventCLM c)^(j+1)) v := by
    simp only [parameterSeries,ContinuousLinearMap.compFormalMultilinearSeries_apply',
      ContinuousMultilinearMap.mkPiRing_apply,Finset.prod_const_one,one_smul,
      smul_pow,ContinuousLinearMap.apply_apply,_root_.smul_apply]
    rw [pow_succ]
    rfl
  rw [coefficient,←Nat.cast_smul_eq_nsmul ℂ,smul_smul] at actual
  simpa only [one_div,inv_pow,div_eq_mul_inv,one_mul] using actual.symm
end OriginalRResolventParameterJet
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
