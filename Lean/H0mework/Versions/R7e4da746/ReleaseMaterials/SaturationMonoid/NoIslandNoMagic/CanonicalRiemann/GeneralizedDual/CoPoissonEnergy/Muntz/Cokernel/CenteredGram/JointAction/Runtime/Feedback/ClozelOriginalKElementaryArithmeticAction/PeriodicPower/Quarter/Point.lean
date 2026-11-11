import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Programme
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Point
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Point
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Source OriginalKElementaryArithmeticAction.PeriodicPower.Resolved
open OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Source OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
open OriginalKElementaryArithmeticAction.PeriodicPower.Programme OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Programme
open OriginalKElementaryArithmeticAction.PeriodicPower.Point
open scoped Topology InnerProductSpace
local instance periodPositive : Fact (0<(1:ℝ)) := ⟨by norm_num⟩
local notation "q" => (1/4:ℝ)

private theorem quarter_phase : _root_.fourier 1 (q:AddCircle (1:ℝ))=Complex.I := by
  rw [_root_.fourier_coe_apply]
  norm_num only [Int.cast_one,Complex.ofReal_one,mul_one,div_one]
  convert Complex.exp_pi_div_two_mul_I using 1
  congr 1
  push_cast
  ring

private theorem quarter_nontrivial : _root_.fourier 1 (q:AddCircle (1:ℝ))≠1 := by
  rw [quarter_phase]
  intro same
  have imaginary:=congrArg Complex.im same
  norm_num at imaginary

/-- The actual cofinal integer programme pays the noncentral quarter reading. -/
theorem actual_original_point_zero_quarter (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) : pointRaw c (q:AddCircle (1:ℝ))=0 := by
  have index:Tendsto (fun M:ℕ=>4*(M+1)) atTop atTop :=
    ((strictMono_mul_left_of_pos (by decide:(0:ℕ)<4)).comp
      (strictMono_nat_of_lt_succ (by intro n;omega))).tendsto_atTop
  exact tendsto_nhds_unique
    ((actual_programme_point_limit c (q:AddCircle (1:ℝ)) quarter_nontrivial).comp index)
    (actual_original_programme_zero_quarter c zero)

private theorem quarter_representative : representative (q:AddCircle (1:ℝ))=q := by
  have member:q∈Ioc (-(1/2):ℝ) (-(1/2)+(1:ℝ)) := by norm_num
  exact congrArg Subtype.val (AddCircle.equivIoc_coe_eq member)

private theorem quarter_away_boundary :
    (q:AddCircle (1:ℝ))≠((-(1/2):ℝ):AddCircle (1:ℝ)) := by
  intro same
  have inside:q∈Ico (-(1/2):ℝ) (-(1/2)+(1:ℝ)) := by norm_num
  have boundary:(-(1/2):ℝ)∈Ico (-(1/2):ℝ) (-(1/2)+(1:ℝ)) := by norm_num
  have impossible := (AddCircle.coe_eq_coe_iff_of_mem_Ico inside boundary).mp same
  norm_num at impossible

/-- Two source-generated AE representatives agree at their shared continuous quarter point. -/
theorem actual_quarter_continuous_representatives (c:BurnolCompletedMellinCoordinate) :
    pointRaw c (q:AddCircle (1:ℝ))=periodicRaw c q := by
  have same : pointRaw c=ᵐ[AddCircle.haarAddCircle]
      fun x=>periodicRaw c (representative x) :=
    (actual_point_raw_representative c).symm.trans (actual_periodic_raw c)
  have pointContinuous := actual_point_raw_continuousAt c (q:AddCircle (1:ℝ)) quarter_nontrivial
  have reprContinuous : ContinuousAt representative (q:AddCircle (1:ℝ)) :=
    continuous_subtype_val.continuousAt.comp
      (AddCircle.continuousAt_equivIoc (1:ℝ) (-(1/2):ℝ) quarter_away_boundary)
  have rawContinuous := actual_periodic_raw_continuousAt c q (by norm_num) (by norm_num) (by norm_num)
  have aliasContinuous : ContinuousAt (fun x:AddCircle (1:ℝ)=>periodicRaw c (representative x))
      (q:AddCircle (1:ℝ)) := by
    rw [←quarter_representative] at rawContinuous
    exact rawContinuous.comp reprContinuous
  have dense := Measure.dense_of_ae same
  have frequent := mem_closure_iff_frequently.mp (dense (q:AddCircle (1:ℝ)))
  have value := tendsto_nhds_unique_of_frequently_eq pointContinuous aliasContinuous frequent
  simpa only [quarter_representative] using value

theorem actual_original_periodic_zero_quarter (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) : periodicRaw c q=0 := by
  rw [←actual_quarter_continuous_representatives c]
  exact actual_original_point_zero_quarter c zero

/-- Full alias endpoint: the original constant and every alias remain in the equation. -/
theorem actual_original_complete_alias_quarter (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) :
    resolvedFourierRaw c q+aliasRaw c q=resolvedRaw c 0 := by
  exact sub_eq_zero.mp (actual_original_periodic_zero_quarter c zero)

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Point
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
