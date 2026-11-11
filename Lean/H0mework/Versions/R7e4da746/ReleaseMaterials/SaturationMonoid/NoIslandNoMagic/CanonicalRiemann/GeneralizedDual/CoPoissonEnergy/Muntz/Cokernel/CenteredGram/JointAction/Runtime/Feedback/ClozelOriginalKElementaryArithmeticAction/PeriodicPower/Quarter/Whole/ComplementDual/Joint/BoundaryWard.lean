import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CompactMass
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.CompactStock

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.BoundaryWard
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward OriginalKFourierKernelDependentRAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.NativePa
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CompactMass OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountingCut OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.AnnulusCross
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open scoped Topology InnerProductSpace
open private outgoing_power_compact from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
local notation "q"=>(1/4:ℝ)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "μq"=>volume.restrict (symmetricInterval q)
local notation "E"=>burnolQuarterZeroExtension
local notation "Rq"=>burnolQuarterRestriction
local notation "μ"=>burnolQuarterMeanCoefficient
local notation "A"=>sourceAnnulusCut
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate
local instance finiteQuarter:IsFiniteMeasure μq where
  measure_univ_lt_top:=lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

private theorem positive_compact_mass (state:Hq) (even:reflectL2 (E state)=E state):
    (∫x:ℝ in Ioc 0 q,state x)=μ state/4:=by
  have indicatorDomain:Integrable ((symmetricInterval q).indicator (state:ℝ→ℂ)):=
    IntegrableOn.integrable_indicator
      (show IntegrableOn (state:ℝ→ℂ) (symmetricInterval q) volume from (Lp.memLp state).integrable (by norm_num))
      (measurableSet_symmetricInterval q)
  have domain:Integrable (fun x:ℝ=>E state x):=
    indicatorDomain.congr (burnolQuarterZeroExtension_coe state).symm
  have reflected:=Lp.coeFn_compMeasurePreserving (E state) negMeasurePreserving
  change (reflectL2 (E state):ℝ→ℂ)=ᵐ[volume]fun x:ℝ=>E state (-x) at reflected
  rw [even] at reflected
  have negative:(∫x:ℝ in Iic 0,E state x)=∫x:ℝ in Ioi 0,E state x:=by
    calc
      _=∫x:ℝ in Iic 0,E state (-x):=integral_congr_ae (ae_restrict_of_ae reflected)
      _=_:=by simpa only [neg_zero] using integral_comp_neg_Iic 0 (fun x:ℝ=>E state x)
  have split:=setIntegral_union (Iic_disjoint_Ioi (a:=(0:ℝ)) le_rfl) measurableSet_Ioi
    domain.integrableOn domain.integrableOn
  rw [Iic_union_Ioi,setIntegral_univ,negative] at split
  have mean:μ state=2*(∫x:ℝ,E state x):=by
    rw [Constructor.mean_integral,integral_congr_ae (burnolQuarterZeroExtension_coe state),
      integral_indicator (measurableSet_symmetricInterval q)]
  have positive:(∫x:ℝ in Ioi 0,E state x)=∫x:ℝ in Ioc 0 q,state x:=by
    rw [integral_congr_ae (ae_restrict_of_ae (burnolQuarterZeroExtension_coe state)),
      integral_indicator (measurableSet_symmetricInterval q),
      Measure.restrict_restrict (measurableSet_symmetricInterval q)]
    have intersection:symmetricInterval q∩Ioi (0:ℝ)=Ioc 0 q:=by
      ext x
      change ((-q≤x∧x≤q)∧0<x)↔0<x∧x≤q
      constructor
      · exact fun h=>⟨h.2,h.1.2⟩
      · intro h
        exact ⟨⟨by linarith [h.1],h.2⟩,h.1⟩
    rw [intersection]
  rw [split,positive] at mean
  linear_combination -mean/4

private theorem native_compact_even (c:BurnolCompletedMellinCoordinate):
    reflectL2 (E (nativeCompact c))=E (nativeCompact c):=by
  have wave:=burnolReflectL2_eq_of_even_raw _ _ (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source.actual_quarter_raw c)
    (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source.actual_quarter_even c)
  change reflectL2 (quarterWave c)=quarterWave c at wave
  have source:E (nativeCompact c)=quarterWave c-actualWholeSingleSource c:=by
    rw [nativeCompact,map_sub]
    rfl
  rw [source,map_sub,wave,(actual_single_source_even c).1]

def compactAt (c:BurnolCompletedMellinCoordinate) (j:ℕ):Hq:=
  Rq (((sourceVolterraResolvent (barC c))^j) (E (nativeCompact c)))

theorem actual_compact_at (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    E (compactAt c j)=((sourceVolterraResolvent (barC c))^j) (E (nativeCompact c)):=
  outgoing_power_compact (barC c) (nativeCompact c) j

private theorem compact_at_even (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    reflectL2 (E (compactAt c j))=E (compactAt c j):=by
  rw [actual_compact_at]
  induction j with
  | zero => exact native_compact_even c
  | succ j previous =>
    rw [pow_succ',mul_apply_eq_comp,sourceVolterraResolvent_reflect,previous]

/-- The ordinary positive mass of the actual whole compact stock is generated at every original order. -/
theorem actual_compact_positive_mass (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    (∫x:ℝ in Ioc 0 q,compactAt c j x)=
      ((-2/star c.value)^j*μ (Rq (quarterWave c)))/4:=by
  rw [positive_compact_mass _ (compact_at_even c j),compactAt,actual_native_compact_mean]

/-- This is the complete continuous boundary debit of H−B, on the same actual integer clock. -/
theorem actual_native_compact_stock (c:BurnolCompletedMellinCoordinate) (j N:ℕ) (one:1≤N):
    (cutBoundaryStock N (((sourceVolterraResolvent (barC c))^j) (E (nativeCompact c))):ℝ→ℂ)=ᵐ[
        volume.restrict (Ioc q 4)]fun x:ℝ=>
      -(x:ℂ)⁻¹*(((-2/star c.value)^j*μ (Rq (quarterWave c)))/4):=by
  rw [←actual_compact_at]
  filter_upwards [actual_compact_stock_positive (compactAt c j) N one] with x source
  rw [source,actual_compact_positive_mass]

theorem actual_complete_boundary_stock (c:BurnolCompletedMellinCoordinate) (j N:ℕ):
    cutBoundaryStock N (tateSource c j)=
      cutBoundaryStock N (E (compactAt c j))+
        cutBoundaryStock N (((sourceVolterraResolvent (barC c))^j) (nativeReturn c)):=by
  have source:tateSource c j=E (compactAt c j)+
      ((sourceVolterraResolvent (barC c))^j) (nativeReturn c):=by
    rw [actual_compact_at,actual_tate_outgoing,actual_native_source,map_add]
  rw [source,←actual_cut_boundary_stock,←actual_cut_boundary_stock,←actual_cut_boundary_stock]
  simp only [CountingDual.dual_eq_adjoint,map_add]
  module

/-- Both boundary stocks and the two actual R cutcrosses are consumed on the unchanged source step. -/
theorem actual_source_boundary_ward (c:BurnolCompletedMellinCoordinate) (j N:ℕ):
    cutBoundaryStock N (tateSource c (j+1))-
      sourceVolterraResolvent (barC c) (cutBoundaryStock N (tateSource c j))=
      (A (sourceVolterraResolvent (barC c) (DualSource.source N (tateSource c j)))-
        sourceVolterraResolvent (barC c) (A (DualSource.source N (tateSource c j))))-
        DualSource.source N (annulusCross c j):=by
  have step:tateSource c (j+1)=sourceVolterraResolvent (barC c) (tateSource c j):=by
    rw [actual_tate_outgoing,actual_tate_outgoing,pow_succ',mul_apply_eq_comp]
  rw [step,←actual_cut_boundary_stock,←actual_cut_boundary_stock]
  exact actual_joint_cut_ward N c j

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.BoundaryWard
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
