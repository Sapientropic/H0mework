import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.NativePa
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
open scoped Topology
open private outgoing_power_compact from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
local notation "q"=>(1/4:ℝ)
local notation "E"=>burnolQuarterZeroExtension
local notation "A"=>sourceAnnulusCut
local notation "C"=>FiniteMobiusResolventFlux.cutoff q
local notation "T"=>burnolTateReciprocalL2
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate
local instance physicalComplete:CompleteSpace BurnolPaAmbientCarrier:=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem compact_annulus_zero (value:BurnolL2) (supported:C value=value):A value=0:=by
  have compact:=FiniteMobiusResolventFlux.cutoff_read q value
  rw [supported] at compact
  apply Lp.ext
  filter_upwards [sourceAnnulusCut_coeFn value,compact,Lp.coeFn_zero ℂ 2 volume] with x cut source zero
  rw [cut,zero]
  by_cases band:q < |x| ∧ |x|≤4
  · have outside:x∉symmetricInterval q:=fun inside=>not_le.mpr band.1 (abs_le.mpr inside)
    rw [if_pos band,source,indicator_of_notMem outside]
    rfl
  · rw [if_neg band]
    rfl

/-- The whole compact H−B stock is eliminated by the actual annulus after every outgoing source action. -/
theorem actual_native_annulus (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    A (tateSource c j)=A (((sourceVolterraResolvent (barC c))^j) (nativeReturn c)):=by
  rw [actual_tate_outgoing,actual_native_source,map_add,map_add,
    compact_annulus_zero _ (outgoing_power_compact (barC c) (nativeCompact c) j),zero_add]

/-- The actual infinite Pa state is generated entirely by the original K/log return source. -/
theorem actual_native_pa (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    actualPa c j=sourceVolterraPhysical (barC c)
      (((sourceVolterraResolvent (barC c))^j) (nativeReturn c)):=by
  change sourceVolterraPhysical (barC c) (tateSource c j)=_
  rw [←sourceVolterraPhysical_annulus (barC c) (tateSource c j),actual_native_annulus,
    sourceVolterraPhysical_annulus]

theorem actual_native_pa_source (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    T (burnolMobiusSourceL2 (actualPa c j))=
      sourceVolterraWindow (barC c)
        (A (((sourceVolterraResolvent (barC c))^j) (nativeReturn c))):=by
  rw [actual_pa_source,actual_native_annulus]

/-- All compact origin stock remains in this full source equality; no separate L2 co-Poisson image is asserted. -/
theorem actual_complete_native_residual (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    residualSource c j=
      ((sourceVolterraResolvent (barC c))^(j+1)) (E (nativeCompact c))+
        (((sourceVolterraResolvent (barC c))^(j+1)) (nativeReturn c)-
          sourceVolterraWindow (barC c)
            (A (((sourceVolterraResolvent (barC c))^j) (nativeReturn c)))):=by
  rw [residualSource,actual_native_annulus,actual_tate_outgoing,actual_native_source]
  simp only [map_add,pow_succ',mul_apply_eq_comp]
  module

/-- The same source K/log stock now supplies the entire actual annulus coefficient of the independent consumer. -/
theorem actual_native_residual_profile (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    ∀ᵐx:ℝ∂volume,∀_positive:0<x,
      residualSource c j x=if q<x∧x≤4 then
        (-2:ℂ)*(x:ℂ)^((barC c).value-1)*
          burnolRadiusMellinTailEvaluator 4 (by norm_num) (barC c).value (barC c).rightHalf
            (((sourceVolterraResolvent (barC c))^j) (nativeReturn c))
        else sourceVolterraResolvent (barC c) (tateSource c j) x:=by
  filter_upwards [actual_residual_source_profile c j] with x actual positive
  simpa only [actual_native_upper_tail] using actual positive

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.NativePa
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
