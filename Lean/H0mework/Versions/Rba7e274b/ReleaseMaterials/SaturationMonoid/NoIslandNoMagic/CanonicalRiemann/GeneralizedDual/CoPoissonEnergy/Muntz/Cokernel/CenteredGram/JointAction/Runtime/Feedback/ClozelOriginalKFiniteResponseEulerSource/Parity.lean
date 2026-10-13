import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteResponseEulerSource.Action
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteResponseEulerSource
open Complex MeasureTheory Set Filter SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean Rplus RplusIntegrand Rplus_integrable)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (actual_mean_source_integral actual_mean_dilation_source source_weight_mean_phase)
end Paid
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

/-- Finite U inherits source parity through the actual same Fourier action. -/
theorem actual_U_even (n : Nat) :
 reflectRestricted q (Prior.actualU n:BurnolQuarterIntervalL2)=Prior.actualU n :=by
 induction n with
 | zero=>simp [OriginalKResponseCofinalSourceAction.actualU]
 | succ n previous=>
  have fixed:sourceMeanZeroReflection (Prior.actualU n)=Prior.actualU n:=Subtype.ext previous
  have one:=sourceMeanZeroFourier_reflect (Prior.actualU n)
  rw [fixed] at one
  have Vfixed:sourceMeanZeroReflection (Prior.actualV n)=Prior.actualV n:=one.symm
  have two:=sourceMeanZeroFourier_reflect (Prior.actualV n)
  rw [Vfixed] at two
  rw [Prior.actual_source_step]
  change reflectRestricted q ((OriginalRieszSource.Response.eta:BurnolQuarterIntervalL2)+
   (burnolMeanZeroTruncatedFourier (Prior.actualV n):BurnolQuarterIntervalL2))=_
  rw [map_add,OriginalRieszSource.Response.eta_reflection]
  exact congrArg (fun state:BurnolQuarterMeanZeroCarrier=>
   (OriginalRieszSource.Response.eta:BurnolQuarterIntervalL2)+(state:BurnolQuarterIntervalL2)) two.symm

theorem actual_V_even (n : Nat) :
 reflectRestricted q (Prior.actualV n:BurnolQuarterIntervalL2)=Prior.actualV n :=by
 have fixed:sourceMeanZeroReflection (Prior.actualU n)=Prior.actualU n:=Subtype.ext (actual_U_even n)
 have generated:=sourceMeanZeroFourier_reflect (Prior.actualU n)
 rw [fixed] at generated
 exact congrArg (fun state:BurnolQuarterMeanZeroCarrier=>(state:BurnolQuarterIntervalL2)) generated.symm

private theorem actual_raw_endpoints (state : BurnolQuarterMeanZeroCarrier) (raw : ℝ→ℂ)
 (continuous : Continuous raw) (read : (state:BurnolQuarterIntervalL2)=ᵐ[μq] raw)
 (even : reflectRestricted q (state:BurnolQuarterIntervalL2)=state) : raw (-q)=raw q :=by
 let reflectionMap:=negMeasurePreserving_restrict q
 have parity : (fun x:ℝ=>raw (-x))=ᵐ[μq] raw :=by
  filter_upwards [Lp.coeFn_compMeasurePreserving (state:BurnolQuarterIntervalL2) reflectionMap,
   reflectionMap.quasiMeasurePreserving.ae read,read] with x reflected negative direct
  change reflectRestricted q (state:BurnolQuarterIntervalL2) x=(state:BurnolQuarterIntervalL2) (-x) at reflected
  rw [even] at reflected
  exact negative.symm.trans (reflected.symm.trans direct)
 exact Measure.eqOn_Icc_of_ae_eq volume (by norm_num : -q≠q) parity
  (continuous.comp continuous_neg).continuousOn continuous.continuousOn (by norm_num)

theorem actual_U_endpoints (n : Nat) : actualURaw n (-q)=actualURaw n q :=
 actual_raw_endpoints _ _ (actual_U_raw_continuous n) (actual_U_raw_source n) (actual_U_even n)
theorem actual_V_endpoints (n : Nat) : actualVRaw n (-q)=actualVRaw n q :=
 actual_raw_endpoints _ _ (actual_V_raw_continuous n) (actual_V_raw_source n) (actual_V_even n)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteResponseEulerSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
