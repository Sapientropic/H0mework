import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteResponseEulerSource.Parity
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

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

namespace WholePaid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalRieszSource.Euler (smoothEuler_mean even_extension_euler)
end WholePaid

def actualWholeUEuler (n : Nat) : BurnolL2:=
 burnolQuarterZeroExtension (actualUEuler n : BurnolQuarterIntervalL2)
def actualWholeVEuler (n : Nat) : BurnolL2:=
 burnolQuarterZeroExtension (actualVEuler n : BurnolQuarterIntervalL2)
def actualWholeU (n : Nat) : BurnolL2:=
 OriginalKResponseCofinalSourceAction.actualWholeRead (Prior.actualU n)
def actualWholeV (n : Nat) : BurnolL2:=
 OriginalKResponseCofinalSourceAction.actualWholeRead (Prior.actualV n)
def actualUCorrected (n : Nat) : BurnolL2:=
 actualWholeU n-actualURaw n q • OriginalKConstantSeedWholeRAction.ConstantSource.seed
def actualVCorrected (n : Nat) : BurnolL2:=
 actualWholeV n-actualVRaw n q • OriginalKConstantSeedWholeRAction.ConstantSource.seed

theorem actual_whole_U_euler (n : Nat) :
 OriginalRieszSource.GapEuler.euler (actualWholeU n : TemperedDistribution ℝ ℂ)=
 (actualWholeUEuler n : TemperedDistribution ℝ ℂ)-actualURaw n q • OriginalRieszSource.GapEuler.edge q :=by
 have generated:=WholePaid.even_extension_euler _ _ _ (actual_U_raw_source n)
  (actual_U_raw_continuous n) (actual_U_slope_continuous n) (actual_U_derivative n)
  (WholePaid.smoothEuler_mean _ _ _ (actual_U_raw_source n) (actual_U_raw_continuous n)
   (actual_U_slope_continuous n) (actual_U_derivative n)) (actual_U_endpoints n)
 exact generated

theorem actual_whole_V_euler (n : Nat) :
 OriginalRieszSource.GapEuler.euler (actualWholeV n : TemperedDistribution ℝ ℂ)=
 (actualWholeVEuler n : TemperedDistribution ℝ ℂ)-actualVRaw n q • OriginalRieszSource.GapEuler.edge q :=by
 have generated:=WholePaid.even_extension_euler _ _ _ (actual_V_raw_source n)
  (actual_V_raw_continuous n) (actual_V_slope_continuous n) (actual_V_derivative n)
  (WholePaid.smoothEuler_mean _ _ _ (actual_V_raw_source n) (actual_V_raw_continuous n)
   (actual_V_slope_continuous n) (actual_V_derivative n)) (actual_V_endpoints n)
 exact generated

/-- The actual finite endpoint is corrected by the same original seed, generating a whole strong-domain source field. -/
theorem actual_U_corrected_euler (n : Nat) :
 OriginalRieszSource.GapEuler.euler (actualUCorrected n : TemperedDistribution ℝ ℂ)=
 (actualWholeUEuler n+(actualURaw n q/2) • OriginalKConstantSeedWholeRAction.ConstantSource.seed : BurnolL2) :=by
 have native:=actual_whole_U_euler n
 have seed:=actualConstantEulerSource
 change OriginalRieszSource.GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 (actualUCorrected n))=Lp.toTemperedDistributionCLM ℂ volume 2 _
 unfold actualUCorrected
 simp only [map_sub,map_smul,map_add,Lp.toTemperedDistributionCLM_apply]
 rw [native,seed]
 module

theorem actual_V_corrected_euler (n : Nat) :
 OriginalRieszSource.GapEuler.euler (actualVCorrected n : TemperedDistribution ℝ ℂ)=
 (actualWholeVEuler n+(actualVRaw n q/2) • OriginalKConstantSeedWholeRAction.ConstantSource.seed : BurnolL2) :=by
 have native:=actual_whole_V_euler n
 have seed:=actualConstantEulerSource
 change OriginalRieszSource.GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 (actualVCorrected n))=Lp.toTemperedDistributionCLM ℂ volume 2 _
 unfold actualVCorrected
 simp only [map_sub,map_smul,map_add,Lp.toTemperedDistributionCLM_apply]
 rw [native,seed]
 module

theorem actual_U_corrected_strong (n : Nat) :
 HasDerivAt (fun shift:ℝ=>burnolMultiplicativeDilation shift (actualUCorrected n))
 (actualWholeUEuler n+(actualURaw n q/2) • OriginalKConstantSeedWholeRAction.ConstantSource.seed) 0 :=
 OriginalRieszFinitePairing.CoPoisson.Ward.DilationWard.strong_derivative _ _ (actual_U_corrected_euler n)
theorem actual_V_corrected_strong (n : Nat) :
 HasDerivAt (fun shift:ℝ=>burnolMultiplicativeDilation shift (actualVCorrected n))
 (actualWholeVEuler n+(actualVRaw n q/2) • OriginalKConstantSeedWholeRAction.ConstantSource.seed) 0 :=
 OriginalRieszFinitePairing.CoPoisson.Ward.DilationWard.strong_derivative _ _ (actual_V_corrected_euler n)

def actualUVelocity (n : Nat) : BurnolL2:=
 actualWholeUEuler n+(actualURaw n q/2) • OriginalKConstantSeedWholeRAction.ConstantSource.seed
def actualVVelocity (n : Nat) : BurnolL2:=
 actualWholeVEuler n+(actualVRaw n q/2) • OriginalKConstantSeedWholeRAction.ConstantSource.seed

/-- Existing resolvent uniqueness consumes the actual finite whole source action, with its complete endpoint correction. -/
theorem actual_U_R_source_inverse (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) :
 burnolDirectRightResolvent (coordinate.value/2)
  (actualUVelocity n+(coordinate.value-1/2) • actualUCorrected n)=
 (-2:ℂ) • actualUCorrected n :=by
 have strong:=actual_U_corrected_strong n
 have generated:HasDerivAt (fun shift:ℝ=>burnolMultiplicativeDilation shift ((-2:ℂ) • actualUCorrected n))
  ((-2:ℂ) • actualUVelocity n) 0 :=by
  have scaled:=strong.const_smul (-2:ℂ)
  convert! scaled using 1
  · funext shift;exact (burnolMultiplicativeDilation shift).map_smul (-2:ℂ) _
 have original:HasDerivAt (fun time:ℝ=>burnolMultiplicativeDilation (-time/2) ((-2:ℂ) • actualUCorrected n))
  ((coordinate.value/2-1/4) • ((-2:ℂ) • actualUCorrected n)+
   (actualUVelocity n+(coordinate.value-1/2) • actualUCorrected n)) 0 :=by
  have scalar:HasDerivAt (fun time:ℝ=>-time/2) (-1/2:ℝ) 0:=by
   simpa only [Pi.neg_apply,neg_div,id_eq] using ((hasDerivAt_id (0:ℝ)).neg.div_const 2)
  have source:=generated.scomp_of_eq (0:ℝ) scalar (by norm_num)
  convert! source using 1
  rw [←algebraMap_smul ℂ (-1/2:ℝ)]
  push_cast
  module
 have right:1/4<(coordinate.value/2).re:=by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 exact (burnolDirectRightResolvent_of_strongEquation (coordinate.value/2) right
  (actualUVelocity n+(coordinate.value-1/2) • actualUCorrected n) ((-2:ℂ) • actualUCorrected n) original).symm

theorem actual_V_R_source_inverse (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) :
 burnolDirectRightResolvent (coordinate.value/2)
  (actualVVelocity n+(coordinate.value-1/2) • actualVCorrected n)=
 (-2:ℂ) • actualVCorrected n :=by
 have strong:=actual_V_corrected_strong n
 have generated:HasDerivAt (fun shift:ℝ=>burnolMultiplicativeDilation shift ((-2:ℂ) • actualVCorrected n))
  ((-2:ℂ) • actualVVelocity n) 0 :=by
  have scaled:=strong.const_smul (-2:ℂ)
  convert! scaled using 1
  · funext shift;exact (burnolMultiplicativeDilation shift).map_smul (-2:ℂ) _
 have original:HasDerivAt (fun time:ℝ=>burnolMultiplicativeDilation (-time/2) ((-2:ℂ) • actualVCorrected n))
  ((coordinate.value/2-1/4) • ((-2:ℂ) • actualVCorrected n)+
   (actualVVelocity n+(coordinate.value-1/2) • actualVCorrected n)) 0 :=by
  have scalar:HasDerivAt (fun time:ℝ=>-time/2) (-1/2:ℝ) 0:=by
   simpa only [Pi.neg_apply,neg_div,id_eq] using ((hasDerivAt_id (0:ℝ)).neg.div_const 2)
  have source:=generated.scomp_of_eq (0:ℝ) scalar (by norm_num)
  convert! source using 1
  rw [←algebraMap_smul ℂ (-1/2:ℝ)]
  push_cast
  module
 have right:1/4<(coordinate.value/2).re:=by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 exact (burnolDirectRightResolvent_of_strongEquation (coordinate.value/2) right
  (actualVVelocity n+(coordinate.value-1/2) • actualVCorrected n) ((-2:ℂ) • actualVCorrected n) original).symm

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteResponseEulerSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
