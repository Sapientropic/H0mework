import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKJordanExteriorSourceAction.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSingleReturnEulerRAction
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

namespace Native
export OriginalKFourierKernelDependentRAction (actualWholeSingleReturn actualSingleReturn actual_single_source_even actual_single_source_equation)
export OriginalKConstantSeedWholeRAction.ConstantSource (seed)
end Native

def actualReturnEndpoint (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
 burnolRieszReturnRaw coordinate q

def actualCorrectedReturn (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
 Native.actualWholeSingleReturn coordinate-actualReturnEndpoint coordinate • Native.seed

def actualReturnVelocity (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
 -(star coordinate.value-1/2) • Native.actualWholeSingleReturn coordinate-
 OriginalRieszSource.Kernel.A coordinate • OriginalRieszSource.Response.wholeV+
 OriginalRieszSource.Kernel.beta coordinate • OriginalRieszSource.Response.wholeU+
 ((1/2:ℂ)*actualReturnEndpoint coordinate) • Native.seed

/-- The actual original return and the same seed contact generate one entire L2 Euler field. -/
theorem actual_return_corrected_euler (coordinate : BurnolCompletedMellinCoordinate) :
 OriginalRieszSource.GapEuler.euler (actualCorrectedReturn coordinate : TemperedDistribution ℝ ℂ)=
 (actualReturnVelocity coordinate : TemperedDistribution ℝ ℂ) :=by
 let extension:BurnolQuarterMeanZeroCarrier→L[ℂ]TemperedDistribution ℝ ℂ:=
  (Lp.toTemperedDistributionCLM ℂ volume 2).comp
   (burnolQuarterZeroExtension.comp (Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule))
 have velocity:=congrArg extension (OriginalRieszSource.Euler.returnEuler_eq coordinate)
 simp only [map_add,map_sub,map_smul] at velocity
 have source:=OriginalRieszSource.Euler.return_euler coordinate
 change OriginalRieszSource.GapEuler.euler (Native.actualWholeSingleReturn coordinate : TemperedDistribution ℝ ℂ)=
  extension (OriginalRieszSource.Constructor.returnEuler coordinate)-
  actualReturnEndpoint coordinate • OriginalRieszSource.GapEuler.edge q at source
 rw [velocity] at source
 change OriginalRieszSource.GapEuler.euler (Native.actualWholeSingleReturn coordinate : TemperedDistribution ℝ ℂ)=
  -(star coordinate.value-1/2) • (Native.actualWholeSingleReturn coordinate : TemperedDistribution ℝ ℂ)-
  OriginalRieszSource.Kernel.A coordinate • (OriginalRieszSource.Response.wholeV : TemperedDistribution ℝ ℂ)+
  OriginalRieszSource.Kernel.beta coordinate • (OriginalRieszSource.Response.wholeU : TemperedDistribution ℝ ℂ)-
  actualReturnEndpoint coordinate • OriginalRieszSource.GapEuler.edge q at source
 have constant:=actualConstantEulerSource
 change OriginalRieszSource.GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 (actualCorrectedReturn coordinate))=
  Lp.toTemperedDistributionCLM ℂ volume 2 (actualReturnVelocity coordinate)
 unfold actualCorrectedReturn actualReturnVelocity
 simp only [map_sub,map_add,map_smul,Lp.toTemperedDistributionCLM_apply]
 rw [source,constant]
 module

/-- The existing weak-to-strong source engine consumes the actual return contact cancellation. -/
theorem actual_return_corrected_strong (coordinate : BurnolCompletedMellinCoordinate) :
 HasDerivAt (fun shift:ℝ=>burnolMultiplicativeDilation shift (actualCorrectedReturn coordinate))
  (actualReturnVelocity coordinate) 0 :=
 OriginalRieszFinitePairing.CoPoisson.Ward.DilationWard.strong_derivative _ _
  (actual_return_corrected_euler coordinate)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSingleReturnEulerRAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
