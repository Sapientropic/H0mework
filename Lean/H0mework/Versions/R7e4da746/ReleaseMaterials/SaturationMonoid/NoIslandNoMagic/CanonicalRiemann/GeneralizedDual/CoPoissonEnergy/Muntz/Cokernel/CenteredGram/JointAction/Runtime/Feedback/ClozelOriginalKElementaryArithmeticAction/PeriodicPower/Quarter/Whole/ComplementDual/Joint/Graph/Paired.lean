import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Compact
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.StrongIdentification
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.KPaired

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Paired
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Compact OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.JointSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open scoped Topology InnerProductSpace
open private forward_fourier from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeGramSource
open private forward_reflect from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingJointEnergy
local notation "T"=>burnolTateReciprocalL2
local notation "F"=>fourierL2
local notation "E"=>burnolQuarterZeroExtension
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "S"=>burnolMeanZeroTruncatedFourier
local notation "K"=>burnolCompletedMellinRieszVector
local notation "leading"=>ForcingPrimitive.leadingCoefficient

def forwardValue (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):BurnolL2:=
  nativeProgramme c+leading c • F (poissonPair (logProgramme c))-
    F (-PositionCounting.value c zero-T (CountingDual.value c))

def reverseValue (c:BurnolCompletedMellinCoordinate):BurnolL2:=
  poissonPair (nativeProgramme c)+leading c • F (logProgramme c)-F (KCountingGram.value c)

/-- The full original joint source generates its forward graph before any cut or Pa projection. -/
theorem actual_joint_forward_graph (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    Tendsto (fun N:ℕ=>FiniteForcing.source N (jointSource c)) atTop (𝓝 (forwardValue c zero)):=by
  have logs:=(fourierL2.continuous.tendsto _).comp (actual_log_return_reverse c)
  have kernel:=(fourierL2.continuous.tendsto _).comp (KCounting.original_tendsto c zero)
  have total:=((actual_native_forward c).add (logs.const_smul (leading c))).sub kernel
  have finite (N:ℕ):FiniteForcing.source N (jointSource c)=
      FiniteForcing.source N (E (nativeCompact c))+
        leading c • F (DualSource.source N (E (S (OriginalKFiniteOrderRelease.UnitPowerJordanSource.logBFirst c 0):Hq)))-
        F (DualSource.source N (K c:BurnolL2)):=by
    change CountingDual.sourceCLM N (jointSource c)=_
    rw [actual_native_source,nativeReturn,map_add,map_sub,map_smul]
    simp only [CountingDual.sourceCLM_apply,forward_fourier]
    module
  exact total.congr' (Eventually.of_forall (fun N=>(finite N).symm))

/-- The independently generated reverse retains the complete original K and both compact source programmes. -/
theorem actual_joint_reverse_graph (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    Tendsto (fun N:ℕ=>DualSource.source N (jointSource c)) atTop (𝓝 (reverseValue c)):=by
  have logs:=(fourierL2.continuous.tendsto _).comp (actual_logB_return_forward c)
  have kernel:=(fourierL2.continuous.tendsto _).comp (KCountingGram.forward_tendsto c zero)
  have total:=((actual_native_reverse c).add (logs.const_smul (leading c))).sub kernel
  have finite (N:ℕ):DualSource.source N (jointSource c)=
      DualSource.source N (E (nativeCompact c))+
        leading c • F (FiniteForcing.source N (E (S (OriginalKFiniteOrderRelease.UnitPowerJordanSource.logBFirst c 0):Hq)))-
        F (FiniteForcing.source N (K c:BurnolL2)):=by
    rw [actual_native_source,nativeReturn]
    simp only [CountingDual.dual_eq_adjoint,map_add,map_sub,map_smul]
    simp only [←CountingDual.dual_eq_adjoint,actual_reverse_fourier]
    module
  exact total.congr' (Eventually.of_forall (fun N=>(finite N).symm))

private theorem counted_K_even (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    reflectL2 (KCountingGram.value c)=KCountingGram.value c:=by
  have original:=KCountingGram.forward_tendsto c zero
  have even:reflectL2 (K c:BurnolL2)=(K c:BurnolL2):=
    mem_evenL2ClosedFace_iff.mp (K c).property.2
  have reflected:=(reflectL2.continuous.tendsto _).comp original
  have finite (N:ℕ):reflectL2 (FiniteForcing.source N (K c:BurnolL2))=FiniteForcing.source N (K c:BurnolL2):=by
    rw [forward_reflect,even]
  have same:=reflected.congr' (Eventually.of_forall finite)
  exact tendsto_nhds_unique same original

private theorem poisson_fourier_poisson (value:BurnolL2) (even:reflectL2 value=value):
    poissonPair (F (poissonPair value))=F value:=by
  change T (F (F (T (F value))))=F value
  rw [fourierL2_fourierL2,burnolTateReciprocal_reflect,burnolTateReciprocalL2_involutive,
    ←fourierL2_reflectL2_commute,even]

/-- The two full values are identified by their source programmes and the original K paired graph. -/
theorem actual_joint_paired_value (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    reverseValue c=poissonPair (forwardValue c zero):=by
  have logEven:reflectL2 (logProgramme c)=logProgramme c:=
    burnolRemainderRealization_even _ _ (actual_log_return_realizes c)
  rw [forwardValue,map_sub,map_add,map_smul,actual_original_K_paired_value,
    poisson_fourier_poisson _ logEven,poisson_fourier_poisson _ (counted_K_even c zero)]
  rfl

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Paired
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
