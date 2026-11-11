import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fixed
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Cotest
open OriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer OriginalKElementaryArithmeticAction.FreeParameter.Riesz
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountedPa
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.OriginalK OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Compact
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.WholeResidual
open scoped Topology InnerProductSpace
local notation "T"=>burnolTateReciprocalL2
local notation "F"=>fourierL2
local notation "D"=>burnolMultiplicativeDilation
local notation "A"=>sourceAnnulusCut
local notation "C"=>OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor.fullFloorValue
local notation "K"=>burnolCompletedMellinRieszVector
local notation "leading"=>ForcingPrimitive.leadingCoefficient
local notation "h₀"=>Real.log stageZeroSonineQ

private theorem original_counted_covector (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    countedKernel c zero=F (KCountingGram.value c):=by
  rw [countedKernel,OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.actual_original_K_paired_value c zero]
  change T (T (F (KCountingGram.value c)))=F (KCountingGram.value c)
  exact burnolTateReciprocalL2_involutive _

/-- The genuine moved Pa price now consumes the same whole C, actual counted log field and original B leg. -/
theorem actual_moving_complete_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (j:ℕ) (h:ℝ):
    -inner ℂ (T (C c zero)) (D h (A (tateSource c (j+1))))+
      star (leading c)*inner ℂ (F (logProgramme c)) (D h (A (tateSource c (j+1))))-
      inner ℂ (CountingDual.value c) (D h (A (tateSource c (j+1))))=
        inner ℂ (K c:BurnolL2) (D (-h) (enrichedPa c j:BurnolL2)):=by
  have source:=actual_moving_pa_price c zero j h
  rw [original_counted_covector c zero,actual_original_K_counted_field c zero] at source
  simpa only [inner_sub_left,inner_add_left,inner_neg_left,inner_smul_left,starRingEnd_apply] using source

def nativeFixedNet (c:BurnolCompletedMellinCoordinate):ℂ:=
  (pairedMellinTranslationCharacter c.value h₀-pairedMellinTranslationCharacter (star c.value) h₀)*kernelSelfSource c+
    (1/2:ℂ)*(-inner ℂ (movedTest c h₀) (freeUnit (star c.value) ConstantDual.value)+
      leading c*inner ℂ (twoClockCorrection c h₀) (centeredLogColumn c 0)-
        inner ℂ (jointCotest c h₀) (nativeSmooth c))

/-- This is the original fixed occurrence and exact original consumer, with its actual native B source and whole Unit. -/
theorem actual_original_fixed_native_consumer (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    BurnolPaBoundaryCancellationAt c zero↔nativeFixedNet c=0:=by
  have nonnegative:0≤h₀:=Real.log_nonneg (by
    change 1≤Real.sqrt 3
    exact Real.one_le_sqrt.mpr (by norm_num))
  rw [actual_original_fixed_cotest c zero,actual_two_clock_native_price c h₀ nonnegative]
  simp only [nativeFixedNet,add_sub_assoc]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fixed
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
