import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountedPa
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.OriginalK
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Cotest

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerJordanSource OriginalKFiniteOrderRelease.UnitPowerJordanAction
open OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Cotest
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.OriginalB
open scoped Topology InnerProductSpace
local notation "M"=>BurnolQuarterMeanZeroCarrier
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "S"=>burnolMeanZeroTruncatedFourier
local notation "L"=>burnolMeanZeroOneMinusSquare
local notation "q"=>(1/4:ℝ)
local notation "leading"=>ForcingPrimitive.leadingCoefficient
local notation "η"=>burnolAmbientMeanZeroFourier

def nativeSmooth (c:BurnolCompletedMellinCoordinate):M:=
  leading c • logBFirst c 0-burnolRieszSingleFourierSource c

/-- This actual native source is the already generated smoothed original L1 dual. -/
theorem actual_native_smooth (c:BurnolCompletedMellinCoordinate):
    nativeSmooth c=smooth (dualRaw c.value c.belowOne) (actual_dual_integrable c.value c.belowOne):=
  (actual_original_dual_fourier_source c).symm

private theorem native_even (c:BurnolCompletedMellinCoordinate):
    reflectRestricted q (nativeSmooth c:Hq)=nativeSmooth c:=by
  have logEven:=congrArg (fun v:M=>(v:Hq)) (log_B_even c 0)
  have bEven:=burnolRieszSingleFourierSource_reflection_fixed c
  change reflectRestricted q (logBFirst c 0:Hq)=logBFirst c 0 at logEven
  change reflectRestricted q ((leading c • logBFirst c 0-burnolRieszSingleFourierSource c:M):Hq)=_
  simp only [nativeSmooth,Submodule.coe_sub,Submodule.coe_smul,map_sub,map_smul,logEven,bEven]

private theorem native_return_even (c:BurnolCompletedMellinCoordinate):
    reflectRestricted q (S (nativeSmooth c):Hq)=S (nativeSmooth c):=by
  have parity:sourceMeanZeroReflection (nativeSmooth c)=nativeSmooth c:=Subtype.ext (native_even c)
  have returned:=sourceMeanZeroFourier_reflect (nativeSmooth c)
  rw [parity] at returned
  exact congrArg (fun v:M=>(v:Hq)) returned.symm

private theorem native_block_source (c:BurnolCompletedMellinCoordinate):
    L (nativeSmooth c)=leading c • centeredLogColumn c 0-
      η (burnolAmbientCompletedMellinKernelFormula c):=by
  have logSource: L (logBFirst c 0)=centeredLogColumn c 0:=by
    have paid:=(log_B_source c 0).1
    change logBFirst c 0-S (S (logBFirst c 0))=centeredLogColumn c 0
    simpa only [logBSecond,map_neg,←sub_eq_add_neg] using paid
  rw [nativeSmooth,map_sub,map_smul,logSource,burnolRieszSingleFourierSource_equation]

private theorem native_inverse_price (c:BurnolCompletedMellinCoordinate) (test:M):
    inner ℂ (L test) (nativeSmooth c)=inner ℂ test (L (nativeSmooth c)):=by
  change inner ℂ (test-S (S test)) (nativeSmooth c)=inner ℂ test (nativeSmooth c-S (S (nativeSmooth c)))
  rw [inner_sub_left,inner_sub_right,
    meanZero_fourier_pairing_of_reflection (S test) (nativeSmooth c) (native_even c),
    meanZero_fourier_pairing_of_reflection test (S (nativeSmooth c)) (native_return_even c)]

/-- The two genuine moved-K clocks consume the actual native B source price, without identifying distinct inverse inputs. -/
theorem actual_two_clock_native_price (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nonnegative:0≤h):
    inner ℂ (twoClockCorrection c h) (η (burnolAmbientCompletedMellinKernelFormula c))=
      leading c*inner ℂ (twoClockCorrection c h) (centeredLogColumn c 0)-
        inner ℂ (jointCotest c h) (nativeSmooth c):=by
  have generated:=native_inverse_price c (twoClockCorrection c h)
  rw [native_block_source,inner_sub_right,inner_smul_right,
    actual_two_clock_correction_source c h nonnegative] at generated
  linear_combination generated

/-- The original complete joint source keeps its full Unit while its actual B price is delivered by the native source. -/
theorem actual_complete_native_price (c:BurnolCompletedMellinCoordinate) (h:ℝ)
    (nonnegative:0≤h) (bounded:h≤Real.log 2):
    OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.CrossContact.completeJointModel c h (star c.value)=
      -inner ℂ (OriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer.movedTest c h)
        (OriginalKElementaryArithmeticAction.FreeParameter.Riesz.freeUnit (star c.value) ConstantDual.value)+
      leading c*inner ℂ (twoClockCorrection c h) (centeredLogColumn c 0)-
        inner ℂ (jointCotest c h) (nativeSmooth c):=by
  rw [actual_complete_joint_source_price c c h nonnegative bounded,actual_two_clock_native_price c h nonnegative]
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
