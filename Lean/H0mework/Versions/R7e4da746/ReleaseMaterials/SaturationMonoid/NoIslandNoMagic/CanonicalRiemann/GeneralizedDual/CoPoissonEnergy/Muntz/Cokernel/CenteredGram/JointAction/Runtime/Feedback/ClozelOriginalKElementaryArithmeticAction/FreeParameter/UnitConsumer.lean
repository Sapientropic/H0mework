import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.UnitSplice
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.FixedConsumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer
open Complex Filter MeasureTheory BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.FreeParameter.UnitSplice OriginalKElementaryArithmeticAction.FreeParameter.Family OriginalKElementaryArithmeticAction.FreeParameter.FixedConsumer
open scoped Topology InnerProductSpace
local notation "q" => (1/4 : ℝ)
local notation "K" => burnolCompletedMellinRieszVector
local notation "T" => burnolTateReciprocalL2
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

def movedTest (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  burnolMultiplicativeDilation h (K c : BurnolL2)-(Real.exp (h/2):ℂ) • (K c : BurnolL2)

def unitTest (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  fourierL2.symm (T (movedTest c h))

def fourierContacts (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  inner ℂ (burnolMultiplicativeDilation h (fourierL2 (K c : BurnolL2))) (CountingDual.value c)-
    (Real.exp (h/2):ℂ)*inner ℂ (fourierL2 (K c : BurnolL2)) (CountingDual.value c)

private theorem tate_fourier_read (test value : BurnolL2) :
    inner ℂ test (T (fourierL2 value))=inner ℂ (fourierL2.symm (T test)) value := by
  rw [←OriginalRieszFiniteSynthesis.tate_pairing]
  simpa only [fourierL2.apply_symm_apply] using
    fourierL2.inner_map_map (fourierL2.symm (T test)) value

/-- The freely varied source is read by its actual Tate/Fourier-transformed test, with every contact retained. -/
theorem actual_native_unit_read (c d : BurnolCompletedMellinCoordinate) (h : ℝ) :
    nativeRead c h (star d.value)=
      (1/2:ℂ)*inner ℂ (unitTest c h) (burnolUnitTailResponse (barC d) q)-
      constantCoefficient (star d.value)*inner ℂ (movedTest c h) ConstantDual.value-
      inner ℂ (movedTest c h) (ReturnCounting.value d)+fourierContacts c h := by
  have whole : wholeModel (star d.value)=
      (1/2:ℂ) • T (fourierL2 (burnolUnitTailResponse (barC d) q))-
      constantCoefficient (star d.value) • ConstantDual.value-ReturnCounting.value d := by
    rw [←actual_original_whole_model]
    exact actual_whole_unit_source d
  have moved (value : BurnolL2) : inner ℂ (movedTest c h) value=
      inner ℂ (burnolMultiplicativeDilation h (K c : BurnolL2)) value-
      (Real.exp (h/2):ℂ)*inner ℂ (K c : BurnolL2) value := by
    rw [movedTest,inner_sub_left,inner_smul_left,Complex.conj_ofReal]
  change inner ℂ (burnolMultiplicativeDilation h (K c : BurnolL2)) (wholeModel (star d.value))-
    (Real.exp (h/2):ℂ)*inner ℂ (K c : BurnolL2) (wholeModel (star d.value))+
    inner ℂ (burnolMultiplicativeDilation h (fourierL2 (K c : BurnolL2))) (CountingDual.value c)-
    (Real.exp (h/2):ℂ)*inner ℂ (fourierL2 (K c : BurnolL2)) (CountingDual.value c)=_
  rw [←moved,whole]
  simp only [inner_sub_right,inner_smul_right]
  rw [tate_fourier_read]
  unfold unitTest fourierContacts
  ring

end OriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
