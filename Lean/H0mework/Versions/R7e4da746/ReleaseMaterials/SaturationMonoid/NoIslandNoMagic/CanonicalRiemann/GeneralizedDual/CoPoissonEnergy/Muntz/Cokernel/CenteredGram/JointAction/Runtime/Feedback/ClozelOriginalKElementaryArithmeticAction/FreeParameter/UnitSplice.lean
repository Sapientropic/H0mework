import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.Riesz
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.Inverse
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.FourierSource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.UnitSplice
open Complex Filter MeasureTheory BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction OriginalKElementaryArithmeticAction.FreeParameter.Riesz
open OriginalKElementaryArithmeticAction.FreeParameter.Position OriginalKElementaryArithmeticAction.FreeParameter.Inverse
open OriginalUnitMellinSource.Fourier
open scoped Topology InnerProductSpace
local notation "q" => (1/4 : ℝ)
local notation "T" => burnolTateReciprocalL2
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

def constantCoefficient (s : ℂ) : ℂ := (q:ℂ)^(-s)/(2*(1-s))

/-- The original complete Poisson pair identifies the entire free inverse, including its constant. -/
theorem actual_free_inverse_unit (c : BurnolCompletedMellinCoordinate) :
    freeUnit c.value ConstantDual.value=
      constantCoefficient c.value • ConstantDual.value-
        (1/2:ℂ) • T (fourierL2 (burnolUnitTailResponse c q)) := by
  have nonzero : 1-c.value≠0 := by
    intro same
    have realPart := congrArg Complex.re same
    simp only [sub_re,one_re,zero_re] at realPart
    linarith [c.belowOne]
  rw [actual_unit_quarter_fourier,map_smul,burnolTateReciprocalL2_involutive]
  unfold freeUnit coefficient constantCoefficient
  simp only [smul_sub,smul_add,smul_smul]
  have first : c.value*(q:ℂ)^(-c.value)/(2*(1-c.value))=
      (q:ℂ)^(-c.value)/(2*(1-c.value))-(1/2:ℂ)*(q:ℂ)^(-c.value) := by
    field_simp [nonzero]
    ring
  have second : (c.value*(q:ℂ)^(-c.value)/(2*(1-c.value)))*((1-c.value)/2)=
      ((1/2:ℂ)*(q:ℂ)^(-c.value))*(c.value/2) := by
    field_simp [nonzero]
  rw [second,first,sub_smul]
  module

/-- Original P/b counting is a full Unit/Tate field minus the actual constant and B-return. -/
theorem actual_whole_unit_source (c : BurnolCompletedMellinCoordinate) :
    wholeValue c=(1/2:ℂ) • T (fourierL2 (burnolUnitTailResponse (barC c) q))-
      constantCoefficient (star c.value) • ConstantDual.value-ReturnCounting.value c := by
  rw [actual_whole_inverse_source,actual_free_unit]
  have source := actual_free_inverse_unit (barC c)
  change freeUnit (star c.value) ConstantDual.value=
    constantCoefficient (star c.value) • ConstantDual.value-
      (1/2:ℂ) • T (fourierL2 (burnolUnitTailResponse (barC c) q)) at source
  rw [source]
  module

theorem actual_original_position_unit_source (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value=0) :
    PositionCounting.value c zero=
      (1/2:ℂ) • T (fourierL2 (burnolUnitTailResponse (barC c) q))-
      constantCoefficient (star c.value) • ConstantDual.value-ReturnCounting.value c := by
  rw [←actual_original_zero_value c zero]
  exact actual_whole_unit_source c

end OriginalKElementaryArithmeticAction.FreeParameter.UnitSplice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
