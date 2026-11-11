import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.RadiusConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.UnitSource
import H0mework.Versions.R7e4da746.Arithmetic.BurnolMellin.GenericPhysicalMellinRead

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.MellinSelf
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing
open OriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer
open scoped Topology InnerProductSpace
open private actual_dilation_mellin actual_smul_mellin source_ae from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.UnitSource
local notation "K" => burnolCompletedMellinRieszVector

theorem actual_K_full_mellin (c : BurnolCompletedMellinCoordinate) :
    HasMellin (K c : BurnolL2) (1-c.value) (kernelSelfSource c) := by
  have domain := burnolGenericPhysicalMellin_integrableOn_positive (K c) c
  have read := burnolCompletedMellinRieszVector_generic_readback (K c) c
  change inner ℂ (K c : BurnolL2) (K c : BurnolL2)=_ at read
  rw [original_kernel_self_source] at read
  constructor
  · simpa only [MellinConvergent,show 1-c.value-1= -c.value by ring,smul_eq_mul] using domain
  · simpa only [mellin,show 1-c.value-1= -c.value by ring,smul_eq_mul] using read.symm

/-- This is the honest full Mellin transform of the actual moved test; no ambient projection is inserted. -/
theorem actual_moved_full_mellin (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    HasMellin (movedTest c h : ℝ→ℂ) (1-c.value)
      ((reciprocalMellinTranslationCharacter c.value h-(Real.exp (h/2):ℂ))*kernelSelfSource c) := by
  have original := actual_K_full_mellin c
  have shifted := actual_dilation_mellin (K c : BurnolL2) c.value _ h original
  have scaled := actual_smul_mellin (K c : BurnolL2) (1-c.value) _ (Real.exp (h/2):ℂ) original
  have difference := hasMellin_sub shifted.1 scaled.1
  rw [shifted.2,scaled.2] at difference
  have value : Complex.exp ((c.value-1/2)*(h:ℂ))*kernelSelfSource c-
      (Real.exp (h/2):ℂ)*kernelSelfSource c=
      (reciprocalMellinTranslationCharacter c.value h-(Real.exp (h/2):ℂ))*kernelSelfSource c := by
    unfold reciprocalMellinTranslationCharacter
    ring
  rw [value] at difference
  exact source_ae _ _ _ _ (ae_restrict_of_ae
    (Lp.coeFn_sub (burnolMultiplicativeDilation h (K c : BurnolL2))
      ((Real.exp (h/2):ℂ) • (K c : BurnolL2)))) difference

theorem actual_moved_power_integral (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    (∫ x : ℝ in Ioi 0,(x:ℂ)^(-c.value)*movedTest c h x)=
      (reciprocalMellinTranslationCharacter c.value h-(Real.exp (h/2):ℂ))*kernelSelfSource c := by
  simpa only [mellin,show 1-c.value-1= -c.value by ring,smul_eq_mul] using
    (actual_moved_full_mellin c h).2

end OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.MellinSelf
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
