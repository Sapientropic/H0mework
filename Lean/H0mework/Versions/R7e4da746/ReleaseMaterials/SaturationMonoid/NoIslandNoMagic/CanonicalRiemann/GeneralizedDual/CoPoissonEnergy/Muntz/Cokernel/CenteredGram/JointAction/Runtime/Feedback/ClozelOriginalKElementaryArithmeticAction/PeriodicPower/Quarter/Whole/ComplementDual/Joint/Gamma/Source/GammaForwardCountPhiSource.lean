import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.CountingQuadraticLimit
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaKernelWholeWeakCountSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KForwardWholeSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KappaConductorSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.PhiConductorReadback
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorGapReadback
import H0mework.Arithmetic.BurnolCarrier.AdditiveFullEvenL2
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFourier
import H0mework.Arithmetic.BurnolPhysical.PhysicalityProjection
import H0mework.Arithmetic.BurnolMellin.CompletedMellinEvaluatorKernel
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSource
import H0mework.Arithmetic.MellinProjection.TailKernel

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.GammaForwardCountPhi
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.KGamma OriginalGamma.Source.GammaKernelWholeWeakCount OriginalGamma.Source.CountingQuadraticLimit
open OriginalGamma.Source.RelativeConductorGapReadback OriginalGamma.Source.KForwardWhole
open OriginalGamma.Source.KappaConductor OriginalGamma.Source.PhiConductorReadback
open OriginalGamma.Source.JointLogConductor
noncomputable section
local notation "K" => burnolCompletedMellinRieszVector
local notation "A" => CountingDual.sourceCLM
local notation "D" => DualSource.source
local notation "F" => fourierL2

macro "programmeCountPaid% " field:ident : term => do
  let owner:=Lean.Name.num `_private.H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaKernelWholeWeakCountSource 0
  let scope:=`SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalGamma.Source.GammaKernelWholeWeakCount
  return Lean.mkIdent (owner.append (scope.append field.getId))
macro "programmeGammaFourierPaid% " field:ident : term => do
  let owner:=Lean.Name.num `_private.H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaSource 0
  let scope:=`SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalGamma.Source.KGamma
  return Lean.mkIdent (owner.append (scope.append field.getId))
macro "programmeForwardPaid% " field:ident : term => do
  let owner:=Lean.Name.num `_private.H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KForwardWholeSource 0
  let scope:=`SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalGamma.Source.KForwardWhole
  return Lean.mkIdent (owner.append (scope.append field.getId))

private theorem forward_same_inverse_dual (N : ℕ) (v : BurnolL2) :
    A N v=F (D N (fourierL2.symm v)) := by
  have source:=source_fourier N (fourierL2.symm v)
  rw [fourierL2.apply_symm_apply] at source
  exact source

/-- The original full forward count commutes with Gamma through the actual inverse-Fourier and dual count sources. -/
theorem actual_original_forward_gamma_kernel_count_source (c : BurnolCompletedMellinCoordinate) (N : ℕ) :
    GammaPair (A N (K c:BurnolL2)) (A N (actualGammaKernel c)) := by
  have inverse:=(phiGammaPaid% gamma_pair_inverse_fourier) _ _ (actual_gamma_original_kernel c)
  have dual:=(programmeCountPaid% actual_complete_count_gamma_pair) N _ _ inverse
  have forward:=(programmeGammaFourierPaid% gamma_pair_fourier) _ _ dual
  rw [←forward_same_inverse_dual,←forward_same_inverse_dual] at forward
  exact forward

/-- Fourier read of the original forward K count reaches the same actual complete dual field. -/
theorem actual_original_fourier_forward_K_whole_source
    (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    Tendsto (fun N:ℕ=>F (A N (K c:BurnolL2))) atTop (𝓝 (originalDualField c zero)) := by
  have source := (fourierL2.continuous.tendsto (F (originalDualField c zero))).comp
    (original_forward_K_whole_source c zero)
  simpa only [Function.comp_def,fourierL2_fourierL2,(programmeForwardPaid% actual_dual_even) c zero] using source

end
end OriginalGamma.Source.GammaForwardCountPhi
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
