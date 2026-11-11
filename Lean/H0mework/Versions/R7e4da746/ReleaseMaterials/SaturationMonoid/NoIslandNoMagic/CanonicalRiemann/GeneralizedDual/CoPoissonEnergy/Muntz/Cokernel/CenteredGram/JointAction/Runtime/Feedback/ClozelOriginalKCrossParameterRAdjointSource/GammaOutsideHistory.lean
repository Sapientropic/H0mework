import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.GammaOutsideDomain

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.GammaOutsideHistory

open MeasureTheory BurnolPhysicalState
open OriginalGamma.Source.KGamma OriginalGamma.Source.RelativeConductorGapReadback
open OriginalGamma.Source.JointLogConductor
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutPower
open OriginalKSourceResolventReconstruction
open OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open OriginalKCrossParameterRAdjointSource.PhysicalDefectSource
open OriginalKCrossParameterRAdjointSource.GammaOutsideDomain
open scoped InnerProductSpace

open private physical_outside_zero from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyEnergySource

local notation "R" => burnolDirectRightResolventCLM
local notation "P" => burnolEvenAmbientProjection
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "F" => fourierL2
local notation "K" => burnolCompletedMellinRieszVector
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

private def emitted (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] ℂ :=
  (-2 : ℂ) • (innerSL ℂ (F (generatedK c))).comp burnolEvenAmbientProjectionEndomorphism

private def returning (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] ℂ :=
  (-2 : ℂ) • (innerSL ℂ (hPowerPhysicalCorrection c)).comp O

/-- The old outside graph advances using both actual R ports of the same old stock. -/
def write (c : BurnolCompletedMellinCoordinate) : (BurnolL2 × BurnolL2) →L[ℂ] BurnolL2 :=
  (((emitted c).smulRight (forwardColumnGamma c)).comp (ContinuousLinearMap.fst ℂ BurnolL2 BurnolL2)) +
    (R c).comp (ContinuousLinearMap.snd ℂ BurnolL2 BurnolL2) -
  (((returning c).smulRight (actualGammaKernel (barC c))).comp
    (ContinuousLinearMap.fst ℂ BurnolL2 BurnolL2))

private theorem outside_write (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) :
    O (R c v) = emitted c v • physicalOutsideColumn c + R c (O v) -
      returning c v • (K (barC c) : BurnolL2) := by
  have split := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_add_starProjection_orthogonal v
  change (P v : BurnolL2) + O v = v at split
  have acted := congrArg (fun value : BurnolL2 => O (R c value)) split
  change O (R c ((P v : BurnolL2) + O v)) = O (R c v) at acted
  rw [map_add, map_add] at acted
  have first := original_R_projected_outside_source c v
  change O (R c (P v : BurnolL2)) = emitted c v • physicalOutsideColumn c at first
  have back := original_R_outside_physical_generatedK c v
  change (P (R c (O v)) : BurnolL2) = returning c v • generatedK (barC c) at back
  rw [generatedK_eq_original] at back
  have returned := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_add_starProjection_orthogonal (R c (O v))
  change (P (R c (O v)) : BurnolL2) + O (R c (O v)) = R c (O v) at returned
  rw [first] at acted
  rw [back] at returned
  linear_combination (norm := module) -acted + returned

theorem write_graph (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (old oldGamma : BurnolL2) (paid : GammaPair (O old) oldGamma) :
    GammaPair (O (R c old)) (write c (old, oldGamma)) := by
  intro test
  change inner ℂ (wholeConductorTest test) (O (R c old)) =
    inner ℂ (test.toLp 2 volume)
      (emitted c old • forwardColumnGamma c + R c oldGamma -
        returning c old • actualGammaKernel (barC c))
  rw [outside_write]
  simp only [inner_add_right, inner_sub_right, inner_smul_right,
    actual_forward_column_gamma c zero test, actual_Gamma_R c _ _ paid test,
    actual_gamma_original_kernel (barC c) test]

theorem physical_start_graph (v : BurnolPaAmbientCarrier) :
    GammaPair (O (v : BurnolL2)) 0 := by
  rw [physical_outside_zero]
  intro test
  simp only [inner_zero_right]

/-- The graph history reads the supplied stock at every old index. -/
def history (c : BurnolCompletedMellinCoordinate) (stock : ℕ → BurnolL2)
    (initialGamma : BurnolL2) (n : ℕ) : BurnolL2 :=
  Nat.rec initialGamma (fun n previous => write c (stock n, previous)) n

theorem history_graph (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (stock : ℕ → BurnolL2) (initialGamma : BurnolL2)
    (initial : GammaPair (O (stock 0)) initialGamma)
    (actualStep : ∀ n, stock (n+1) = R c (stock n)) (n : ℕ) :
    GammaPair (O (stock n)) (history c stock initialGamma n) := by
  induction n with
  | zero => exact initial
  | succ n prior =>
    rw [actualStep n]
    exact write_graph c zero _ _ prior

end OriginalKCrossParameterRAdjointSource.GammaOutsideHistory
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
