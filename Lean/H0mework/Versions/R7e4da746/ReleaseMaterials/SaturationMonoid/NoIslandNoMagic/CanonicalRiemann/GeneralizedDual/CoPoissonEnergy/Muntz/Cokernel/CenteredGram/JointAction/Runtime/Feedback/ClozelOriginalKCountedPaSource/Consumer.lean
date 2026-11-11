import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.RContact.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCountedPaSource.Consumer
open Complex MeasureTheory Set BurnolPhysicalState
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKFiniteOrderRelease
open scoped InnerProductSpace Topology BigOperators
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
open private paCoefficientSource_mem from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.PaAdjointSource
open private whole_price from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.RContact.Consumer

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal N : ℕ)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth ordinal
local notation "feedback" => UnitPowerSource.feedbackCoefficient observation half

/-- The same counting adjoint reads the complete new input, then the existing Pa covector consumes E. -/
theorem actual_pa_fee :
    inner ℂ (FiniteForcing.source N (UnitPowerSource.paPowerField observation half:BurnolL2)) raw=
      feedback*burnolPaResolventSourceCoefficient c
        (PA.E (actualField observation nontrivial half depth ordinal N)) := by
  rw [CountingDual.source_pairing]
  change inner ℂ (UnitPowerSource.paPowerField observation half:BurnolL2)
    (actualField observation nontrivial half depth ordinal N)=_
  rw [UnitPowerSource.paPowerField,Submodule.coe_smul,inner_smul_left]
  have normal:=PA.wholePa_normal_read (actualField observation nontrivial half depth ordinal N)
    (paCoefficientSource c) (paCoefficientSource_mem c)
  have coefficient:=paCoefficientSource_read c
    (PA.E (actualField observation nontrivial half depth ordinal N))
    (Submodule.starProjection_apply_mem _ _)
  rw [←normal,coefficient]
  simp only [UnitPowerSource.paPowerCoefficient,UnitPowerSource.feedbackCoefficient,
    starRingEnd_apply,star_neg,star_mul,star_star]
  ring

/-- The original Q bill now consumes the computed counted Pa source, without discarding its full-adjoint or outside term. -/
theorem actual_counted_Q_price :
    inner ℂ (FiniteForcing.source N (UnitPowerJordanSource.sourceQ observation half)) raw=
      inner ℂ (FiniteForcing.source N (UnitPowerSource.fulladjointPowerZ observation half)) raw-
      feedback*burnolPaResolventSourceCoefficient c
        (PA.E (actualField observation nontrivial half depth ordinal N))-
      inner ℂ (CountedSchur.RContact.outsideFinite c m N) raw := by
  have original:=UnitPowerJordanMaterialConsumer.actual_unit_jordan_on_original_whole_next
    observation nontrivial half depth ordinal
  have source:=whole_price observation nontrivial half depth ordinal N original
  rw [actual_pa_fee observation nontrivial half depth ordinal N] at source
  exact source

/-- The inherited material/whole-next is the original actor; N indexes its separate source action. -/
noncomputable def read :=
  let inherited:=CountedSchur.RContact.MaterialConsumer.read observation nontrivial half depth ordinal N
  let field:=actualField observation nontrivial half depth ordinal N
  PProd.mk inherited <| PProd.mk field <| PProd.mk
    (counted_inventory N raw) <| PProd.mk
    (actual_input_inventory observation nontrivial half depth ordinal N) <| PProd.mk
    (actual_full_inventory observation nontrivial half depth ordinal N) <| PProd.mk
    (actual_outside_return observation nontrivial half depth ordinal N) <| PProd.mk
    (actual_counted_next observation nontrivial half depth ordinal N) <| PProd.mk
    (actual_Pa_source observation nontrivial half depth ordinal N) <| PProd.mk
    (actual_Mobius_source observation nontrivial half depth ordinal N) <| PProd.mk
    (actual_coefficient_source observation nontrivial half depth ordinal N) <| PProd.mk
    (actual_pa_fee observation nontrivial half depth ordinal N)
    (actual_counted_Q_price observation nontrivial half depth ordinal N)

end OriginalKCountedPaSource.Consumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
