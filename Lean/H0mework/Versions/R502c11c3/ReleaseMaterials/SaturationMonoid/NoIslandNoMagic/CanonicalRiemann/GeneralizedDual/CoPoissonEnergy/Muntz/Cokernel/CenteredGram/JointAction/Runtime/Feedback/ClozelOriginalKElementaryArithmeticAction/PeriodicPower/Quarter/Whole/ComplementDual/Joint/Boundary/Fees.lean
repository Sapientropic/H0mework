import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.OriginalH
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.PairedSharp

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fees
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKPairedBEulerJunctionSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fields OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.FourField
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Prices OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.OriginalH
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.WholeResidual
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountedPa OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Field
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open scoped Topology InnerProductSpace
local notation "T"=>burnolTateReciprocalL2
local notation "P"=>burnolEvenAmbientProjection
local notation "R"=>burnolDirectRightResolventCLM
local notation "A"=>sourceAnnulusCut
local notation "D"=>burnolMultiplicativeDilation
local notation "K"=>burnolCompletedMellinRieszVector
local notation "μ"=>burnolQuarterMeanCoefficient
local notation "Rq"=>burnolQuarterRestriction
local notation "E"=>burnolQuarterZeroExtension
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "h₀"=>Real.log stageZeroSonineQ
local notation "order"=>generatedRiemannXiZeroOrder ActualAnalyticOwner
local notation "H"=>OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source.quarterWave

/-- The complete outside-source fee is determined by the actual two-clock B programme. -/
theorem actual_residual_source_fee (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    fixedFee c (P (wholeResidual c zero h positive (order c.value-1)):BurnolL2)=
      inner ℂ (T (pairedCotestReverse c)) (tateSource c (order c.value)-A (tateSource c (order c.value))):=by
  have graph:=actual_paired_cotest_tate_forward c zero
  change Tendsto (fun N:ℕ=>FiniteForcing.source N (T (physicalCotest c:BurnolL2))) atTop
    (𝓝 (T (pairedCotestReverse c))) at graph
  have generated:=graph.inner (𝕜:=ℂ)
    (tendsto_const_nhds (x:=tateSource c (order c.value)-A (tateSource c (order c.value))))
  exact tendsto_nhds_unique (actual_residual_fee_same_N c zero h positive) generated

/-- The whole fee is read by its generated acted cotest on the original compact H source. -/
theorem actual_whole_source_fee (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    fixedFee c (P (wholeArm c zero h positive):BurnolL2)=
      inner ℂ (((R c)^(order c.value)) (fourierL2.symm (pairedCotestForward c))) (H c):=by
  have graph:=actual_paired_cotest_whole_reverse c zero (order c.value)
  change Tendsto (fun N:ℕ=>DualSource.source N (wholeCotest c)) atTop
    (𝓝 (((R c)^(order c.value)) (fourierL2.symm (pairedCotestForward c)))) at graph
  have generated:=graph.inner (𝕜:=ℂ) (tendsto_const_nhds (x:=H c))
  exact tendsto_nhds_unique (actual_whole_fee_same_N c zero h positive) generated

/-- Every field in the original fixed bill now has its actual source value; both means and both moving contacts remain literal. -/
theorem actual_complete_source_bill (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    rieszAmplitude c*evaluatorSource c h₀=
      inner ℂ (T (pairedCotestReverse c)) (tateSource c (order c.value)-A (tateSource c (order c.value)))-
      inner ℂ (((R c)^(order c.value)) (fourierL2.symm (pairedCotestForward c))) (H c)-
      ((2/(1-star c.value))^(order c.value)*
        (4*deriv (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Continuation.poleFreeSource c) 1/(1-star c.value)))*
        (pairedMellinTranslationCharacter c.value h₀*(star (μ (Rq (K c:BurnolL2)))/2)-
          star (sourceMean c 0)/2+star (μ (Rq (fourierL2 (E (sourceSecond c:Hq)))))/2)+
      (-1/2:ℂ)*(inner ℂ (countedKernel c zero) (D (-h₀) (A (tateSource c (order c.value))))+
        inner ℂ (countedKernel c zero) (D h₀ (A (tateSource c (order c.value))))):=by
  rw [actual_original_four_field_price c zero h positive]
  unfold fourFieldNet
  rw [actual_residual_source_fee c zero h positive,actual_whole_source_fee c zero h positive,
    actual_compact_mass_source c zero,actual_fixed_unit_fee]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fees
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
