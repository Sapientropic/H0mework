import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fees
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.PairedValue

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Source
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource.Translator OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKPairedBEulerJunctionSource OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fields OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.FourField
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Prices OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fees
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.WholeResidual
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountedPa OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.PaCut
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.JointSource OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Field
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open scoped Topology InnerProductSpace
local notation "T"=>burnolTateReciprocalL2
local notation "R"=>burnolDirectRightResolventCLM
local notation "P"=>burnolEvenAmbientProjection
local notation "A"=>sourceAnnulusCut
local notation "H"=>OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source.quarterWave
local notation "h₀"=>Real.log stageZeroSonineQ
local notation "order"=>generatedRiemannXiZeroOrder ActualAnalyticOwner
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate

def nativeCotest (c:BurnolCompletedMellinCoordinate):BurnolL2:=T (pairedCotestReverse c)

def nativeSource (c:BurnolCompletedMellinCoordinate):BurnolL2:=jointSource c-H c

/-- The remaining carrier is the complete original homogeneous native source; its cancellation is performed inside L2. -/
theorem actual_native_source (c:BurnolCompletedMellinCoordinate):
    nativeSource c= -ForcingWhole.whole c+fourierL2 (burnolQuarterZeroExtension
      (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source.correction c.value c.belowOne:BurnolQuarterIntervalL2)):=by
  rw [nativeSource,jointSource]
  module

private theorem actual_pa_source_fee (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (j:ℕ):
    fixedFee c (enrichedPa c j:BurnolL2)=inner ℂ (nativeCotest c) (A (tateSource c (j+1))):=by
  have forward:=actual_paired_cotest_tate_forward c zero
  change Tendsto (fun N:ℕ=>FiniteForcing.source N (T (physicalCotest c:BurnolL2))) atTop
    (𝓝 (nativeCotest c)) at forward
  have right:=(tendsto_const_nhds (x:=T (physicalCotest c:BurnolL2))).inner (𝕜:=ℂ)
    (actual_joint_annulus_reverse c j)
  have left:=forward.inner (𝕜:=ℂ) (tendsto_const_nhds (x:=A (tateSource c (j+1))))
  have same:=left.congr' (Eventually.of_forall (fun N=>CountingDual.source_pairing N _ _))
  have price:=tendsto_nhds_unique same right
  rw [OriginalRieszFiniteSynthesis.tate_pairing,burnolTateReciprocalL2_involutive] at price
  have field:=actual_projection_fee c (enrichedPa c j:BurnolL2)
  have fixed:P (enrichedPa c j:BurnolL2)=enrichedPa c j:=Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  rw [fixed] at field
  exact field.trans price.symm

private theorem source_power_price (c:BurnolCompletedMellinCoordinate) (j:ℕ) (v:BurnolL2):
    inner ℂ v (tateSource c j)=inner ℂ (((R c)^j) v) (jointSource c):=by
  have step:star (R c)=sourceVolterraResolvent (barC c):=by
    apply ContinuousLinearMap.ext
    intro value
    exact sourceStep_actual c value
  have source:tateSource c j=star ((R c)^j) (jointSource c):=by
    rw [actual_tate_outgoing,star_pow,step]
  rw [source]
  exact ContinuousLinearMap.adjoint_inner_right ((R c)^j) v (jointSource c)

/-- The true outside source and the whole generated Pa state are consumed together, before either contact is removed. -/
theorem actual_complete_pa_source_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    fixedFee c (P (wholeResidual c zero h positive (order c.value-1)):BurnolL2)+
      fixedFee c (enrichedPa c (order c.value-1):BurnolL2)=
        inner ℂ (((R c)^(order c.value)) (nativeCotest c)) (jointSource c):=by
  have positiveOrder:=generatedRiemannXiZeroOrder_pos (burnolPaZeroObservation c zero)
    (burnolPaZeroObservation_nontrivial c zero)
  change 0<order c.value at positiveOrder
  rw [actual_residual_source_fee c zero h positive,actual_pa_source_fee c zero (order c.value-1),
    Nat.sub_add_cancel positiveOrder]
  change inner ℂ (nativeCotest c) (tateSource c (order c.value)-A (tateSource c (order c.value)))+
    inner ℂ (nativeCotest c) (A (tateSource c (order c.value)))=_
  rw [inner_sub_right,sub_add_cancel,source_power_price]

/-- Whole H cancels against its own actual programme, leaving one native source and its complete original Unit. -/
theorem actual_native_boundary_bill (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    rieszAmplitude c*evaluatorSource c h₀=
      inner ℂ (((R c)^(order c.value)) (nativeCotest c)) (nativeSource c)-
        compactMass c zero*fixedFee c (originalUnit:BurnolL2):=by
  have positive:0<h₀:=junctionShift_pos
  have orderPositive:=generatedRiemannXiZeroOrder_pos (burnolPaZeroObservation c zero)
    (burnolPaZeroObservation_nontrivial c zero)
  change 0<order c.value at orderPositive
  have paFee:=actual_pa_boundary_fee c zero (order c.value-1)
  rw [Nat.sub_add_cancel orderPositive] at paFee
  have full:=actual_original_four_field_price c zero h₀ positive
  unfold fourFieldNet at full
  rw [←paFee] at full
  have complete:=actual_complete_pa_source_price c zero h₀ positive
  have whole:=actual_whole_source_fee c zero h₀ positive
  rw [←actual_paired_cotest_common_value c zero] at whole
  change fixedFee c (P (wholeArm c zero h₀ positive):BurnolL2)=
    inner ℂ (((R c)^(order c.value)) (nativeCotest c)) (H c) at whole
  rw [nativeSource,inner_sub_right]
  linear_combination full+complete-whole

/-- The same installed original fixed consumer now reads the actual native source bill. -/
theorem actual_original_native_source_consumer (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    BurnolPaBoundaryCancellationAt c zero↔
      inner ℂ (((R c)^(order c.value)) (nativeCotest c)) (nativeSource c)-
        compactMass c zero*fixedFee c (originalUnit:BurnolL2)=0:=by
  have original:=fixed_residual_source c zero
  have bill:=actual_native_boundary_bill c zero
  unfold BurnolPaBoundaryCancellationAt
  rw [installedOriginalK_fixedResidual_eq_original]
  constructor
  · intro cancelled
    rw [cancelled,neg_zero] at original
    rw [←bill,←original,mul_zero]
  · intro cancelled
    rw [cancelled] at bill
    have evaluator:evaluatorSource c h₀=0:=(mul_eq_zero.mp bill).resolve_left (actual_K_amplitude_nonzero c)
    rw [evaluator] at original
    exact neg_eq_zero.mp original

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Source
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
