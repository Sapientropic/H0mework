import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Prices

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.OriginalH
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Prices OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fields OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.FourField
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Compact OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Paired OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Realized
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.OriginalK OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Realizer OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa
open scoped Topology InnerProductSpace
open private forward_reflect from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingJointEnergy
local notation "T"=>burnolTateReciprocalL2
local notation "F"=>fourierL2
local notation "P"=>burnolEvenAmbientProjection
local notation "E"=>burnolQuarterZeroExtension
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "AN"=>FiniteForcing.source
local notation "DN"=>DualSource.source
local notation "H"=>quarterWave
local notation "leading"=>ForcingPrimitive.leadingCoefficient
local notation "order"=>generatedRiemannXiZeroOrder ActualAnalyticOwner

private theorem original_B_even (c:BurnolCompletedMellinCoordinate):
    reflectL2 (E (burnolRieszSingleFourierSource c:Hq))=E (burnolRieszSingleFourierSource c:Hq):=by
  change reflectL2 (burnolRadiusZeroExtension (1/4:ℝ) (burnolRieszSingleFourierSource c:Hq))=_
  rw [burnolRadiusZeroExtension_reflect,burnolRieszSingleFourierSource_reflection_fixed]
  rfl

private theorem ambient_even (c:BurnolCompletedMellinCoordinate):
    reflectL2 (AmbientCounting.value c)=AmbientCounting.value c:=by
  have original:=AmbientCounting.original_ambient_limit c
  have reflected:=(reflectL2.continuous.tendsto _).comp original
  have finite (N:ℕ):reflectL2 (AN N (E (burnolRieszSingleFourierSource c:Hq)))=
      AN N (E (burnolRieszSingleFourierSource c:Hq)):=by
    rw [forward_reflect,original_B_even]
  exact tendsto_nhds_unique (reflected.congr' (Eventually.of_forall finite)) original

/-- The complete original whole value is determined by the actual compact H−B programme and original B programme. -/
theorem actual_whole_native_value (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    wholeValue c zero h positive=nativeProgramme c+AmbientCounting.value c:=by
  have original:=actual_original_joint_forward_value c zero h positive
  change nativeProgramme c+leading c • F (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired.poissonPair (logProgramme c))-
    F (-PositionCounting.value c zero-T (CountingDual.value c))=
      wholeValue c zero h positive+F (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor.fullFloorValue c zero) at original
  rw [actual_original_C_position_count c zero,map_add,map_smul] at original
  simp only [map_sub,map_neg] at original
  have B:T (CountingDual.value c)=F (AmbientCounting.value c):=by
    rw [DualLanding.original_tate_fourier,burnolTateReciprocalL2_involutive]
  rw [B,fourierL2_fourierL2,ambient_even] at original
  linear_combination (norm:=module) -original

/-- The original H itself generates the whole actual strong forward graph; no origin or ordinary mass premise is inserted. -/
theorem actual_original_H_forward (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    Tendsto (fun N:ℕ=>AN N (H c)) atTop (𝓝 (wholeValue c zero h positive)):=by
  have generated:=(actual_native_forward c).add (AmbientCounting.original_ambient_limit c)
  rw [←actual_whole_native_value c zero h positive] at generated
  have split:H c=E (nativeCompact c)+E (burnolRieszSingleFourierSource c:Hq):=by
    rw [quarterWave,nativeCompact,map_sub]
    module
  have finite (N:ℕ):AN N (H c)=AN N (E (nativeCompact c))+AN N (E (burnolRieszSingleFourierSource c:Hq)):=by
    change CountingDual.sourceCLM N (H c)=_
    rw [split,map_add]
    rfl
  exact generated.congr' (Eventually.of_forall (fun N=>(finite N).symm))

/-- The same actual compact H source consumes the whole acted boundary cotest at every finite N. -/
theorem actual_whole_fee_same_N (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    Tendsto (fun N:ℕ=>inner ℂ (DN N (wholeCotest c)) (H c)) atTop
      (𝓝 (fixedFee c (P (wholeArm c zero h positive):BurnolL2))):=by
  have generated:=(tendsto_const_nhds (x:=wholeCotest c)).inner (𝕜:=ℂ) (actual_original_H_forward c zero h positive)
  rw [←actual_whole_boundary_price c zero h positive] at generated
  have finite (N:ℕ):inner ℂ (wholeCotest c) (AN N (H c))=inner ℂ (DN N (wholeCotest c)) (H c):=by
    calc
      _=star (inner ℂ (AN N (H c)) (wholeCotest c)):=(inner_conj_symm _ _).symm
      _=star (inner ℂ (H c) (DN N (wholeCotest c))):=congrArg star (CountingDual.source_pairing N (H c) (wholeCotest c))
      _=_:=inner_conj_symm _ _
  exact generated.congr' (Eventually.of_forall finite)

/-- The true outside source similarly consumes the uncut fixed cotest with the same N and complete residual value. -/
theorem actual_residual_fee_same_N (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h):
    Tendsto (fun N:ℕ=>inner ℂ (AN N (T (physicalCotest c:BurnolL2)))
      (tateSource c (order c.value)-sourceAnnulusCut (tateSource c (order c.value)))) atTop
      (𝓝 (fixedFee c (P (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.WholeResidual.wholeResidual c zero h positive (order c.value-1)):BurnolL2))):=by
  have positiveOrder:=generatedRiemannXiZeroOrder_pos (burnolPaZeroObservation c zero)
    (burnolPaZeroObservation_nontrivial c zero)
  change 0<order c.value at positiveOrder
  have source:=OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountedPa.actual_whole_residual_reverse c zero h positive (order c.value-1)
  rw [Nat.sub_add_cancel positiveOrder] at source
  have generated:=(tendsto_const_nhds (x:=T (physicalCotest c:BurnolL2))).inner (𝕜:=ℂ) source
  rw [OriginalRieszFiniteSynthesis.tate_pairing,burnolTateReciprocalL2_involutive,
    ←actual_projection_fee] at generated
  exact generated.congr' (Eventually.of_forall (fun N=>(CountingDual.source_pairing N _ _).symm))

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.OriginalH
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
