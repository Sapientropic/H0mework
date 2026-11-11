import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.PaCut

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountedPa
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.PaCut OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Realized
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.WholeResidual
open scoped Topology InnerProductSpace
open private dual_tate from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
open private dual_dilation from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountingCut
local notation "T"=>burnolTateReciprocalL2
local notation "ν"=>burnolMobiusSourceL2
local notation "A"=>sourceAnnulusCut
local notation "DN"=>DualSource.source
local notation "AN"=>FiniteForcing.source
local notation "K"=>burnolCompletedMellinRieszVector
local notation "order"=>generatedRiemannXiZeroOrder ActualAnalyticOwner

def countedKernel (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):BurnolL2:=
  T (-PositionCounting.value c zero-T (CountingDual.value c))

/-- The original K's independent reverse programme supplies this forward covector at the same N. -/
theorem actual_counted_kernel_forward (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    Tendsto (fun N:ℕ=>AN N (T (K c:BurnolL2))) atTop (𝓝 (countedKernel c zero)):=by
  have generated:=(burnolTateReciprocalL2.continuous.tendsto _).comp (KCounting.original_tendsto c zero)
  have finite (N:ℕ):T (DN N (K c:BurnolL2))=AN N (T (K c:BurnolL2)):=by
    have original:=congrArg T (dual_tate N (T (K c:BurnolL2)))
    simpa only [burnolTateReciprocalL2_involutive] using original
  exact generated.congr' (Eventually.of_forall finite)

private theorem original_pa_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (j:ℕ):
    inner ℂ (K c:BurnolL2) (enrichedPa c j:BurnolL2)=0:=by
  have original:=riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c zero
  exact inner_eq_zero_symm.mpr ((Submodule.mem_orthogonal _ _).mp original _ (actual_enriched_pa_mem c j))

/-- The cut programme produces the specified whole residual, retaining its full Unit and shell columns. -/
theorem actual_whole_residual_reverse (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h) (j:ℕ):
    Tendsto (fun N:ℕ=>DN N (tateSource c (j+1)-A (tateSource c (j+1)))) atTop
      (𝓝 (T (wholeResidual c zero h positive j))):=by
  have generated:=(actual_original_joint_reverse_graph c zero h positive (j+1)).sub
    (actual_joint_annulus_reverse c j)
  have target:T (directValue c zero h positive (j+1))-T (enrichedPa c j:BurnolL2)=
      T (wholeResidual c zero h positive j):=by rw [wholeResidual,map_sub]
  rw [target] at generated
  exact generated.congr' (Eventually.of_forall (fun N=>by
    simp only [CountingDual.dual_eq_adjoint,map_sub]))

/-- Both exact same-N cut crossings now have their own full field limit. -/
theorem actual_cut_stock_reverse (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h) (j:ℕ):
    Tendsto (fun N:ℕ=>OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.cutBoundaryStock N (tateSource c (j+1))) atTop
      (𝓝 (A (T (directValue c zero h positive (j+1)))-T (enrichedPa c j:BurnolL2))):=by
  have generated:=((sourceAnnulusCut.continuous.tendsto _).comp
    (actual_original_joint_reverse_graph c zero h positive (j+1))).sub (actual_joint_annulus_reverse c j)
  exact generated.congr' (Eventually.of_forall (fun N=>OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.actual_cut_boundary_stock N _))

/-- The actual annulus source is consumed by the independent counted K and its original Pa zero. -/
theorem actual_original_K_annulus_zero (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (j:ℕ):
    inner ℂ (countedKernel c zero) (A (tateSource c (j+1)))=0:=by
  have forward:=(actual_counted_kernel_forward c zero).inner (𝕜:=ℂ)
    (tendsto_const_nhds (x:=A (tateSource c (j+1))))
  have reverse:=(tendsto_const_nhds (x:=T (K c:BurnolL2))).inner (𝕜:=ℂ) (actual_joint_annulus_reverse c j)
  have same:=forward.congr' (Eventually.of_forall (fun N=>CountingDual.source_pairing N _ _))
  have price:=tendsto_nhds_unique same reverse
  rw [OriginalRieszFiniteSynthesis.tate_pairing,burnolTateReciprocalL2_involutive,original_pa_price c zero j] at price
  exact price

/-- The original exact order consumes the generated m-th annulus, including the case m=1. -/
theorem actual_original_order_annulus_zero (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    inner ℂ (countedKernel c zero) (A (tateSource c (order c.value)))=0:=by
  have positive:=generatedRiemannXiZeroOrder_pos (burnolPaZeroObservation c zero)
    (burnolPaZeroObservation_nontrivial c zero)
  change 0<order c.value at positive
  have source:=actual_original_K_annulus_zero c zero (order c.value-1)
  rw [Nat.sub_add_cancel positive] at source
  exact source

/-- The independent original K also reads the complete residual, including every retained Unit column. -/
theorem actual_original_K_whole_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (positive:0<h) (j:ℕ):
    inner ℂ (countedKernel c zero) (tateSource c (j+1)-A (tateSource c (j+1)))=
      inner ℂ (K c:BurnolL2) (directValue c zero h positive (j+1)):=by
  have forward:=(actual_counted_kernel_forward c zero).inner (𝕜:=ℂ)
    (tendsto_const_nhds (x:=tateSource c (j+1)-A (tateSource c (j+1))))
  have reverse:=(tendsto_const_nhds (x:=T (K c:BurnolL2))).inner (𝕜:=ℂ)
    (actual_whole_residual_reverse c zero h positive j)
  have same:=forward.congr' (Eventually.of_forall (fun N=>CountingDual.source_pairing N _ _))
  have price:=tendsto_nhds_unique same reverse
  rw [OriginalRieszFiniteSynthesis.tate_pairing,burnolTateReciprocalL2_involutive] at price
  simp only [wholeResidual,inner_sub_right,original_pa_price c zero j,sub_zero] at price
  simpa only [inner_sub_right] using price

/-- Genuine movement precedes the cut source's independent counting programme and retains its complete Pa value. -/
theorem actual_moving_pa_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (j:ℕ) (shift:ℝ):
    inner ℂ (countedKernel c zero) (burnolMultiplicativeDilation shift (A (tateSource c (j+1))))=
      inner ℂ (K c:BurnolL2) (burnolMultiplicativeDilation (-shift) (enrichedPa c j:BurnolL2)):=by
  have source:=((burnolMultiplicativeDilation shift).continuous.tendsto _).comp (actual_joint_annulus_reverse c j)
  have moved:Tendsto (fun N:ℕ=>DN N (burnolMultiplicativeDilation shift (A (tateSource c (j+1))))) atTop
      (𝓝 (burnolMultiplicativeDilation shift (T (enrichedPa c j:BurnolL2)))):=
    source.congr' (Eventually.of_forall (fun N=>(dual_dilation N shift _).symm))
  have forward:=(actual_counted_kernel_forward c zero).inner (𝕜:=ℂ)
    (tendsto_const_nhds (x:=burnolMultiplicativeDilation shift (A (tateSource c (j+1)))))
  have reverse:=(tendsto_const_nhds (x:=T (K c:BurnolL2))).inner (𝕜:=ℂ) moved
  have same:=forward.congr' (Eventually.of_forall (fun N=>CountingDual.source_pairing N _ _))
  have price:=tendsto_nhds_unique same reverse
  rw [burnolTateReciprocalL2_dilation_inverse,OriginalRieszFiniteSynthesis.tate_pairing,
    burnolTateReciprocalL2_involutive] at price
  exact price

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountedPa
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
