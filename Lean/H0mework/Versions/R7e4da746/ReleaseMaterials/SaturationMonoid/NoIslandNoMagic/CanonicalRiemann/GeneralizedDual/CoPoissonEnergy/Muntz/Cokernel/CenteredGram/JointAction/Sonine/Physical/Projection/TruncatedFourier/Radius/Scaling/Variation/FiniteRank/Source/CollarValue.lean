import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.Source.PhysicalTransfer

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalConstantFourierCollarValue
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing
open OriginalKPairedBEulerJunctionSource OriginalConstantFourierPhysicalTransfer
open OriginalConstantFourierPriceFlow
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "p" => junctionPoint
local notation "h0" => junctionShift
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "BI" => burnolMeanZeroBlockInverse
local notation "μq" => volume.restrict (symmetricInterval q)
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

def collarClock (x:ℝ) : ℝ := Real.log (Real.exp h0*x/q)
def transferOuter (c:BurnolCompletedMellinCoordinate) (side:Fin 2) (x:ℝ) : ℂ :=
  (Real.exp (h0/2):ℂ)/2*
    (sourceTransfer c (collarClock x) side 0*Kernel.A c+
      sourceTransfer c (collarClock x) side 1*Kernel.beta c)

private def originalProfile (c:BurnolCompletedMellinCoordinate) (side:Fin 2) (x:ℝ) : ℂ :=
  ![positionSource c x,burnolRieszSingleFourierSourceRaw c x] side

private theorem actual_clock (x:ℝ) (positive:0<x) :
    physicalClock (collarClock x)=Real.exp h0*x := by
  have inside : 0<Real.exp h0*x/q := by positivity
  unfold physicalClock collarClock
  rw [Real.exp_log inside]
  field_simp

private theorem actual_transfer_outer (c:BurnolCompletedMellinCoordinate) (side:Fin 2)
    (x:ℝ) (positive:0<x) : transferOuter c side x=
      (Real.exp (h0/2):ℂ)/2*originalProfile c side (Real.exp h0*x) := by
  have actual := actual_physical_transfer c (collarClock x)
  rw [actual_clock x positive] at actual
  fin_cases side
  · exact congrArg (fun z:ℂ=>(Real.exp (h0/2):ℂ)/2*z) actual.1.symm
  · exact congrArg (fun z:ℂ=>(Real.exp (h0/2):ℂ)/2*z) actual.2.symm

private theorem transfer_outer_continuous (c:BurnolCompletedMellinCoordinate) (side:Fin 2) :
    ContinuousOn (transferOuter c side) (Icc p q) := by
  intro x member
  have positive : 0<x := junctionPoint_bounds.1.trans_le member.1
  have same : transferOuter c side =ᶠ[𝓝 x]
      (fun y:ℝ=>(Real.exp (h0/2):ℂ)/2*originalProfile c side (Real.exp h0*y)) := by
    filter_upwards [lt_mem_nhds positive] with y yPositive
    exact actual_transfer_outer c side y yPositive
  have scaled : 0<Real.exp h0*x := mul_pos (Real.exp_pos _) positive
  have continuous : ContinuousAt (originalProfile c side) (Real.exp h0*x) := by
    fin_cases side
    · exact positionSource_continuousAt c scaled
    · exact burnolRieszSingleFourierSourceRaw_continuousAt c scaled.ne'
  have generated := (continuous.comp (by fun_prop : ContinuousAt (fun y:ℝ=>Real.exp h0*y) x)).const_mul
    ((Real.exp (h0/2):ℂ)/2)
  exact (generated.congr_of_eventuallyEq same).continuousWithinAt

/-- This L2 source is generated only from the constant-response transfer and original A/beta. -/
def transferWindow (c:BurnolCompletedMellinCoordinate) (side:Fin 2) : Hq :=
  (TwoPieceFourierAction.piece_native p junctionPoint_bounds.1 junctionPoint_bounds.2
    (fun _=>0) (transferOuter c side) continuousOn_const (transfer_outer_continuous c side)).toLp
      (TwoPieceFourierAction.pieceRaw p (fun _=>0) (transferOuter c side))

private theorem transfer_window_read (c:BurnolCompletedMellinCoordinate) (side:Fin 2) :
    (transferWindow c side:ℝ→ℂ)=ᵐ[μq]
      TwoPieceFourierAction.pieceRaw p (fun _=>0) (transferOuter c side) :=
  MemLp.coeFn_toLp _

private theorem actual_raw_piece (c:BurnolCompletedMellinCoordinate) (side:Fin 2) (x:ℝ) :
    TwoPieceFourierAction.pieceRaw p (fun _=>0) (transferOuter c side) x=
      driveRaw c side x-driveInnerRaw c side 0 := by
  unfold TwoPieceFourierAction.pieceRaw driveRaw
  by_cases inside:|x|≤p
  · rw [if_pos inside,if_pos inside]
    simp only [driveInnerRaw,sub_self]
  · rw [if_neg inside,if_neg inside]
    have positive : 0 < |x| := junctionPoint_bounds.1.trans (lt_of_not_ge inside)
    rw [actual_transfer_outer c side |x| positive]
    fin_cases side
    · change (Real.exp (h0/2):ℂ)/2*positionSource c (Real.exp h0*|x|)=
        driveOuterRaw c 0 |x|-driveInnerRaw c 0 0
      simp only [driveOuterRaw,driveInnerRaw,originalOuter,originalGap,
        Matrix.cons_val_zero]
      rw [positionSource_eq_outer_sub_mean]
      ring
    · change (Real.exp (h0/2):ℂ)/2*burnolRieszSingleFourierSourceRaw c (Real.exp h0*|x|)=
        driveOuterRaw c 1 |x|-driveInnerRaw c 1 0
      simp only [driveOuterRaw,driveInnerRaw,originalOuter,originalGap,
        Matrix.cons_val_zero,Matrix.cons_val_one]
      ring

open private drive_raw_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource

/-- The removed mean is the literal original inner carrier, including both ordinary means. -/
theorem actual_complete_window (c:BurnolCompletedMellinCoordinate) (side:Fin 2) :
    transferWindow c side=(sourceDrive c side:Hq)-driveInnerRaw c side 0 • intervalConstant q := by
  apply Lp.ext
  filter_upwards [transfer_window_read c side,drive_raw_read c side,
    Lp.coeFn_sub (sourceDrive c side:Hq) (driveInnerRaw c side 0 • intervalConstant q),
    Lp.coeFn_smul (driveInnerRaw c side 0) (intervalConstant q),intervalConstant_coeFn q]
    with x generated original difference scalar constant
  rw [generated,difference,Pi.sub_apply,scalar,Pi.smul_apply,constant,smul_eq_mul,mul_one,original]
  exact actual_raw_piece c side x

def generatedDrive (c:BurnolCompletedMellinCoordinate) (side:Fin 2) : M :=
  Constructor.zeroMean (transferWindow c side)

theorem actual_original_drive (c:BurnolCompletedMellinCoordinate) (side:Fin 2) :
    generatedDrive c side=sourceDrive c side := by
  unfold generatedDrive
  rw [actual_complete_window,map_sub,map_smul,Constructor.zeroMean_constant,smul_zero,sub_zero]
  apply Subtype.ext
  exact Submodule.starProjection_eq_self_iff.mpr (sourceDrive c side).property

/-- A finite source programme now computes the specified original value, with no target field input. -/
def generatedPrice (c:BurnolCompletedMellinCoordinate) : ℂ :=
  inner ℂ (power c) (BI (generatedDrive c 1-S (generatedDrive c 0)))

theorem actual_generated_price (c:BurnolCompletedMellinCoordinate) :
    generatedPrice c=OriginalWholeDebtRJointMobiusContactClosureSource.finitePrice c c := by
  unfold generatedPrice
  rw [actual_original_drive,actual_original_drive]
  change inner ℂ (power c) (BI (nativeDrive c))=_
  rw [actual_second_source_preimage]
  rfl

end OriginalConstantFourierCollarValue
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
