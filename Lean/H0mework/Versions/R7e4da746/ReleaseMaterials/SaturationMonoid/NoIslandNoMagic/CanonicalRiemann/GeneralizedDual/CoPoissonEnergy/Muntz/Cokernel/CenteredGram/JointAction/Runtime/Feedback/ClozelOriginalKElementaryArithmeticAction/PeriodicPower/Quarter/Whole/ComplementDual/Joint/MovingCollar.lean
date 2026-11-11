import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.PaUpdate

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingCollar
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.PaUpdate
open scoped Topology InnerProductSpace
local notation "T"=>burnolTateReciprocalL2
local notation "A"=>sourceAnnulusCut
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate
local instance physicalComplete:CompleteSpace BurnolPaAmbientCarrier:=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def fixedShift:ℝ:=Real.log stageZeroSonineQ

private theorem fixed_nonnegative:0≤fixedShift:=by
  apply Real.log_nonneg
  change 1≤Real.sqrt 3
  exact Real.one_le_sqrt.mpr (by norm_num)

private theorem fixed_admitted:4*Real.exp (-fixedShift)∈Icc (1/4:ℝ) 4:=by
  have one:1≤stageZeroSonineQ:=by
    change 1≤Real.sqrt 3
    exact Real.one_le_sqrt.mpr (by norm_num)
  have two:stageZeroSonineQ≤2:=by
    change Real.sqrt 3≤2
    exact Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  rw [fixedShift,Real.exp_neg,Real.exp_log stageZeroSonineQ_pos]
  change (1/4:ℝ)≤4/stageZeroSonineQ∧4/stageZeroSonineQ≤4
  constructor
  · apply (le_div_iff₀ stageZeroSonineQ_pos).mpr
    nlinarith
  · apply (div_le_iff₀ stageZeroSonineQ_pos).mpr
    nlinarith

def movingNext (c:BurnolCompletedMellinCoordinate) (j:ℕ):BurnolPaAmbientCarrier:=
  sourceTruncatedPhysicalAction (barC c) fixedShift (actualPa c j) fixed_admitted+
    forcingCoefficient c j • sourceTruncatedPhysicalAction (barC c) fixedShift
      (volterraPhysicalShell (barC c) 4) fixed_admitted

theorem actual_moving_next_mem (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    movingNext c j∈burnolCompactCoPoissonClosedRange:=
  burnolCompactCoPoissonClosedRange.toSubmodule.add_mem (sourceTruncatedPhysicalAction_mem _ _ _ _)
    (burnolCompactCoPoissonClosedRange.toSubmodule.smul_mem _ (sourceTruncatedPhysicalAction_mem _ _ _ _))

/-- The original fixed action occurs before its source cut, and the actual next Pa is transported whole. -/
theorem actual_moving_next_source (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    T (burnolMobiusSourceL2 (movingNext c j))=
      A (burnolMultiplicativeDilation (-fixedShift)
        (T (burnolMobiusSourceL2 (actualPa c (j+1))))):=by
  rw [movingNext,map_add,map_add,map_smul,map_smul,
    sourceTruncatedPhysicalAction_source _ _ fixed_nonnegative fixed_admitted _ (actual_pa_mem c j),
    sourceTruncatedPhysicalAction_source _ _ fixed_nonnegative fixed_admitted _ (volterraPhysicalShell_mem _ _),
    actual_next_pa]
  simp only [map_add,map_smul]
  rfl

def movingExterior (c:BurnolCompletedMellinCoordinate) (j:ℕ):BurnolL2:=
  sourceExteriorCollar fixedShift (T (burnolMobiusSourceL2 (actualPa c (j+1))))

def movingExteriorValue (c:BurnolCompletedMellinCoordinate) (j:ℕ):BurnolL2:=
  burnolMultiplicativeDilation (-fixedShift) (fourierL2 (actualPa c (j+1):BurnolL2))-
    fourierL2 (movingNext c j:BurnolL2)

/-- The two fixed-h0 exterior collars are the actual wave difference, with no shifted-Pa premise. -/
theorem actual_moving_exterior_realizes (c:BurnolCompletedMellinCoordinate) (j:ℕ)
    (test:SchwartzMap ℝ ℂ):
    burnolRemainderSourceRead (movingExterior c j) test=
      (Lp.toTemperedDistributionCLM ℂ volume 2 (movingExteriorValue c j)) test:=by
  rw [movingExterior,sourceExteriorCollar,←actual_moving_next_source,
    ←burnolRemainderSourceReadCLM_apply,map_sub,
    burnolRemainderSourceReadCLM_apply,burnolRemainderSourceReadCLM_apply,
    original_tate_source_shift_realizes _ _ (actual_pa_mem c (j+1)),
    original_tate_source_realizes _ (actual_moving_next_mem c j),movingExteriorValue,map_sub]
  rfl

/-- The original zero-owned K independently consumes the generated fixed-h0 Pa and reads the complete exterior. -/
theorem actual_original_fixed_K_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (j:ℕ):
    inner ℂ (burnolCompletedMellinRieszVector c:BurnolL2)
      (burnolMultiplicativeDilation fixedShift (actualPa c (j+1):BurnolL2))=
      inner ℂ (fourierL2 (burnolCompletedMellinRieszVector c:BurnolL2)) (movingExteriorValue c j):=by
  have orthogonal:=riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c zero
  have paid:inner ℂ (burnolCompletedMellinRieszVector c:BurnolL2) (movingNext c j:BurnolL2)=0:=
    inner_eq_zero_symm.mpr ((Submodule.mem_orthogonal _ _).mp orthogonal _ (actual_moving_next_mem c j))
  have acted:=fourierL2.inner_map_map (burnolCompletedMellinRieszVector c:BurnolL2)
    (burnolMultiplicativeDilation fixedShift (actualPa c (j+1):BurnolL2))
  rw [fourierL2_burnolMultiplicativeDilation] at acted
  rw [movingExteriorValue,inner_sub_right,fourierL2.inner_map_map,paid,sub_zero]
  exact acted.symm

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingCollar
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
