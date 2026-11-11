import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CorePosition
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.FirstBandCounting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction
open Complex Filter MeasureTheory Set BurnolPhysicalState
open BurnolPhysicalState.OriginalRieszSource BurnolPhysicalState.OriginalRieszSourceGreen
open BurnolPhysicalState.OriginalRieszFinitePairing BurnolPhysicalState.OriginalRieszFiniteColumns
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKFixedBoundarySourceFibre
open OriginalKExteriorCoPoissonAction OriginalKSourceFiniteUpdate.OriginalBFiniteAction
open OriginalPaPhysicalGreen
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "R" => burnolQuarterRestriction

private theorem K_gap (c:BurnolCompletedMellinCoordinate) :
    (sourceKernel c:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)] fun _=>positionMean c := by
  rw [sourceKernel_original]
  filter_upwards [ae_restrict_of_ae (burnolRieszState_ae_raw c),ae_restrict_mem (measurableSet_symmetricInterval q)] with x raw inside
  rw [raw,position_raw,if_pos inside,add_zero]

private theorem K_supported_pair (c:BurnolCompletedMellinCoordinate) (v:BurnolL2)
    (support:v=E (R v)) : inner ℂ (sourceKernel c) v=star (positionMean c)*(∫x:ℝ,v x) := by
  have gap:=(ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (K_gap c)
  have read:=originalPhysicalCutoff_coeFn q v
  have cut:originalPhysicalCutoff q v=v:=support.symm
  rw [cut] at read
  rw [L2.inner_def,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [gap,read] with x actual cutoff
  by_cases inside:x∈symmetricInterval q
  · rw [actual inside,RCLike.inner_apply]
    simp only [starRingEnd_apply]
    ring
  · rw [cutoff,indicator_of_notMem inside]
    simp

/-- A read of the paid generic first-band action; source membership is supplied by actual constructors. -/
theorem meanZero_firstBand_counted_read (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (state:M) (even:reflectRestricted q (state:Hq)=state) :
    inner ℂ (KCountingGram.value c) (burnolMultiplicativeDilation (-Real.log 2) (E (state:Hq))) =
      inner ℂ (sourceKernel c) (burnolMultiplicativeDilation (-Real.log 2) (E (state:Hq)))+
        (Real.sqrt 2:ℂ)*star (positionMean c)*inner ℂ SmallScaleLog.logL2 (state:Hq) := by
  let expanded:=burnolMultiplicativeDilation (-Real.log 2) (E (state:Hq))
  have finite (N:ℕ) (large:2≤N) :
      inner ℂ (FiniteForcing.source N (burnolCompletedMellinRieszVector c:BurnolL2)) expanded=
        inner ℂ (sourceKernel c) expanded+(Real.sqrt 2:ℂ)*star (positionMean c)*inner ℂ SmallScaleLog.logL2 (state:Hq) := by
    rw [CountingDual.source_pairing]
    change inner ℂ (burnolCompletedMellinRieszVector c:BurnolL2) (DualSource.source N
      (burnolMultiplicativeDilation (-Real.log 2) (E (state:Hq))))=_
    rw [FirstBandCounting.finite_integer_read c state N large,←sourceKernel_original c]
    change _-inner ℂ (sourceKernel c) (FirstBandNormalization.normalPlus (N:ℝ)
      (burnolMultiplicativeDilation (-Real.log 2) (E (state:Hq))))=_
    rw [K_supported_pair c _ (FirstBandNormalization.shifted_support state even (N:ℝ) (by exact_mod_cast large)),
      FirstBandNormalization.shifted_integral state even (N:ℝ) (by exact_mod_cast large)]
    ring
  have actual: Tendsto (fun N:ℕ=>inner ℂ (FiniteForcing.source N (burnolCompletedMellinRieszVector c:BurnolL2)) expanded)
      atTop (𝓝 (inner ℂ (sourceKernel c) expanded+(Real.sqrt 2:ℂ)*star (positionMean c)*inner ℂ SmallScaleLog.logL2 (state:Hq))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (2:ℕ)] with N large
    exact (finite N large).symm
  exact tendsto_nhds_unique ((KCountingGram.forward_tendsto c zero).inner (𝕜:=ℂ) (tendsto_const_nhds (x:=expanded))) actual

def positionLogPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
  (Real.sqrt 2:ℂ)*star (positionMean c)*inner ℂ SmallScaleLog.logL2 (compressedCoreSource c h:Hq)

theorem position_core_counted_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    inner ℂ (KCountingGram.value c) (positionCoreSource c h)=inner ℂ (sourceKernel c) (positionCoreSource c h)+positionLogPrice c h := by
  have read:=meanZero_firstBand_counted_read c zero (compressedCoreSource c h) (compressed_core_even c h nn bound)
  rw [compressed_core_expanded c h nn bound] at read
  exact read

private theorem reverse_original_unit_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    inner ℂ (sourceKernel c) (elementaryReverseSource c zero)=reverseMean c zero*inner ℂ (sourceKernel c) ConstantDual.seed := by
  have zsupport:elementaryReverseSource c zero=E (R (elementaryReverseSource c zero)):=
    (elementary_reverse_support c zero).symm
  have cSupport:ConstantDual.seed=E (R ConstantDual.seed) := by
    change E (intervalConstant q)=E (R (E (intervalConstant q)))
    rw [burnolQuarterRestriction_zeroExtension]
  have zm : (∫x:ℝ,elementaryReverseSource c zero x)=(1/2:ℂ)*reverseMean c zero := by
    have read:=Constructor.mean_integral (R (elementaryReverseSource c zero))
    rw [←integral_indicator (measurableSet_symmetricInterval q)] at read
    rw [←integral_congr_ae (burnolQuarterZeroExtension_coe _)] at read
    rw [←zsupport] at read
    change reverseMean c zero=2*(∫x:ℝ,elementaryReverseSource c zero x) at read
    linear_combination -read/2
  have cm : (∫x:ℝ,ConstantDual.seed x)=(1/2:ℂ) := by
    rw [show ConstantDual.seed=E (intervalConstant q) from rfl,
      integral_congr_ae (burnolQuarterZeroExtension_coe _),integral_indicator (measurableSet_symmetricInterval q)]
    have same: (intervalConstant q:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)] fun _=>1 := intervalConstant_coeFn q
    rw [integral_congr_ae same,integral_const]
    norm_num [symmetricInterval,real_smul]
  rw [K_supported_pair c _ zsupport,K_supported_pair c _ cSupport,zm,cm]
  ring

theorem elementary_counted_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) :
    inner ℂ (KCountingGram.value c) (elementarySource c)=reverseMean c zero*inner ℂ (sourceKernel c) ConstantDual.seed := by
  have left:=(KCountingGram.forward_tendsto c zero).inner (𝕜:=ℂ) (tendsto_const_nhds (x:=elementarySource c))
  have right:=(tendsto_const_nhds (x:=(burnolCompletedMellinRieszVector c:BurnolL2))).inner (𝕜:=ℂ)
    (elementary_reverse_tendsto c zero)
  have same:=left.congr' (Eventually.of_forall (fun N=>CountingDual.source_pairing N
    (burnolCompletedMellinRieszVector c:BurnolL2) (elementarySource c)))
  have read:=tendsto_nhds_unique same right
  rw [←sourceKernel_original c,reverse_original_unit_price c zero] at read
  exact read

private theorem K_pa_read (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (v:BurnolL2) (member:v∈burnolOriginalPaInL2) : inner ℂ (sourceKernel c) v=0 := by
  obtain ⟨physical,inPa,actual⟩:=Submodule.mem_map.mp member
  have orthogonal:=riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c zero
  have read:=(burnolCompactCoPoissonClosedRange.toSubmodule.mem_orthogonal _).mp orthogonal physical inPa
  change inner ℂ (physical:BurnolL2) (burnolCompletedMellinRieszVector c:BurnolL2)=0 at read
  change (physical:BurnolL2)=v at actual
  rw [actual] at read
  rw [sourceKernel_original,←inner_conj_symm,read,map_zero]

theorem fourier_forward_unit_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    inner ℂ (sourceKernel c) (fourierL2 (FullUnit.fullForward c h 0))=
      centeringMean c h 0*inner ℂ (sourceKernel c) (fourierL2 ConstantForward.value) := by
  rw [FullUnit.fullForward,map_add,map_smul,inner_add_right,inner_smul_right,
    K_pa_read c zero _ (burnolOriginalPaInL2_fourier (exterior_wave_inPa c h nn bound 0)),zero_add]

theorem fourier_loss_counted_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    inner ℂ (KCountingGram.value c) (fourierL2 (FullUnit.fullSource c h 0))=
      centeringMean c h 0*inner ℂ (sourceKernel c) (fourierL2 ConstantForward.value) := by
  have left:=(KCountingGram.forward_tendsto c zero).inner (𝕜:=ℂ) (tendsto_const_nhds (x:=fourierL2 (FullUnit.fullSource c h 0)))
  have right:=(tendsto_const_nhds (x:=(burnolCompletedMellinRieszVector c:BurnolL2))).inner (𝕜:=ℂ)
    ((fourierL2.continuous.tendsto _).comp (FullUnit.full_forward_tendsto c h nn 0))
  have same:=left.congr' (Eventually.of_forall (fun N=>(CountingDual.source_pairing N
    (burnolCompletedMellinRieszVector c:BurnolL2) (fourierL2 (FullUnit.fullSource c h 0))).trans
      (congrArg (inner ℂ (burnolCompletedMellinRieszVector c:BurnolL2)) (KCounting.dual_fourier N (FullUnit.fullSource c h 0)))))
  have read:=tendsto_nhds_unique same right
  rw [←sourceKernel_original c,fourier_forward_unit_price c zero h nn bound] at read
  exact read

/-- Every foot of the actual core is consumed; no whole-core compactness is assumed. -/
theorem original_core_counted_difference (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    inner ℂ (KCountingGram.value c) (sourceCore c h)-inner ℂ (sourceKernel c) (sourceCore c h)=
      coreCharacterDefect c h*(reverseMean c zero*inner ℂ (sourceKernel c) ConstantDual.seed-
        inner ℂ (sourceKernel c) (elementarySource c))+positionLogPrice c h+
      (1/2:ℂ)*(centeringMean c h 0*inner ℂ (sourceKernel c) (fourierL2 ConstantForward.value)-
        inner ℂ (sourceKernel c) (fourierL2 (FullUnit.fullSource c h 0))) := by
  rw [core_two_foot_source c h]
  simp only [inner_add_right,inner_smul_right]
  rw [elementary_counted_price c zero,position_core_counted_price c zero h nn bound,fourier_loss_counted_price c zero h nn bound]
  ring

/-- The same forward-B unit read cancels between the whole comparison and the computed collar Ward. -/
theorem original_fixedResidual_firstBand_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) (fixed:h=Real.log stageZeroSonineQ) :
    -burnolPaFixedShiftResidual c zero=
      ((pairedMellinTranslationCharacter c.value h-((Real.exp (h/2):ℂ)+(Real.exp (-h/2):ℂ))/2)*reverseMean c zero+
        (2*q:ℝ)*GapEuler.gapMean q c*(Complex.exp (OriginalKSourceResolventReconstruction.sourceRate c*(h:ℂ))-(Real.exp (-h/2):ℂ)))*
        inner ℂ (sourceKernel c) ConstantDual.seed-(1/2:ℂ)*inner ℂ (sourceKernel c) (collarSource c h)-
      (1/2:ℂ)*inner ℂ (sourceKernel c) (FullUnit.fullReverse c h 1)-
      coreCharacterDefect c h*(reverseMean c zero*inner ℂ (sourceKernel c) ConstantDual.seed-
        inner ℂ (sourceKernel c) (elementarySource c))-positionLogPrice c h+
      (1/2:ℂ)*inner ℂ (sourceKernel c) (fourierL2 (FullUnit.fullSource c h 0)) := by
  have ward:=original_core_collar_ward c zero h nn bound
  have comparison:=original_core_counted_difference c zero h nn bound
  have residual:=original_fixedResidual_core c zero h nn fixed
  rw [fourier_forward_unit_price c zero h nn bound] at ward
  linear_combination ward-comparison-residual

end OriginalKElementaryArithmeticAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
