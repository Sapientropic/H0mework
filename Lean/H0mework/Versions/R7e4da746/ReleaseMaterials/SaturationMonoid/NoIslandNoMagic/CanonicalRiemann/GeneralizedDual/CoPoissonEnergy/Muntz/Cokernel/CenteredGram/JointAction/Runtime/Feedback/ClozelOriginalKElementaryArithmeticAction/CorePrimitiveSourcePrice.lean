import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseCoreJumpMean
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CoreLogCancellation
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCurrentRegularPrice
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKSourceGramAction OriginalKSourceResolventReconstruction OriginalKCoefficientBFiniteAction
open OriginalKElementaryArithmeticAction OriginalKExteriorCoPoissonAction OriginalKFiniteOrderRelease
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "P" => Constructor.zeroMean
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "X" => burnolAmbientMeanZeroPosition
local notation "Y" => burnolAmbientMeanZeroFourier
local notation "b" => burnolAmbientMeanZeroFirstCorrection
local notation "d" => burnolAmbientMeanZeroSecondCorrection
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
open private gap_dilation originalPa_read
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.AmbientMellin
open private supported_integral
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.FirstBandNormalization
open private evenPart_inner
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator
open private loss_inventory
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CorePosition
open private pair_raw dilation_raw
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseCoreJumpMean
open private column_raw
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.Source

private theorem elementary_restriction (c:BurnolCompletedMellinCoordinate) :
    Rq (elementarySource c)=GapEuler.gapMean q c • intervalConstant q :=
  gapState_restriction c

private theorem quarter_price (value:BurnolL2) (state:Hq) :
    inner ℂ value (E state)=inner ℂ (Rq value) state :=
  ContinuousLinearMap.adjoint_inner_right Rq value state

private theorem quarter_price_left (value:BurnolL2) (state:Hq) :
    inner ℂ (E state) value=inner ℂ state (Rq value) :=
  ContinuousLinearMap.adjoint_inner_left Rq value state

private theorem elementary_supported_price (c:BurnolCompletedMellinCoordinate) (value:BurnolL2)
    (support:value=E (Rq value)) :
    inner ℂ (elementarySource c) value=star (GapEuler.gapMean q c)*(∫x:ℝ,value x) := by
  have price:inner ℂ (elementarySource c) value=
      star (GapEuler.gapMean q c)*inner ℂ ConstantDual.seed value := by
    conv_lhs=>rhs; rw [support]
    rw [quarter_price,elementary_restriction,inner_smul_left]
    rw [show ConstantDual.seed=E (intervalConstant q) from rfl,quarter_price_left]
    rfl
  have mass:inner ℂ ConstantDual.seed value=∫x:ℝ,value x:=supported_integral value support
  rw [price,mass]

private theorem elementary_meanZero_price (c:BurnolCompletedMellinCoordinate) (state:M) :
    inner ℂ (elementarySource c) (E (state:Hq))=0 := by
  rw [quarter_price,elementary_restriction,inner_smul_left]
  have mean:inner ℂ (intervalConstant q) (state:Hq)=0 :=
    (Submodule.mem_orthogonal _ _).mp state.property _ (Submodule.mem_span_singleton_self _)
  rw [mean,mul_zero]

private theorem elementary_contracted_price (c:BurnolCompletedMellinCoordinate) (state:M)
    (t:ℝ) (nn:0≤t) :
    inner ℂ (elementarySource c) (burnolMultiplicativeDilation t (E (state:Hq)))=0 := by
  have flip:=(burnolMultiplicativeDilation (-t)).inner_map_eq_flip
    (elementarySource c) (E (state:Hq))
  rw [←burnolMultiplicativeDilation_neg_eq_symm,neg_neg] at flip
  rw [←flip,quarter_price,
    gap_dilation (elementarySource c) _ (elementary_restriction c) (-t) (neg_nonpos.mpr nn),inner_smul_left]
  have mean:inner ℂ (intervalConstant q) (state:Hq)=0 :=
    (Submodule.mem_orthogonal _ _).mp state.property _ (Submodule.mem_span_singleton_self _)
  rw [mean,mul_zero]

private theorem elementary_integer_price (c:BurnolCompletedMellinCoordinate) (state:M)
    (n:ℕ) (large:2≤n) :
    inner ℂ (elementarySource c) (ContinuousChannels.channel 1 (n:ℝ)
      (burnolMultiplicativeDilation (-Real.log 2) (E (state:Hq))))=0 := by
  rw [ContinuousChannels.channel,one_mul,burnolMultiplicativeDilation_add,inner_smul_right]
  have nn:0≤Real.log (n:ℝ)+ -Real.log 2 := by
    have lower:(2:ℝ)≤n := by exact_mod_cast large
    have order:=Real.strictMonoOn_log.monotoneOn
      (show (2:ℝ)∈Ioi 0 by norm_num) (show (n:ℝ)∈Ioi 0 by change 0<(n:ℝ);linarith)
      lower
    linarith
  rw [elementary_contracted_price c state _ nn,mul_zero]

private theorem elementary_firstBand_finite (c:BurnolCompletedMellinCoordinate) (state:M)
    (even:reflectRestricted q (state:Hq)=state) (N:ℕ) (large:2≤N) :
    inner ℂ (elementarySource c) (DualSource.source N
      (burnolMultiplicativeDilation (-Real.log 2) (E (state:Hq))))=
    inner ℂ (elementarySource c) (burnolMultiplicativeDilation (-Real.log 2) (E (state:Hq)))+
      (Real.sqrt 2:ℂ)*star (GapEuler.gapMean q c)*inner ℂ SmallScaleLog.logL2 (state:Hq) := by
  have integer:inner ℂ (elementarySource c) (DualSource.source N
      (burnolMultiplicativeDilation (-Real.log 2) (E (state:Hq))))=
      inner ℂ (elementarySource c) (burnolMultiplicativeDilation (-Real.log 2) (E (state:Hq)))-
        inner ℂ (elementarySource c) (FirstBandNormalization.normalPlus (N:ℝ)
          (burnolMultiplicativeDilation (-Real.log 2) (E (state:Hq)))) := by
    rw [DualSource.source,inner_sub_right,inner_sum]
    congr 1
    rw [Finset.sum_eq_single 1]
    · simp only [Nat.cast_one,ContinuousChannels.channel,Real.sqrt_one,Complex.ofReal_one,
        inv_one,Real.log_one,mul_zero,burnolMultiplicativeDilation_zero,one_smul]
    · intro n member different
      exact elementary_integer_price c state n (by have := (Finset.mem_Ico.mp member).1;omega)
    · intro absent
      exact (absent (Finset.mem_Ico.mpr ⟨le_rfl,by omega⟩)).elim
  rw [integer,elementary_supported_price c _
      (FirstBandNormalization.shifted_support state even (N:ℝ) (by exact_mod_cast large)),
    FirstBandNormalization.shifted_integral state even (N:ℝ) (by exact_mod_cast large)]
  ring

/-- Actual finite reverse channels pay the original elementary/SB price, including their log compensation. -/
theorem elementary_fullReverse_SB_price (c:BurnolCompletedMellinCoordinate)
    (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    inner ℂ (elementarySource c) (FullUnit.fullReverse c h 1)=
      inner ℂ (elementarySource c) (FullUnit.fullSource c h 1)+
        (Real.sqrt 2:ℂ)*star (GapEuler.gapMean q c)*
          inner ℂ SmallScaleLog.logL2 (lossFirstBandColumn c h:Hq) := by
  have input:= (tendsto_const_nhds (x:=elementarySource c)).inner (𝕜:=ℂ)
    (FullUnit.full_reverse_tendsto c h nn 1)
  have finite:Tendsto (fun N:ℕ=>inner ℂ (elementarySource c)
      (DualSource.source N (FullUnit.fullSource c h 1))) atTop
      (𝓝 (inner ℂ (elementarySource c) (FullUnit.fullSource c h 1)+
        (Real.sqrt 2:ℂ)*star (GapEuler.gapMean q c)*
          inner ℂ SmallScaleLog.logL2 (lossFirstBandColumn c h:Hq))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (2:ℕ)] with N large
    rw [←loss_firstBand_expanded c h nn bound]
    exact (elementary_firstBand_finite c _ (loss_firstBand_even c h nn bound) N large).symm
  exact tendsto_nhds_unique input finite

private theorem elementary_Pa_price (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (value:BurnolL2) (member:value∈burnolOriginalPaInL2) :
    inner ℂ (elementarySource c) value=0 := by
  have read:inner ℂ (burnolAmbientCompletedMellinKernelFormula c) value=0 := by
    rw [←burnolAmbientCompletedMellinRieszVector_eq_kernelFormula,
      burnolAmbientCompletedMellinRieszVector_readback]
    exact (originalPa_read c zero value member).1
  obtain ⟨physical,inPa,actual⟩:=Submodule.mem_map.mp member
  have even:reflectL2 value=value := by
    change (physical:BurnolL2)=value at actual
    rw [←actual]
    exact mem_evenL2ClosedFace_iff.mp physical.property.2
  exact (evenPart_inner _ _ even).trans read

/-- The generated finite forward wave pays this elementary price; the complete unit remains. -/
theorem elementary_fullForward_F_price (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    inner ℂ (elementarySource c) (fourierL2 (FullUnit.fullForward c h 0))=
      centeringMean c h 0*inner ℂ (elementarySource c) (fourierL2 ConstantForward.value) := by
  rw [FullUnit.fullForward,map_add,map_smul,inner_add_right,inner_smul_right,
    elementary_Pa_price c zero _ (burnolOriginalPaInL2_fourier (exterior_wave_inPa c h nn bound 0)),zero_add]

/-- The only elementary/SB source cost is the original raw outward window, not an opaque reverse effect. -/
theorem elementary_loss_SB_source (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
    inner ℂ (elementarySource c) (FullUnit.fullSource c h 1)=
      OriginalReverseCoreJumpMean.rawPair (burnolEvenRaw (burnolAmbientMellinKernelRaw c))
        (OriginalReverseCoreJumpMean.dilationProfile (-h)
          ((symmetricInterval q).indicator (sourceProfile c 1))) := by
  change inner ℂ (elementarySource c) (OriginalKSourceFiniteUpdate.OriginalBFiniteAction.fullWindowLoss h (sourceSB c))=_
  rw [loss_inventory,inner_sub_right,elementary_meanZero_price,sub_zero]
  exact pair_raw _ _ _ _ (gapState_read c) (dilation_raw (-h) _ _ (column_raw c 1))

def elementaryBoundarySourcePrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
  let raw:=burnolEvenRaw (burnolAmbientMellinKernelRaw c)
  pairedMellinTranslationCharacter c.value h*OriginalReverseCoreJumpMean.rawPair raw (elementaryReverseRaw c)-
    (1/2:ℂ)*(OriginalReverseCoreJumpMean.rawPair raw
      (OriginalReverseCoreJumpMean.dilationProfile h (elementaryReverseRaw c))+
      OriginalReverseCoreJumpMean.rawPair raw
        (OriginalReverseCoreJumpMean.dilationProfile (-h) (elementaryReverseRaw c)))

def elementaryCoreSourcePrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
  elementaryBoundarySourcePrice c h-(1/2:ℂ)*
    (OriginalReverseCoreJumpMean.rawPair (burnolEvenRaw (burnolAmbientMellinKernelRaw c))
      (OriginalReverseCoreJumpMean.dilationProfile (-h)
        ((symmetricInterval q).indicator (sourceProfile c 1)))+
      (Real.sqrt 2:ℂ)*star (GapEuler.gapMean q c)*
        inner ℂ SmallScaleLog.logL2 (lossFirstBandColumn c h:Hq)-
      centeringMean c h 0*inner ℂ (elementarySource c) (fourierL2 ConstantForward.value))

private theorem elementary_boundary_source (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) :
    inner ℂ (elementarySource c)
      (OriginalKFixedBoundarySourceFibre.finiteBoundaryAction c h (elementaryReverseSource c zero))=
      elementaryBoundarySourcePrice c h := by
  have raw:(elementarySource c:ℝ→ℂ)=ᵐ[volume] burnolEvenRaw (burnolAmbientMellinKernelRaw c):=gapState_read c
  unfold OriginalKFixedBoundarySourceFibre.finiteBoundaryAction elementaryBoundarySourcePrice
  dsimp only
  rw [inner_sub_right,inner_smul_right,inner_smul_right,inner_add_right]
  rw [pair_raw _ _ _ _ raw (elementary_reverse_raw c zero),
    pair_raw _ _ _ _ raw (dilation_raw h _ _ (elementary_reverse_raw c zero)),
    pair_raw _ _ _ _ raw (dilation_raw (-h) _ _ (elementary_reverse_raw c zero))]

/-- Complete primitive/core price is calculated from actual finite Dirichlet, B-window and log source data. -/
theorem elementary_core_source (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    inner ℂ (elementarySource c) (coreReverseSource c zero h)=elementaryCoreSourcePrice c h := by
  unfold coreReverseSource elementaryCoreSourcePrice
  rw [inner_sub_right,inner_smul_right,inner_sub_right,elementary_boundary_source c zero h,
    elementary_fullReverse_SB_price c h nn bound,elementary_loss_SB_source,
    elementary_fullForward_F_price c zero h nn bound]

end OriginalCurrentRegularPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
