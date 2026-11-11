import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CompleteContact
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingJointEnergy
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.BCountingCocycle
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing
open OriginalRieszFinitePairing.CoPoisson OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKSourceFiniteUpdate.OriginalBFiniteAction
open OriginalKExteriorCoPoissonAction
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "R" => burnolQuarterRestriction
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "B" => burnolMeanZeroOneMinusSquare
local notation "C" => ConstantDual.seed
local notation "DN" => CenteredCountingDual.reverse
local notation "CN" => CenteredCountingDual.forward

/-- The inward unit profile is generated before the B source is counted. -/
def inwardUnitProfile (h:ℝ) : M := Constructor.zeroMean (R (burnolMultiplicativeDilation h C))

def sourceReverseMean (c:BurnolCompletedMellinCoordinate) (N:ℕ) : ℂ :=
  burnolQuarterMeanCoefficient (R (DualSource.source N (E (sourceB c:Hq))))

private theorem dual_dilation (N:ℕ) (t:ℝ) (v:BurnolL2) :
    DualSource.source N (burnolMultiplicativeDilation t v)=
      burnolMultiplicativeDilation t (DualSource.source N v) := by
  have channel (a:ℝ) : ContinuousChannels.channel 1 a (burnolMultiplicativeDilation t v)=
      burnolMultiplicativeDilation t (ContinuousChannels.channel 1 a v) := by
    simp only [ContinuousChannels.channel,map_smul,burnolMultiplicativeDilation_add]
    rw [add_comm]
  unfold DualSource.source
  simp_rw [channel]
  rw [map_sub,map_sum]
  congr 1
  exact (burnolMultiplicativeDilation t).toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
    (ContinuousChannels.channel_integrable 1 N v)

theorem source_reverse_mean (c:BurnolCompletedMellinCoordinate) (N:ℕ) (positive:0<N) :
    sourceReverseMean c N=2*inner ℂ SmallScaleLog.logL2 (sourceB c:Hq) := by
  have price:inner ℂ C (DualSource.source N (E (sourceB c:Hq)))=inner ℂ SmallScaleLog.logL2 (sourceB c:Hq) := by
    rw [←CountingDual.source_pairing]
    have restriction:R (FiniteForcing.source N C)=WindowCounting.harmonicCoefficient N • intervalConstant q+SmallScaleLog.logL2 :=
      WindowCounting.constant_source N positive
    have adjoint:=ContinuousLinearMap.adjoint_inner_right R (FiniteForcing.source N C) (sourceB c:Hq)
    change inner ℂ (FiniteForcing.source N C) (E (sourceB c:Hq))=_ at adjoint
    rw [adjoint,restriction,inner_add_left,inner_smul_left]
    have mean:inner ℂ (intervalConstant q) (sourceB c:Hq)=0 :=
      (Submodule.mem_orthogonal _ _).mp (sourceB c).property _ (Submodule.mem_span_singleton_self _)
    rw [mean,mul_zero,zero_add]
  have actual:=ContinuousLinearMap.adjoint_inner_left R
    (DualSource.source N (E (sourceB c:Hq))) (intervalConstant q)
  change inner ℂ C (DualSource.source N (E (sourceB c:Hq)))=_ at actual
  rw [actual] at price
  unfold sourceReverseMean burnolQuarterMeanCoefficient
  rw [Complex.ofReal_pow,burnolIntervalConstant_norm_sq (by norm_num : (0:ℝ)<q)]
  rw [price]
  norm_num
  ring

private theorem whole_reverse_B (c:BurnolCompletedMellinCoordinate) (N:ℕ) (positive:0<N) :
    DualSource.source N (E (sourceB c:Hq))=
      E (DN N (sourceB c):Hq)+sourceReverseMean c N • C := by
  have parity:reflectRestricted q (sourceB c:Hq)=sourceB c:=burnolRieszSingleFourierSource_reflection_fixed c
  have support:=CenteredCountingDualSupport.source_support (sourceB c) parity N positive
  have split:=Constructor.zeroMean_read (R (DualSource.source N (E (sourceB c:Hq))))
  change (DN N (sourceB c):Hq)=_ at split
  rw [split,map_sub,map_smul]
  change _=E (R (DualSource.source N (E (sourceB c:Hq))))-
    sourceReverseMean c N • C+sourceReverseMean c N • C
  rw [←support]
  module

/-- Its input is the reverse source, the original B finite action, and the actual unit contact. -/
def countedFirstSource (c:BurnolCompletedMellinCoordinate) (N:ℕ) (h:ℝ) : M :=
  meanZeroDilation h (DN N (sourceB c))+
    (2*inner ℂ SmallScaleLog.logL2 (sourceB c:Hq)) • inwardUnitProfile h

/-- Counting and the actual B finite source share this full quarter vector cocycle. -/
theorem source_firstB_arithmetic_action (c:BurnolCompletedMellinCoordinate) (N:ℕ) (positive:0<N)
    (h:ℝ) (nn:0≤h) : DN N (sourceFirstB c h)=countedFirstSource c N h := by
  rw [sourceFirstB_actual c h nn]
  unfold CenteredCountingDual.reverse
  rw [inward_extension h nn,dual_dilation,whole_reverse_B c N positive,
    map_add,map_smul,map_add,map_smul,map_add,map_smul,source_reverse_mean c N positive]
  rfl

private theorem firstB_even (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) :
    reflectRestricted q (sourceFirstB c h:Hq)=sourceFirstB c h := by
  have whole:E (sourceFirstB c h:Hq)=burnolMultiplicativeDilation h (E (sourceB c:Hq)) := by
    rw [sourceFirstB_actual c h nn,inward_extension h nn]
  have base:reflectL2 (E (sourceB c:Hq))=E (sourceB c:Hq) := by
    change reflectL2 (burnolRadiusZeroExtension q (sourceB c:Hq))=_
    rw [burnolRadiusZeroExtension_reflect]
    have even:reflectRestricted q (sourceB c:Hq)=sourceB c:=burnolRieszSingleFourierSource_reflection_fixed c
    rw [even]
    rfl
  have parity:reflectL2 (E (sourceFirstB c h:Hq))=E (sourceFirstB c h:Hq) := by
    rw [whole,reflectL2_burnolMultiplicativeDilation,base]
  have read:=congrArg R parity
  change R (reflectL2 (burnolRadiusZeroExtension q (sourceFirstB c h:Hq)))=_ at read
  rw [burnolRadiusZeroExtension_reflect] at read
  change R (E (reflectRestricted q (sourceFirstB c h:Hq)))=R (E (sourceFirstB c h:Hq)) at read
  rw [burnolQuarterRestriction_zeroExtension,burnolQuarterRestriction_zeroExtension] at read
  exact read

/-- The SB output is generated from the same reverse column, with both mean contacts retained. -/
def countedSecondSource (c:BurnolCompletedMellinCoordinate) (N:ℕ) (h:ℝ) : M :=
  meanZeroDilation (-h) (S (DN N (sourceB c)))+
    (2*inner ℂ SmallScaleLog.logL2 (sourceB c:Hq)) • S (inwardUnitProfile h)+
      CountingJointEnergy.contact (sourceFirstB c h)

theorem source_secondB_arithmetic_action (c:BurnolCompletedMellinCoordinate) (N:ℕ) (positive:0<N)
    (h:ℝ) (nn:0≤h) : CN N (sourceSecondB c h)=countedSecondSource c N h := by
  have action:=CountingJointEnergy.commutator N positive (sourceFirstB c h) (firstB_even c h nn)
  rw [source_firstB_arithmetic_action c N positive h nn,countedFirstSource,map_add,map_smul,
    finite_fourier_intertwining h nn] at action
  change CN N (sourceSecondB c h)-
    (meanZeroDilation (-h) (S (DN N (sourceB c)))+
      (2*inner ℂ SmallScaleLog.logL2 (sourceB c:Hq)) • S (inwardUnitProfile h))=_ at action
  unfold countedSecondSource
  linear_combination (norm:=module) action

/-- The complete finite SB programme retains its whole moved field and both generated quarter contacts. -/
def fullSBForwardWindowSource (c:BurnolCompletedMellinCoordinate) (N:ℕ) (h:ℝ) : M :=
  Constructor.zeroMean (R (burnolMultiplicativeDilation (-h)
    (FiniteForcing.source N (E (sourceSB c:Hq)))))-countedSecondSource c N h

theorem actual_full_SB_forward_window (c:BurnolCompletedMellinCoordinate) (N:ℕ) (positive:0<N)
    (h:ℝ) (nn:0≤h) :
    Constructor.zeroMean (R (FiniteForcing.source N (FullUnit.fullSource c h 1)))=
      fullSBForwardWindowSource c N h := by
  have inventory:=outward_full_source_inventory h (sourceSB c)
  rw [←sourceSecondB_actual c h nn] at inventory
  have input:FullUnit.fullSource c h 1=burnolMultiplicativeDilation (-h) (E (sourceSB c:Hq))-
      E (sourceSecondB c h:Hq) := by
    change burnolMultiplicativeDilation (-h) (E (sourceSB c:Hq))=
      E (sourceSecondB c h:Hq)+FullUnit.fullSource c h 1 at inventory
    linear_combination (norm:=module) -inventory
  rw [input,←CountingDual.sourceCLM_apply,map_sub]
  simp only [CountingDual.sourceCLM_apply]
  rw [SeedCounting.source_dilation,map_sub,map_sub]
  change _-CN N (sourceSecondB c h)=_
  rw [source_secondB_arithmetic_action c N positive h nn]
  rfl

/-- Cutoff zero retains the real empty programme, rather than borrowing the positive-N contact. -/
theorem zero_cutoff_control (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
    DN 0 (sourceFirstB c h)=0 ∧ CN 0 (sourceSecondB c h)=0 ∧
      DN 0 (sourceFirstB c h)-countedFirstSource c 0 h=
        -(2*inner ℂ SmallScaleLog.logL2 (sourceB c:Hq)) • inwardUnitProfile h := by
  rw [CenteredCountingDual.reverse_zero,CenteredCountingDual.forward_zero]
  refine ⟨rfl,rfl,?_⟩
  unfold countedFirstSource
  rw [CenteredCountingDual.reverse_zero,map_zero,zero_add,zero_sub,neg_smul]

/-- The original physical cotest consumes these exact mean-zero source vectors after they are generated. -/
theorem original_K_unit_profile_prices (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
    inner ℂ (sourceKernel c) (E (inwardUnitProfile h:Hq))=0 ∧
    inner ℂ (sourceKernel c) (fourierL2 (E (S (inwardUnitProfile h):Hq)))=0 := by
  rw [sourceKernel_original]
  let test:=burnolCompletedMellinRieszVector c
  have position (value:M) : inner ℂ (test:BurnolL2) (E (value:Hq))=0 := by
    change inner ℂ (test:BurnolL2) (burnolQuarterRestriction.adjoint (value:Hq))=0
    rw [ContinuousLinearMap.adjoint_inner_right R]
    exact value.property _ test.property.1.1
  constructor
  · exact position (inwardUnitProfile h)
  · have twice:fourierL2 (fourierL2 (test:BurnolL2))=test := by
      rw [fourierL2_fourierL2]
      exact mem_evenL2ClosedFace_iff.mp test.property.2
    have unitary:=fourierL2.inner_map_map (fourierL2 (test:BurnolL2)) (E (S (inwardUnitProfile h):Hq))
    rw [twice] at unitary
    rw [unitary]
    change inner ℂ (fourierL2 (test:BurnolL2)) (burnolQuarterRestriction.adjoint (S (inwardUnitProfile h):Hq))=0
    rw [ContinuousLinearMap.adjoint_inner_right R]
    exact (S (inwardUnitProfile h)).property _ test.property.1.2


end OriginalKElementaryArithmeticAction.BCountingCocycle
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
