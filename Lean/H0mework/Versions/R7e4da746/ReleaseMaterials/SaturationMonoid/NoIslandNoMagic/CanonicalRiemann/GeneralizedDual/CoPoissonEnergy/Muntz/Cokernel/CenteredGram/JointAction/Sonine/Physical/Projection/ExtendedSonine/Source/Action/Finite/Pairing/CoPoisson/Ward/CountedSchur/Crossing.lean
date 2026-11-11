import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingJointEnergy
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.SingularCounting
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.SmallScaleLog
import H0mework.Versions.R7e4da746.Arithmetic.RiemannSourceGreen.ProbeCutoffValue

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur
open Complex Filter MeasureTheory Set
open OriginalRieszSource OriginalPaPhysicalGreen
open scoped Topology InnerProductSpace
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "T" => burnolTruncatedFourier
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "Q" => Constructor.zeroMean
local notation "D" => burnolMultiplicativeDilation
local notation "F" => fourierL2
local notation "cut" => originalPhysicalCutoff
local notation "ell" => CenteredCountingDual.logarithm
local notation "sinc" => CenteredCountingDual.constantFourier
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

private theorem scaled_window (radius shift x:ℝ) :
    Real.exp shift*x∈symmetricInterval radius ↔ x∈symmetricInterval (radius*Real.exp (-shift)) := by
  simp only [symmetricInterval,Set.mem_Icc,←abs_le,abs_mul,abs_of_pos (Real.exp_pos shift)]
  simpa only [Real.exp_neg,div_eq_mul_inv,mul_comm] using
    (le_div_iff₀ (Real.exp_pos shift) : |x|≤radius/Real.exp shift ↔ |x| * Real.exp shift≤radius).symm

/-- The cutoff and actual dilation retain their original moving radius. -/
private theorem cut_dilation (radius shift:ℝ) (value:BurnolL2) :
    D shift (cut radius value)=cut (radius*Real.exp (-shift)) (D shift value) := by
  have scale:Measure.QuasiMeasurePreserving (fun x:ℝ=>Real.exp shift*x) volume volume := by
    simpa only [smul_eq_mul] using (Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ))
      (r:=Real.exp shift) (Real.exp_ne_zero shift))
  apply Lp.ext
  filter_upwards [burnolMultiplicativeDilation_coeFn shift (cut radius value),
    originalPhysicalCutoff_coeFn (radius*Real.exp (-shift)) (D shift value),
    burnolMultiplicativeDilation_coeFn shift value,
    scale.ae (originalPhysicalCutoff_coeFn radius value)] with x lhs rhs valueAt source
  rw [lhs,rhs]
  change (Real.exp (shift/2):ℂ)*cut radius value (Real.exp shift*x)=_
  rw [source]
  by_cases inside:x∈symmetricInterval (radius*Real.exp (-shift))
  · rw [indicator_of_mem inside,indicator_of_mem ((scaled_window radius shift x).mpr inside),valueAt]
    rfl
  · rw [indicator_of_notMem inside,indicator_of_notMem (fun h=>inside ((scaled_window radius shift x).mp h)),mul_zero]

private theorem dilation_quarter_cut (a:ℝ) (positive:0<a) (value:BurnolL2) :
    D (Real.log a) (cut q value)=cut (q/a) (D (Real.log a) value) := by
  simpa only [Real.exp_neg,Real.exp_log positive,div_eq_mul_inv] using cut_dilation q (Real.log a) value

private theorem quarter_cut_inverse_dilation (a:ℝ) (positive:0<a) (value:BurnolL2) :
    cut q (D (-Real.log a) value)=D (-Real.log a) (cut (q/a) value) := by
  have radius:q/a*Real.exp (-(-Real.log a))=q := by
    rw [neg_neg,Real.exp_log positive]
    field_simp
  simpa only [radius] using (cut_dilation (q/a) (-Real.log a) value).symm

/-- Literal cross-window source: two Fourier legs and the original 1/sqrt(a) weight.
No counted response is supplied to this constructor. -/
def crossWindow (a:ℝ) (state:Hq) : Hq :=
  (Real.sqrt a:ℂ)⁻¹ • Rq
    (cut (q/a) (D (Real.log a) (F (E state)))-
      D (Real.log a) (F (cut (q/a) (E state))))

def forwardCell (a:ℝ) (state:Hq) : Hq :=
  Rq (ContinuousChannels.channel (-1) a (E state))
def reverseCell (a:ℝ) (state:Hq) : Hq :=
  Rq (ContinuousChannels.channel 1 a (E state))

/-- The reverse Fourier action is recognized only after the moving-window source was constructed. -/
theorem crossWindow_action (a:ℝ) (state:Hq) :
    crossWindow a state=reverseCell a (T state)-T (forwardCell a state) := by
  by_cases positive:0<a
  · unfold forwardCell reverseCell ContinuousChannels.channel
    simp only [one_mul,neg_one_mul,map_smul]
    change crossWindow a state=(Real.sqrt a:ℂ)⁻¹ • Rq (D (Real.log a) (cut q (F (E state))))-
      (Real.sqrt a:ℂ)⁻¹ • Rq (F (cut q (D (-Real.log a) (E state))))
    rw [dilation_quarter_cut a positive,quarter_cut_inverse_dilation a positive,
      fourierL2_burnolMultiplicativeDilation,neg_neg]
    simp only [crossWindow,map_sub,smul_sub]
  · have zero:Real.sqrt a=0:=Real.sqrt_eq_zero_of_nonpos (le_of_not_gt positive)
    simp only [crossWindow,forwardCell,reverseCell,ContinuousChannels.channel,zero,
      Complex.ofReal_zero,inv_zero,zero_smul,map_zero,sub_zero]

private theorem cut_same_on_extension (radius:ℝ) (large:q≤radius) (state:Hq) :
    cut radius (E state)=E state := by
  apply Lp.ext
  filter_upwards [originalPhysicalCutoff_coeFn radius (E state),burnolQuarterZeroExtension_coe state]
    with x cutAt extension
  rw [cutAt]
  by_cases inside:x∈symmetricInterval radius
  · exact indicator_of_mem inside _
  · rw [indicator_of_notMem inside,extension]
    exact (indicator_of_notMem (fun h=>inside (Icc_subset_Icc (by linarith) large h)) _).symm

private theorem restriction_cut (radius:ℝ) (large:q≤radius) (value:BurnolL2) :
    Rq (cut radius value)=Rq value := by
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) (cut radius value),
    LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) value,
    ae_restrict_of_ae (originalPhysicalCutoff_coeFn radius value),
    ae_restrict_mem (measurableSet_symmetricInterval q)] with x left right raw inside
  change Rq (cut radius value) x=cut radius value x at left
  change Rq value x=value x at right
  have insideRadius : x∈symmetricInterval radius := Icc_subset_Icc (by linarith) large inside
  rw [left,raw,right,indicator_of_mem insideRadius]

/-- Only the uncentered cross-window part vanishes below scale one; centering is kept separately. -/
theorem crossWindow_small (a:ℝ) (positive:0<a) (small:a≤1) (state:Hq) : crossWindow a state=0 := by
  have large:q≤q/a := (le_div_iff₀ positive).mpr (by nlinarith)
  rw [crossWindow,map_sub,restriction_cut _ large,cut_same_on_extension _ large,sub_self,smul_zero]

private theorem cell_integrable (direction upper:ℝ) (state:Hq) :
    IntegrableOn (fun a:ℝ=>Rq (ContinuousChannels.channel direction a (E state))) (Ioc 0 upper) :=
  (Rq).integrable_comp (ContinuousChannels.channel_integrable direction upper (E state))

theorem crossWindow_integrable (upper:ℝ) (state:Hq) :
    IntegrableOn (fun a:ℝ=>crossWindow a state) (Ioc 0 upper) := by
  have first:=cell_integrable 1 upper (T state)
  have second:=(T).integrable_comp (cell_integrable (-1) upper state)
  apply (first.sub second).congr
  filter_upwards [] with a
  exact (crossWindow_action a state).symm

/-- The original finite integer inventory and the entire 0..N source normalization. -/
def crossSource (N:ℕ) (state:Hq) : Hq :=
  (∑ n∈Finset.Ico 1 N,crossWindow n state)-∫a:ℝ in Ioc 0 (N:ℝ),crossWindow a state

theorem crossSource_action (N:ℕ) (state:Hq) :
    crossSource N state=Rq (DualSource.source N (E (T state)))-
      T (Rq (FiniteForcing.source N (E state))) := by
  unfold crossSource
  simp_rw [crossWindow_action]
  have first:=cell_integrable 1 (N:ℝ) (T state)
  have second:=(T).integrable_comp (cell_integrable (-1) (N:ℝ) state)
  simp only [reverseCell,forwardCell]
  rw [integral_sub first second,Finset.sum_sub_distrib]
  simp only [DualSource.source,FiniteForcing.source,ContinuousChannels.normalization,map_sub,map_sum]
  rw [
    ←(Rq).integral_comp_comm (ContinuousChannels.channel_integrable 1 N (E (T state))),
    ←(Rq).integral_comp_comm (ContinuousChannels.channel_integrable (-1) N (E state)),
    ←(T).integral_comp_comm (cell_integrable (-1) N state)]
  simp only [Channels.sourceChannel,ContinuousChannels.channel,neg_one_mul]
  module

/-- This is the original finite Cq response, distinct from the physical unit4 source. -/
def countedUnit (N:ℕ) : M := Q (Rq (DualSource.source N (E (intervalConstant q))))

def oppositeSource (N:ℕ) (state:M) : M :=
  Q (crossSource N (state:Hq))-
    (2*inner ℂ sinc state) • countedUnit N+
    (2*inner ℂ (countedUnit N) state) • sinc

open private fourier_mean zeroMean_pair pair_zeroMean from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CenteredCountingDual
private theorem forward_mean (N:ℕ) (state:M) :
    burnolQuarterMeanCoefficient (Rq (FiniteForcing.source N (E (state:Hq))))=
      2*inner ℂ (countedUnit N) state := by
  have paired:=CountingDual.source_pairing N (E (state:Hq)) (E (intervalConstant q))
  have starred:=congrArg (star:ℂ→ℂ) paired
  simp only [star_def,inner_conj_symm] at starred
  have lhs:=(ContinuousLinearMap.adjoint_inner_left Rq (FiniteForcing.source N (E (state:Hq))) (intervalConstant q)).symm
  have rhs:=(ContinuousLinearMap.adjoint_inner_right Rq (DualSource.source N (E (intervalConstant q))) (state:Hq)).symm
  change inner ℂ (intervalConstant q) (Rq (FiniteForcing.source N (E (state:Hq))))=
    inner ℂ (E (intervalConstant q)) (FiniteForcing.source N (E (state:Hq))) at lhs
  change inner ℂ (Rq (DualSource.source N (E (intervalConstant q)))) (state:Hq)=
    inner ℂ (DualSource.source N (E (intervalConstant q))) (E (state:Hq)) at rhs
  rw [countedUnit,zeroMean_pair]
  change burnolQuarterMeanCoefficient (Rq (FiniteForcing.source N (E (state:Hq))))=
    2*inner ℂ (Rq (DualSource.source N (E (intervalConstant q)))) (state:Hq)
  have normal : burnolQuarterMeanCoefficient (Rq (FiniteForcing.source N (E (state:Hq))))=
      2*inner ℂ (intervalConstant q) (Rq (FiniteForcing.source N (E (state:Hq)))) := by
    unfold burnolQuarterMeanCoefficient
    rw [Complex.ofReal_pow,burnolIntervalConstant_norm_sq (by norm_num:(0:ℝ)<q)]
    norm_num
    ring
  rw [normal,lhs,starred,←rhs]

/-- The full opposite commutator is generated by the explicit crossing source and both centering ranks. -/
theorem oppositeSource_action (N:ℕ) (state:M)
    (even:reflectRestricted q (state:Hq)=state) :
    oppositeSource N state=CenteredCountingDual.reverse N (S state)-S (CenteredCountingDual.forward N state) := by
  have firstSplit : CenteredCountingDual.reverse N (S state)=
      Q (Rq (DualSource.source N (E (T (state:Hq)))))-
        burnolQuarterMeanCoefficient (T (state:Hq)) • countedUnit N := by
    rw [CenteredCountingDual.reverse,burnolMeanZeroTruncatedFourier_coe,
      burnolMeanZeroProjection_eq_sub_constant]
    simp only [map_sub,map_smul,CountingDual.dual_eq_adjoint,countedUnit]
  have secondSplit : S (CenteredCountingDual.forward N state)=
      Q (T (Rq (FiniteForcing.source N (E (state:Hq)))))-
        burnolQuarterMeanCoefficient (Rq (FiniteForcing.source N (E (state:Hq)))) • sinc := by
    change Q (T (burnolQuarterMeanZeroProjection (Rq (FiniteForcing.source N (E (state:Hq))))))=_
    rw [burnolMeanZeroProjection_eq_sub_constant,map_sub,map_smul,map_sub,map_smul]
    rfl
  rw [firstSplit,secondSplit,fourier_mean state even,forward_mean N state,
    oppositeSource,crossSource_action,map_sub]
  module

end OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
