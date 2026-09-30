import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.RawNonlinearWork
import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.JacobianForm
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.Transpose
import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.JacobianCommutator

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeRawCompletionTransfer
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent (physicalSpace pairing coefficients)
open NativeCommonAdvectorAction (curlPair)
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM include_norm restrict_include)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryCreationGeometry (transport square)
open NativeWindowHistorySchurCompletion (completion)
open NativeWindowHistorySchurSampleControl (sample)
open NativeWindowHistorySchurTranspose (transposeAction)
open NativeWindowHistorySchurAdvectorFiber (family)
open NativeWindowHistoryOseen (H)
open NativeWindowTraceWholeHistory (gradient)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
variable {nu : Viscosity}

private theorem scaled_young (n p P g : ℝ) (positive : 0<n)
    (source : 2*n⁻¹*p≤(n⁻¹)^2*P+g) : 2*p≤n⁻¹*P+n*g := by
  have paid:=mul_le_mul_of_nonneg_left source positive.le
  have left : n*(2*n⁻¹*p)=2*p := by field_simp
  have right : n*((n⁻¹)^2*P+g)=n⁻¹*P+n*g := by field_simp
  rwa [left,right] at paid

theorem finite_form (M : ℕ) (x r : physicalSpace (modes M)) (B epsilon : ℝ)
    (positive : 0<epsilon)
    (coefficient : ‖NativeWindowStressHeatSource.physical (square (modes M) x)‖≤B) :
    |2*pairing (modes M) r (transport (modes M) (modes_zero M) (modes_closed M) nu r x)|≤
      epsilon*curlPair (modes M) r.1 r.1+
        (epsilon/2)⁻¹*NativeWindowHistoryCreationForm.budget B
          ((epsilon/2)^2*(2*Real.pi)^2)*pairing (modes M) r r := by
  let n:=epsilon/2
  have n0 : 0<n:=div_pos positive (by norm_num)
  let P:=∫point : NativePhysicalFourier.Torus,square (modes M) r point*square (modes M) x point
  let p:=pairing (modes M) r (transport (modes M) (modes_zero M) (modes_closed M) nu r x)
  have skew:=NativeWindowHistoryJacobianForm.transport_skew nu M r r x
  have pos:=NativeWindowHistorySchurWeakPairing.transport_young (modes M) (modes_zero M)
    (modes_closed M) nu r x r n⁻¹
  have neg:=NativeWindowHistorySchurWeakPairing.transport_young (modes M) (modes_zero M)
    (modes_closed M) nu r x r (-n⁻¹)
  rw [skew] at pos neg
  have upper : 2*n⁻¹*p≤(n⁻¹)^2*P+curlPair (modes M) r.1 r.1 := by
    dsimp only [p,P]
    nlinarith only [neg]
  have lower : 2*n⁻¹*(-p)≤(n⁻¹)^2*P+curlPair (modes M) r.1 r.1 := by
    dsimp only [p,P]
    nlinarith only [pos]
  have absolute : |2*p|≤n⁻¹*P+n*curlPair (modes M) r.1 r.1 := by
    rw [abs_le]
    constructor
    · have paid:=scaled_young n (-p) P _ n0 lower
      linarith only [paid]
    · exact scaled_young n p P _ n0 upper
  have product:=NativeWindowHistoryCreationGeometry.square_absorption (square (modes M) x)
    (modes M) (modes_zero M) (modes_closed M) r (n^2) (sq_pos_of_pos n0)
  have power:=pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left coefficient (Real.sqrt_nonneg NativeWindowGreenTestForm.testKernel.cap)) 8
  have cap : NativeWindowHistoryCreationForm.budget
      ‖NativeWindowStressHeatSource.physical (square (modes M) x)‖ (n^2*(2*Real.pi)^2)≤
        NativeWindowHistoryCreationForm.budget B (n^2*(2*Real.pi)^2) :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_right power (by positivity))
  have reordered : P=∫point : NativePhysicalFourier.Torus,square (modes M) x point*square (modes M) r point := by
    apply integral_congr_ae
    exact Eventually.of_forall fun _ => mul_comm _ _
  have mass0 : 0≤pairing (modes M) r r:=real_inner_self_nonneg (x:=coefficients (modes M) r)
  have bounded : P≤n^2*curlPair (modes M) r.1 r.1+
      NativeWindowHistoryCreationForm.budget B (n^2*(2*Real.pi)^2)*pairing (modes M) r r := by
    rw [reordered]
    exact product.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right cap mass0))
  have scaled:=mul_le_mul_of_nonneg_left bounded (inv_nonneg.mpr n0.le)
  have coefficientRead : n⁻¹*n^2=n := by field_simp
  rw [mul_add,← mul_assoc,coefficientRead] at scaled
  change |2*p|≤epsilon*curlPair (modes M) r.1 r.1+
    n⁻¹*NativeWindowHistoryCreationForm.budget B (n^2*(2*Real.pi)^2)*pairing (modes M) r r
  dsimp only [n] at absolute scaled ⊢
  nlinarith only [absolute,scaled]

theorem source_point (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧∀M≥low,∀t∈Icc 0 horizon,
      ∀ᵐlag ∂averageMeasure,∀r : wholePhysical,
        |2*inner ℝ r (family nu M r (completion seed M t lag))|≤
          epsilon*curlPair (modes M)
            (restrictCLM (modes M) (modes_zero M) (modes_closed M) r).1
            (restrictCLM (modes M) (modes_zero M) (modes_closed M) r).1+C*‖r‖^2 := by
  obtain ⟨low,B,B0,paid⟩:=NativeWindowHistorySchurAdvectorFiber.source_square_bound seed horizon nonnegative
  let C:=(epsilon/2)⁻¹*NativeWindowHistoryCreationForm.budget B ((epsilon/2)^2*(2*Real.pi)^2)
  have C0 : 0≤C:=by unfold C NativeWindowHistoryCreationForm.budget; positivity
  refine ⟨low,C,C0,fun M above t inside => ?_⟩
  filter_upwards [paid M above t inside] with lag coefficient
  intro r
  let v:=restrictCLM (modes M) (modes_zero M) (modes_closed M) r
  have bound:=finite_form (nu:=nu) M (sample seed M t lag) v B epsilon positive coefficient
  have mass:=pow_le_pow_left₀ (norm_nonneg _) (NativeWindowHistorySchurTranspose.input_norm M r) 2
  have paired : inner ℝ r (family nu M r (completion seed M t lag))=
      pairing (modes M) v (transport (modes M) (modes_zero M) (modes_closed M) nu v (sample seed M t lag)) := by
    rw [NativeWindowHistorySchurAdvectorFiber.family_original,real_inner_comm,
      NativePhysicalPairing.include_inner (modes M) (modes_zero M),NativeResolventAdjoint.pairing_symmetric]
    rfl
  rw [paired]
  have original : pairing (modes M) v v=‖coefficients (modes M) v‖^2:=real_inner_self_eq_norm_sq (coefficients (modes M) v)
  rw [original] at bound
  exact bound.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left mass C0))

set_option backward.isDefEq.respectTransparency false in
theorem source_form (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧∀M≥low,∀t∈Icc 0 horizon,∀r : H,
      |2*inner ℝ r (transposeAction seed M t r)|≤epsilon*gradient M r+C*‖r‖^2 := by
  obtain ⟨low,C,C0,paid⟩:=source_point seed horizon nonnegative epsilon positive
  refine ⟨low,C,C0,fun M above t inside r => ?_⟩
  have mass:=((Lp.memLp r).integrable_norm_pow (by norm_num : (2:ℕ)≠0)).const_mul C
  have grad:=(NativeWindowTraceWholeHistory.gradient_integrable nu M r).const_mul epsilon
  have point : ∀ᵐlag ∂averageMeasure,‖2*inner ℝ (r lag) (family nu M (r lag) (completion seed M t lag))‖≤
      epsilon*curlPair (modes M)
        (restrictCLM (modes M) (modes_zero M) (modes_closed M) (r lag)).1
        (restrictCLM (modes M) (modes_zero M) (modes_closed M) (r lag)).1+C*‖r lag‖^2 := by
    filter_upwards [paid M above t inside] with lag source
    exact (Real.norm_eq_abs _).trans_le (source (r lag))
  have bound:=norm_integral_le_of_norm_le (grad.add mass) point
  simp only [Pi.add_apply] at bound
  rw [integral_add grad mass] at bound
  simp only [integral_const_mul] at bound
  rw [← NativeWindowTraceWholeHistory.norm_square] at bound
  have read : inner ℝ r (transposeAction seed M t r)=
      ∫lag,inner ℝ (r lag) (family nu M (r lag) (completion seed M t lag)) ∂averageMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [NativeWindowHistorySchurTranspose.transpose_ae seed M t r] with lag actual
    rw [actual]
  rw [read]
  exact (Real.norm_eq_abs _).symm.trans_le bound
end
end SaturationMonoid.NavierStokes.NativeRawCompletionTransfer
