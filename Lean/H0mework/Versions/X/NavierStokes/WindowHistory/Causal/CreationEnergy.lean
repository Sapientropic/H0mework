import H0mework.Versions.X.NavierStokes.WindowHistoryCreation.Half
import H0mework.Versions.X.NavierStokes.WindowHistory.Causal.Dissipation
import H0mework.Versions.X.NavierStokes.WindowHistory.Causal.ResponseNext

set_option autoImplicit false
open scoped Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCausalCreationEnergy
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowHistoryOseen (H)
open NativeWholeResolvent (wholePhysical)
open NativeWindowHistoryMeanAction (creation)
open NativeWindowHistoryMeanBlocks (bath)
open NativeWindowHistoryCausalBath (bath_continuous)
open NativeWindowHistoryCausalPassivity (creationResponse creationInput creationInput_continuous)
open NativeWindowHistorySchurWeakPairing (potential)
open NativeWindowTraceWholeHistory (gradient)
open NativeWindowHistoryCausalDissipation (gradient_continuous)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativePhysicalPairing (includeCLM)
open NativeFiniteActionResolvent (physicalSpace)
open NativeWindowHistoryAdjointSpatialHalf (moment)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
local notation "Q" => NativeWindowHistoryMeanProjection.residual
variable {nu : Viscosity}

private theorem projected_drive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P A : E →L[ℝ] E) (y f : E) (first : P (A y)=A y)
    (middle : A (P y)=A y) (last : P f=f) : P (A y+f)=A (P y)+f := by
  rw [map_add,first,middle,last]

set_option backward.isDefEq.respectTransparency false in
theorem centered (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (v : ℝ → wholePhysical) (vc : Continuous v) (a B : ℝ) (aB : a≤B)
    (b : ℝ) (inside : b∈Icc a B) :
    Q (creationResponse seed M v vc a B aB b)=creationResponse seed M v vc a B aB b := by
  let y:=creationResponse seed M v vc a B aB
  let f:=creationInput seed M v
  have fc:=creationInput_continuous seed M v vc
  have initial : Q (y a)=0 :=
    (congrArg Q (NativeWindowHistoryCausalPassivity.bathResponse_initial seed M f fc a B aB)).trans (map_zero Q)
  have evolution (t : ℝ) (ht : t∈Icc a B) :
      HasDerivWithinAt (fun s => Q (y s)) (bath seed M t (Q (y t))+f t) (Icc a B) t := by
    have raw := (Q).hasFDerivAt.comp_hasDerivWithinAt t
      (NativeWindowHistoryCausalPassivity.bathResponse_derivative seed M f fc a B aB t ht)
    exact raw.congr_deriv (projected_drive (E := H) Q (bath seed M t) (y t) (f t)
      (NativeWindowHistoryBathResolvent.residual_bath seed M t (y t))
      (NativeWindowHistoryBathResolvent.bath_residual seed M t (y t))
      (NativeWindowHistoryBathResolvent.residual_square _))
  have original := NativeWindowHistoryCausalResponseNext.response_original (E := H)
    (bath seed M) (bath_continuous seed M) f fc a B aB (fun t => Q (y t)) initial evolution
  exact (original inside).symm

theorem moment_continuous (M n : ℕ) : Continuous (moment (modes M) n) := by
  have raw := ((NativeWindowHistoryAdjointSpatialFeedback.read M
    (fun k => NativeUnheatedSexticLatticePower.radical k^n)).continuous.comp
      (includeCLM (modes M) (modes_closed M)).continuous).norm.pow 2
  apply raw.congr
  intro v
  change ‖NativeWindowHistoryAdjointSpatialFeedback.read M
    (fun k => NativeUnheatedSexticLatticePower.radical k^n) (includeCLM (modes M) (modes_closed M) v)‖^2=_
  rw [NativeWindowHistoryAdjointSpatialFeedback.read_moment,NativePhysicalPairing.restrict_include]

private theorem rescale (nu w p g : ℝ) (positive : 0<nu)
    (paid : 2*nu⁻¹*w≤(nu⁻¹)^2*p+g) : 2*w≤nu⁻¹*p+nu*g := by
  have multiplied:=mul_le_mul_of_nonneg_left paid positive.le
  have first : nu*(2*nu⁻¹*w)=2*w := by field_simp
  have last : nu*((nu⁻¹)^2*p+g)=nu⁻¹*p+nu*g := by field_simp
  rwa [first,last] at multiplied

private theorem bounded_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (v : ℝ → physicalSpace (modes M)) (vc : Continuous v) (a B : ℝ) (aB : a≤B)
    (C : ℝ) (paid : ∀t∈Icc a B,potential seed M t (v t)≤C*moment (modes M) 1 (v t))
    (b : ℝ) (inside : b∈Icc a B) :
    let w:=fun t => includeCLM (modes M) (modes_closed M) (v t)
    let wc:Continuous w:=(includeCLM (modes M) (modes_closed M)).continuous.comp vc
    let y:=creationResponse seed M w wc a B aB
    ‖y b‖^2+nu.coeff*(∫t in a..b,gradient M (y t))≤
      (nu.coeff⁻¹*C)*(∫t in a..b,moment (modes M) 1 (v t)) := by
  dsimp only
  let w:=fun t => includeCLM (modes M) (modes_closed M) (v t)
  have wc:Continuous w:=(includeCLM (modes M) (modes_closed M)).continuous.comp vc
  let y:=creationResponse seed M w wc a B aB
  let f:=creationInput seed M w
  have fc:=creationInput_continuous seed M w wc
  have derivative:=NativeWindowHistoryCausalPassivity.bathResponse_derivative seed M f fc a B aB
  have energy:=NativeWindowHistoryCausalDissipation.energy_write seed M y f a B aB
    fc.continuousOn derivative (centered seed M w wc a B aB) b inside
  have initial:y a=0:=NativeWindowHistoryCausalPassivity.bathResponse_initial seed M f fc a B aB
  rw [initial,norm_zero,zero_pow (by decide : (2:ℕ)≠0),zero_add] at energy
  have yc:ContinuousOn y (Icc a b):=fun t ht =>
    ((derivative t ⟨ht.1,ht.2.trans inside.2⟩).mono (Icc_subset_Icc le_rfl inside.2)).continuousWithinAt
  have work:IntervalIntegrable (fun t => inner ℝ (f t) (y t)) volume a b:=
    (fc.continuousOn.inner (𝕜 := ℝ) yc).intervalIntegrable_of_Icc (μ := volume) inside.1
  have moments:=((moment_continuous M 1).comp vc).intervalIntegrable (μ := volume) a b
  have gradients:=((gradient_continuous nu M).comp_continuousOn yc).intervalIntegrable_of_Icc (μ := volume) inside.1
  have point (t : ℝ) (ht : t∈Icc a b) :
      2*inner ℝ (f t) (y t)≤(nu.coeff⁻¹*C)*moment (modes M) 1 (v t)+nu.coeff*gradient M (y t) := by
    have weak:=NativeWindowHistorySchurWeakPairing.creation_young seed M t (v t) (y t) nu.coeff⁻¹
    have bound:=rescale nu.coeff _ _ _ nu.coeff_pos weak
    exact bound.trans (add_le_add
      ((mul_le_mul_of_nonneg_left (paid t ⟨ht.1,ht.2.trans inside.2⟩) (inv_nonneg.mpr nu.coeff_pos.le)).trans_eq
        (mul_assoc nu.coeff⁻¹ C (moment (modes M) 1 (v t))).symm) (le_refl _))
  have integral:=intervalIntegral.integral_mono_on inside.1 (work.const_mul 2)
    ((moments.const_mul (nu.coeff⁻¹*C)).add (gradients.const_mul nu.coeff)) point
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (moments.const_mul (nu.coeff⁻¹*C)) (gradients.const_mul nu.coeff),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at integral
  simp only [Function.comp_def] at integral
  change ‖y b‖^2+nu.coeff*(∫t in a..b,gradient M (y t))≤
    (nu.coeff⁻¹*C)*(∫t in a..b,moment (modes M) 1 (v t))
  linarith only [energy,integral]

theorem source_energy (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M (v : ℝ → physicalSpace (modes M)) (vc : Continuous v)
      (a : ℝ) (start : a∈Icc 0 horizon) (b : ℝ) (_inside : b∈Icc a horizon),
      let w:=fun t => includeCLM (modes M) (modes_closed M) (v t)
      let wc:Continuous w:=(includeCLM (modes M) (modes_closed M)).continuous.comp vc
      let y:=creationResponse seed M w wc a horizon start.2
      ‖y b‖^2+nu.coeff*(∫t in a..b,gradient M (y t))≤
        C*(∫t in a..b,moment (modes M) 1 (v t)) := by
  obtain ⟨C,C0,paid⟩:=NativeWindowHistoryCreationHalf.source_potential_bound seed horizon
  refine ⟨nu.coeff⁻¹*C,mul_nonneg (inv_nonneg.mpr nu.coeff_pos.le) C0,?_⟩
  intro M v vc a start b inside
  exact bounded_energy seed M v vc a horizon start.2 C
    (fun t ht => paid M t ⟨start.1.trans ht.1,ht.2⟩ (v t)) b inside

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCausalCreationEnergy
