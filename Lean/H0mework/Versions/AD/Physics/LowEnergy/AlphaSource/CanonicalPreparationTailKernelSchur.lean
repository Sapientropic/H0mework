import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationTailSourceFourier
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationCompositionFamily

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumTailFourier
open PreparationVacuumWholeTail PreparationVacuumTailSupport PreparationVacuumLocalizedTail
open PreparationVacuumWeyl PreparationVacuumRemainder PreparationActualFactor
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology FourierTransform SchwartzMap RealInnerProductSpace ComplexConjugate

def tailWeylKernel (B : ℕ → Fin 5 → ArrayBound) (xi eta : PhysicalMomentum) : ℂ :=
  tailPartialFourier B (physicalMidpoint xi eta) (xi-eta)

theorem tailPartialFourier_raw100 (B : ℕ → Fin 5 → ArrayBound) (p k : PhysicalMomentum) :
    tailPartialFourier B p k=∫ z : FlatConfiguration,
      𝐞 (-flatCovector k z) • (energyTailFor B (z,p) : ℂ) ∂flatMeasure := by
  change (∫ x : PhysicalMomentum,𝐞 (-⟪x,k⟫) • (energyTailFor B (flatPosition x,p) : ℂ))=_
  simp only [actual_raw_pairing]
  exact actual_flatPosition_measure.integral_comp flatPosition.toHomeomorph.measurableEmbedding
    (fun z : FlatConfiguration=>𝐞 (-flatCovector k z) • (energyTailFor B (z,p) : ℂ))

theorem tailPartialFourier_conjugate (B : ℕ → Fin 5 → ArrayBound) (p k : PhysicalMomentum) :
    conj (tailPartialFourier B p k)=tailPartialFourier B p (-k) := by
  change conj (∫ x : PhysicalMomentum,𝐞 (-⟪x,k⟫) • (energyTailFor B (flatPosition x,p) : ℂ))=
    ∫ x : PhysicalMomentum,𝐞 (-⟪x,-k⟫) • (energyTailFor B (flatPosition x,p) : ℂ)
  rw [←integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Circle.smul_def,smul_eq_mul,map_mul,Circle.starRingEnd_addChar,
    Complex.conj_ofReal,inner_neg_right,neg_neg]

theorem tailWeylKernel_hermitian (B : ℕ → Fin 5 → ArrayBound) (xi eta : PhysicalMomentum) :
    conj (tailWeylKernel B eta xi)=tailWeylKernel B xi eta := by
  rw [tailWeylKernel,tailPartialFourier_conjugate]
  simp only [physicalMidpoint,add_comm eta xi,neg_sub]
  rfl

theorem tailPartialFourier_joint_measurable (B : ℕ → Fin 5 → ArrayBound) :
    StronglyMeasurable (fun w : PhysicalMomentum × PhysicalMomentum=>tailPartialFourier B w.1 w.2) := by
  have amplitude : Continuous
      (fun w : (PhysicalMomentum × PhysicalMomentum) × PhysicalMomentum=>
        (energyTailFor B (flatPosition w.2,w.1.1) : ℂ)) :=
    Complex.continuous_ofReal.comp ((energyTailFor_global_smooth B).continuous.comp
      ((flatPosition.continuous.comp continuous_snd).prodMk (continuous_fst.comp continuous_fst)))
  have phase : Continuous
      (fun w : (PhysicalMomentum × PhysicalMomentum) × PhysicalMomentum=>𝐞 (-⟪w.2,w.1.2⟫)) :=
    Real.continuous_fourierChar.comp ((continuous_snd.inner (continuous_snd.comp continuous_fst)).neg)
  have whole : StronglyMeasurable
      (fun w : (PhysicalMomentum × PhysicalMomentum) × PhysicalMomentum=>
        𝐞 (-⟪w.2,w.1.2⟫) • (energyTailFor B (flatPosition w.2,w.1.1) : ℂ)) :=
    (phase.smul amplitude).stronglyMeasurable
  exact whole.integral_prod_right' (ν:=(volume:Measure PhysicalMomentum))

attribute [local irreducible] tailPartialFourier energyTailFor tailWeylKernel

theorem tailWeylKernel_measurable (B : ℕ → Fin 5 → ArrayBound) :
    StronglyMeasurable (fun w : PhysicalMomentum × PhysicalMomentum=>tailWeylKernel B w.1 w.2) := by
  have physical : Continuous (fun w : PhysicalMomentum × PhysicalMomentum=>
      (physicalMidpoint w.1 w.2,w.1-w.2)) :=
    ((continuous_fst.add continuous_snd).const_smul Real.pi).prodMk (continuous_fst.sub continuous_snd)
  have actual := (tailPartialFourier_joint_measurable B).comp_measurable physical.measurable
  have same : ((fun w : PhysicalMomentum × PhysicalMomentum=>tailPartialFourier B w.1 w.2) ∘
      (fun w : PhysicalMomentum × PhysicalMomentum=>(physicalMidpoint w.1 w.2,w.1-w.2)))=
      (fun w : PhysicalMomentum × PhysicalMomentum=>tailWeylKernel B w.1 w.2) := by
    funext w
    rw [tailWeylKernel]
    rfl
  rw [same] at actual
  exact actual

theorem tailWeylKernel_decay (B : ℕ → Fin 5 → ArrayBound)
    (positive : ∀ k i n,0 ≤ B k i n) (input : UnitEnergyInputs B 102) (xi eta : PhysicalMomentum) :
    ‖tailWeylKernel B xi eta‖≤tailRapidBound B*frequencyDecay101 (xi-eta) := by
  have rapid:=tailPartialFourier_rapid_bound B positive input (physicalMidpoint xi eta) (xi-eta)
  rw [←tailWeylKernel] at rapid
  have smaller : (1+‖xi-eta‖)^101≤(1+‖xi-eta‖)^102 :=
    pow_le_pow_right₀ (by linarith [norm_nonneg (xi-eta)]) (by norm_num)
  have high:= (mul_le_mul_of_nonneg_right smaller (norm_nonneg (tailWeylKernel B xi eta))).trans rapid
  have divide : ‖tailWeylKernel B xi eta‖≤tailRapidBound B/(1+‖xi-eta‖)^101 :=
    (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using high)
  apply divide.trans_eq
  have decay : frequencyDecay101 (xi-eta)=((1+‖xi-eta‖)^101)⁻¹ := by
    unfold frequencyDecay101
    rw [show (-101:ℝ)=-(101:ℕ) by norm_num,Real.rpow_neg (by positivity),Real.rpow_natCast]
  rw [decay,div_eq_mul_inv]

def tailKernelMajorant (B : ℕ → Fin 5 → ArrayBound) (k : PhysicalMomentum) : ℝ :=
  tailRapidBound B*frequencyDecay101 k

def tailSchurBound (B : ℕ → Fin 5 → ArrayBound) : ℝ :=
  tailRapidBound B*∫ k : PhysicalMomentum,frequencyDecay101 k

theorem tailKernelMajorant_integrable (B : ℕ → Fin 5 → ArrayBound) : Integrable (tailKernelMajorant B) :=
  frequencyDecay101_integrable.const_mul _

theorem tailSchurBound_nonnegative (B : ℕ → Fin 5 → ArrayBound)
    (positive : ∀ k i n,0 ≤ B k i n) : 0 ≤ tailSchurBound B :=
  mul_nonneg (tailRapidBound_nonnegative B positive) (integral_nonneg frequencyDecay101_nonnegative)

theorem tailWeylKernel_row_integrable (B : ℕ → Fin 5 → ArrayBound)
    (positive : ∀ k i n,0 ≤ B k i n) (input : UnitEnergyInputs B 102) (xi : PhysicalMomentum) :
    Integrable (fun eta : PhysicalMomentum=>tailWeylKernel B xi eta) := by
  have actual : StronglyMeasurable (fun eta : PhysicalMomentum=>tailWeylKernel B xi eta) :=
    (tailWeylKernel_measurable B).comp_measurable (g:=fun eta : PhysicalMomentum=>(xi,eta))
      (measurable_const.prodMk measurable_id)
  apply ((tailKernelMajorant_integrable B).comp_sub_left xi).mono actual.aestronglyMeasurable
  exact Eventually.of_forall (fun eta=>(tailWeylKernel_decay B positive input xi eta).trans (le_abs_self _))

theorem tailWeylKernel_column_integrable (B : ℕ → Fin 5 → ArrayBound)
    (positive : ∀ k i n,0 ≤ B k i n) (input : UnitEnergyInputs B 102) (eta : PhysicalMomentum) :
    Integrable (fun xi : PhysicalMomentum=>tailWeylKernel B xi eta) := by
  have actual : StronglyMeasurable (fun xi : PhysicalMomentum=>tailWeylKernel B xi eta) :=
    (tailWeylKernel_measurable B).comp_measurable (g:=fun xi : PhysicalMomentum=>(xi,eta))
      (measurable_id.prodMk measurable_const)
  apply ((tailKernelMajorant_integrable B).comp_sub_right eta).mono actual.aestronglyMeasurable
  exact Eventually.of_forall (fun xi=>(tailWeylKernel_decay B positive input xi eta).trans (le_abs_self _))

theorem tailWeylKernel_row_bound (B : ℕ → Fin 5 → ArrayBound)
    (positive : ∀ k i n,0 ≤ B k i n) (input : UnitEnergyInputs B 102) (xi : PhysicalMomentum) :
    (∫ eta : PhysicalMomentum,‖tailWeylKernel B xi eta‖)≤tailSchurBound B := by
  calc
    _≤∫ eta : PhysicalMomentum,tailKernelMajorant B (xi-eta) :=
      integral_mono (tailWeylKernel_row_integrable B positive input xi).norm
        ((tailKernelMajorant_integrable B).comp_sub_left xi) (tailWeylKernel_decay B positive input xi)
    _=∫ k : PhysicalMomentum,tailKernelMajorant B k := integral_sub_left_eq_self _ volume xi
    _=tailSchurBound B := integral_const_mul _ _

theorem tailWeylKernel_column_bound (B : ℕ → Fin 5 → ArrayBound)
    (positive : ∀ k i n,0 ≤ B k i n) (input : UnitEnergyInputs B 102) (eta : PhysicalMomentum) :
    (∫ xi : PhysicalMomentum,‖tailWeylKernel B xi eta‖)≤tailSchurBound B := by
  calc
    _≤∫ xi : PhysicalMomentum,tailKernelMajorant B (xi-eta) :=
      integral_mono (tailWeylKernel_column_integrable B positive input eta).norm
        ((tailKernelMajorant_integrable B).comp_sub_right eta)
        (fun xi=>tailWeylKernel_decay B positive input xi eta)
    _=∫ k : PhysicalMomentum,tailKernelMajorant B k := integral_sub_right_eq_self _ eta
    _=tailSchurBound B := integral_const_mul _ _

end LowEnergy.PreparationVacuumTailFourier
