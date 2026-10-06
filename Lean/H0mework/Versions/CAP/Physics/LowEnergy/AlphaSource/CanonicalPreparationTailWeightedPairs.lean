import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationTailKernelSchur
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationCompositionWeightedPairs
import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumTailOperator
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationVacuumRemainder
open PreparationVacuumWeylDomain
open PreparationVacuumCompositionBounded (originalLp_square_integrable)
open PreparationVacuumFrequencyN2 CanonicalPreparationSquareCutoff MeasureTheory Filter Set
open scoped SchwartzMap ComplexConjugate FourierTransform ENNReal
open PreparationVacuumTailFourier PreparationVacuumTailSupport
abbrev ArrayBound := ℕ → ℝ
variable (B : ℕ → Fin 5 → ArrayBound)
variable (positive : ∀ k i n,0 ≤ B k i n) (input : UnitEnergyInputs B 102)
attribute [local irreducible] tailWeylKernel

def kernelWeight (xy : PhysicalMomentum × PhysicalMomentum) : ℝ :=
  ‖tailWeylKernel B xy.1 xy.2‖

theorem kernelWeight_nonnegative (xy : PhysicalMomentum × PhysicalMomentum) : 0 ≤ kernelWeight B xy :=
  norm_nonneg _

theorem kernelWeight_measurable : StronglyMeasurable (kernelWeight B) :=
  (tailWeylKernel_measurable B).norm

def leftSquare (f : FourierHilbert) (xy : PhysicalMomentum × PhysicalMomentum) : ℝ :=
  kernelWeight B xy*‖f xy.1‖^2

def rightSquare (f : FourierHilbert) (xy : PhysicalMomentum × PhysicalMomentum) : ℝ :=
  kernelWeight B xy*‖f xy.2‖^2

theorem leftSquare_nonnegative (f : FourierHilbert) (xy : PhysicalMomentum × PhysicalMomentum) :
    0 ≤ leftSquare B f xy := mul_nonneg (kernelWeight_nonnegative B _) (sq_nonneg _)

theorem rightSquare_nonnegative (f : FourierHilbert) (xy : PhysicalMomentum × PhysicalMomentum) :
    0 ≤ rightSquare B f xy := mul_nonneg (kernelWeight_nonnegative B _) (sq_nonneg _)

theorem leftSquare_measurable (f : FourierHilbert) : StronglyMeasurable (leftSquare B f) :=
  (kernelWeight_measurable B).mul (((Lp.stronglyMeasurable f).comp_measurable measurable_fst).norm.pow 2)

theorem rightSquare_measurable (f : FourierHilbert) : StronglyMeasurable (rightSquare B f) :=
  (kernelWeight_measurable B).mul (((Lp.stronglyMeasurable f).comp_measurable measurable_snd).norm.pow 2)


include positive input in
theorem leftSquare_fiber_integrable (f : FourierHilbert) (x : PhysicalMomentum) :
    Integrable (fun y : PhysicalMomentum => leftSquare B f (x,y)) := by
  change Integrable (fun y : PhysicalMomentum =>
    ‖tailWeylKernel B x y‖*‖f x‖^2)
  exact (tailWeylKernel_row_integrable B positive input x).norm.mul_const _

include positive input in
theorem leftSquare_fiber_bound (f : FourierHilbert) (x : PhysicalMomentum) :
    (∫ y : PhysicalMomentum,leftSquare B f (x,y)) ≤ tailSchurBound B*‖f x‖^2 := by
  change (∫ y : PhysicalMomentum,‖tailWeylKernel B x y‖*‖f x‖^2)≤_
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right (tailWeylKernel_row_bound B positive input x) (sq_nonneg _)

include positive input in
theorem leftSquare_integrable (f : FourierHilbert) :
    Integrable (leftSquare B f) (volume.prod volume) := by
  apply (integrable_prod_iff (leftSquare_measurable B f).aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun x => leftSquare_fiber_integrable B positive input f x
  · have same : (fun x : PhysicalMomentum => ∫ y : PhysicalMomentum,‖leftSquare B f (x,y)‖)=
        (fun x => ∫ y : PhysicalMomentum,leftSquare B f (x,y)) := by
      funext x
      apply integral_congr_ae
      filter_upwards with y
      exact Real.norm_of_nonneg (leftSquare_nonnegative B f _)
    rw [same]
    apply ((originalLp_square_integrable f).const_mul (tailSchurBound B)).mono'
      (leftSquare_measurable B f).integral_prod_right'.aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (integral_nonneg (fun y => leftSquare_nonnegative B f (x,y)))]
      exact leftSquare_fiber_bound B positive input f x

include positive input in
theorem leftSquare_integral_bound (f : FourierHilbert) :
    (∫ xy : PhysicalMomentum × PhysicalMomentum,leftSquare B f xy ∂volume.prod volume)≤
      tailSchurBound B*(∫ x : PhysicalMomentum,‖f x‖^2) := by
  rw [integral_prod _ (leftSquare_integrable B positive input f),←integral_const_mul]
  exact integral_mono (leftSquare_integrable B positive input f).integral_prod_left
    ((originalLp_square_integrable f).const_mul (tailSchurBound B))
    (leftSquare_fiber_bound B positive input f)

theorem kernelWeight_swap (xy : PhysicalMomentum × PhysicalMomentum) : kernelWeight B xy.swap=kernelWeight B xy := by
  change ‖tailWeylKernel B xy.2 xy.1‖=‖tailWeylKernel B xy.1 xy.2‖
  rw [←tailWeylKernel_hermitian B xy.1 xy.2,Complex.norm_conj]

theorem rightSquare_swap (f : FourierHilbert) : rightSquare B f=leftSquare B f ∘ Prod.swap := by
  funext xy
  change kernelWeight B xy*‖f xy.2‖^2=kernelWeight B xy.swap*‖f xy.2‖^2
  rw [kernelWeight_swap B]

include positive input in
theorem rightSquare_integrable (f : FourierHilbert) :
    Integrable (rightSquare B f) (volume.prod volume) := by
  rw [rightSquare_swap B]
  exact (leftSquare_integrable B positive input f).swap

include positive input in
theorem rightSquare_integral_bound (f : FourierHilbert) :
    (∫ xy : PhysicalMomentum × PhysicalMomentum,rightSquare B f xy ∂volume.prod volume)≤
      tailSchurBound B*(∫ x : PhysicalMomentum,‖f x‖^2) := by
  rw [rightSquare_swap B]
  change (∫ xy : PhysicalMomentum × PhysicalMomentum,leftSquare B f xy.swap
    ∂volume.prod volume)≤_
  rw [integral_prod_swap]
  exact leftSquare_integral_bound B positive input f

end LowEnergy.PreparationVacuumTailOperator
