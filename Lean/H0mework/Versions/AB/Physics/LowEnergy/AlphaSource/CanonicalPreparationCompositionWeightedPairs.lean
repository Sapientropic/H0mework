import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationFrequencyKernelBudgets
import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCompositionBounded
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationVacuumRemainder
open PreparationVacuumWeylDomain
open PreparationVacuumFrequencyN2 CanonicalPreparationSquareCutoff MeasureTheory Filter Set
open scoped SchwartzMap ComplexConjugate FourierTransform ENNReal
attribute [local irreducible] actualFullCompositionKernelDefect

def kernelWeight (xy : PhysicalMomentum × PhysicalMomentum) : ℝ :=
  ‖actualFullCompositionKernelDefect xy.1 xy.2‖

theorem kernelWeight_nonnegative (xy : PhysicalMomentum × PhysicalMomentum) : 0 ≤ kernelWeight xy :=
  norm_nonneg _

theorem kernelWeight_measurable : StronglyMeasurable kernelWeight :=
  actualFullCompositionKernelDefect_measurable.norm

def leftSquare (f : FourierHilbert) (xy : PhysicalMomentum × PhysicalMomentum) : ℝ :=
  kernelWeight xy*‖f xy.1‖^2

def rightSquare (f : FourierHilbert) (xy : PhysicalMomentum × PhysicalMomentum) : ℝ :=
  kernelWeight xy*‖f xy.2‖^2

theorem leftSquare_nonnegative (f : FourierHilbert) (xy : PhysicalMomentum × PhysicalMomentum) :
    0 ≤ leftSquare f xy := mul_nonneg (kernelWeight_nonnegative _) (sq_nonneg _)

theorem rightSquare_nonnegative (f : FourierHilbert) (xy : PhysicalMomentum × PhysicalMomentum) :
    0 ≤ rightSquare f xy := mul_nonneg (kernelWeight_nonnegative _) (sq_nonneg _)

theorem leftSquare_measurable (f : FourierHilbert) : StronglyMeasurable (leftSquare f) :=
  kernelWeight_measurable.mul (((Lp.stronglyMeasurable f).comp_measurable measurable_fst).norm.pow 2)

theorem rightSquare_measurable (f : FourierHilbert) : StronglyMeasurable (rightSquare f) :=
  kernelWeight_measurable.mul (((Lp.stronglyMeasurable f).comp_measurable measurable_snd).norm.pow 2)

theorem originalLp_square_integrable (f : FourierHilbert) :
    Integrable (fun x : PhysicalMomentum => ‖f x‖^2) :=
  (Lp.memLp f).norm.integrable_sq

theorem leftSquare_fiber_integrable (f : FourierHilbert) (x : PhysicalMomentum) :
    Integrable (fun y : PhysicalMomentum => leftSquare f (x,y)) := by
  change Integrable (fun y : PhysicalMomentum =>
    ‖actualFullCompositionKernelDefect x y‖*‖f x‖^2)
  exact (actualKernel_row_integrable x).norm.mul_const _

theorem leftSquare_fiber_bound (f : FourierHilbert) (x : PhysicalMomentum) :
    (∫ y : PhysicalMomentum,leftSquare f (x,y)) ≤ sourceCompositionSchurBound*‖f x‖^2 := by
  change (∫ y : PhysicalMomentum,‖actualFullCompositionKernelDefect x y‖*‖f x‖^2)≤_
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right (actualKernel_row_bound x) (sq_nonneg _)

theorem leftSquare_integrable (f : FourierHilbert) :
    Integrable (leftSquare f) (volume.prod volume) := by
  apply (integrable_prod_iff (leftSquare_measurable f).aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun x => leftSquare_fiber_integrable f x
  · have same : (fun x : PhysicalMomentum => ∫ y : PhysicalMomentum,‖leftSquare f (x,y)‖)=
        (fun x => ∫ y : PhysicalMomentum,leftSquare f (x,y)) := by
      funext x
      apply integral_congr_ae
      filter_upwards with y
      exact Real.norm_of_nonneg (leftSquare_nonnegative f _)
    rw [same]
    apply ((originalLp_square_integrable f).const_mul sourceCompositionSchurBound).mono'
      (leftSquare_measurable f).integral_prod_right'.aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (integral_nonneg (fun y => leftSquare_nonnegative f (x,y)))]
      exact leftSquare_fiber_bound f x

theorem leftSquare_integral_bound (f : FourierHilbert) :
    (∫ xy : PhysicalMomentum × PhysicalMomentum,leftSquare f xy ∂volume.prod volume)≤
      sourceCompositionSchurBound*(∫ x : PhysicalMomentum,‖f x‖^2) := by
  rw [integral_prod _ (leftSquare_integrable f),←integral_const_mul]
  exact integral_mono (leftSquare_integrable f).integral_prod_left
    ((originalLp_square_integrable f).const_mul sourceCompositionSchurBound)
    (leftSquare_fiber_bound f)

theorem kernelWeight_swap (xy : PhysicalMomentum × PhysicalMomentum) : kernelWeight xy.swap=kernelWeight xy := by
  change ‖actualFullCompositionKernelDefect xy.2 xy.1‖=‖actualFullCompositionKernelDefect xy.1 xy.2‖
  rw [←actualFullCompositionKernelDefect_hermitian xy.1 xy.2,Complex.norm_conj]

theorem rightSquare_swap (f : FourierHilbert) : rightSquare f=leftSquare f ∘ Prod.swap := by
  funext xy
  change kernelWeight xy*‖f xy.2‖^2=kernelWeight xy.swap*‖f xy.2‖^2
  rw [kernelWeight_swap]

theorem rightSquare_integrable (f : FourierHilbert) :
    Integrable (rightSquare f) (volume.prod volume) := by
  rw [rightSquare_swap]
  exact (leftSquare_integrable f).swap

theorem rightSquare_integral_bound (f : FourierHilbert) :
    (∫ xy : PhysicalMomentum × PhysicalMomentum,rightSquare f xy ∂volume.prod volume)≤
      sourceCompositionSchurBound*(∫ x : PhysicalMomentum,‖f x‖^2) := by
  rw [rightSquare_swap]
  change (∫ xy : PhysicalMomentum × PhysicalMomentum,leftSquare f xy.swap
    ∂volume.prod volume)≤_
  rw [integral_prod_swap]
  exact leftSquare_integral_bound f

end LowEnergy.PreparationVacuumCompositionBounded
