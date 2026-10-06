import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationCompositionFourierReadback

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace LowEnergy.PreparationVacuumQuadraticForm
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationVacuumWeylDomain
open PreparationVacuumWeylOperator PreparationVacuumRemainder PreparationVacuumCompositionReadback
open PreparationActualFactor CanonicalPreparationSquareCutoff MeasureTheory Filter
open scoped FourierTransform RealInnerProductSpace ComplexConjugate SchwartzMap
attribute [local irreducible] partialFourier symbolSlice b1 weylKernel

def profileWeight (f : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : ℝ :=
  (1+‖x‖)*‖f x‖

theorem profileWeight_nonnegative (f : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    0 ≤ profileWeight f x := by unfold profileWeight; positivity

theorem profileWeight_integrable (f : 𝓢(PhysicalMomentum,ℂ)) : Integrable (profileWeight f) := by
  have moment : Integrable (fun x : PhysicalMomentum => ‖x‖*‖f x‖) := by
    simpa only [pow_one] using f.integrable_pow_mul volume 1
  have same : profileWeight f=(fun x : PhysicalMomentum => ‖f x‖)+(fun x => ‖x‖*‖f x‖) := by
    funext x
    simp only [profileWeight,Pi.add_apply,add_mul,one_mul]
  rw [same]
  exact f.integrable.norm.add moment

def profilePairMajorant (g f : 𝓢(PhysicalMomentum,ℂ)) (xy : PhysicalMomentum × PhysicalMomentum) : ℝ :=
  (2*Real.pi*sourceRapidBound)^2*(profileWeight g xy.1*profileWeight f xy.2)

theorem profilePairMajorant_nonnegative (g f : 𝓢(PhysicalMomentum,ℂ))
    (xy : PhysicalMomentum × PhysicalMomentum) : 0 ≤ profilePairMajorant g f xy := by
  unfold profilePairMajorant
  exact mul_nonneg (sq_nonneg _) (mul_nonneg (profileWeight_nonnegative g _) (profileWeight_nonnegative f _))

theorem profilePairMajorant_integrable (g f : 𝓢(PhysicalMomentum,ℂ)) :
    Integrable (profilePairMajorant g f) (volume.prod volume) :=
  ((profileWeight_integrable g).mul_prod (profileWeight_integrable f)).const_mul _

def squareMajorant (g f : 𝓢(PhysicalMomentum,ℂ))
    (w : (PhysicalMomentum × PhysicalMomentum) × PhysicalMomentum) : ℝ :=
  profilePairMajorant g f w.1*frequencyDecay101 (w.2-w.1.1)

theorem squareMajorant_nonnegative (g f : 𝓢(PhysicalMomentum,ℂ))
    (w : (PhysicalMomentum × PhysicalMomentum) × PhysicalMomentum) : 0 ≤ squareMajorant g f w :=
  mul_nonneg (profilePairMajorant_nonnegative g f _) (frequencyDecay101_nonnegative _)

theorem squareMajorant_continuous (g f : 𝓢(PhysicalMomentum,ℂ)) : Continuous (squareMajorant g f) := by
  have decay : Continuous frequencyDecay101 := by
    unfold frequencyDecay101
    exact (continuous_const.add continuous_norm).rpow_const
      (fun k => Or.inl (by positivity : (1+‖k‖ : ℝ)≠0))
  unfold squareMajorant profilePairMajorant profileWeight frequencyDecay101
  apply Continuous.mul
  · fun_prop
  · exact decay.comp (continuous_snd.sub continuous_fst.fst)

theorem squareMajorant_integrable (g f : 𝓢(PhysicalMomentum,ℂ)) :
    Integrable (squareMajorant g f) ((volume.prod volume).prod volume) := by
  apply (integrable_prod_iff (squareMajorant_continuous g f).aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall (fun xy =>
      (frequencyDecay101_integrable.comp_sub_right xy.1).const_mul (profilePairMajorant g f xy))
  · have same : (fun xy : PhysicalMomentum × PhysicalMomentum =>
        ∫ nu : PhysicalMomentum,‖squareMajorant g f (xy,nu)‖)=
        (fun xy => profilePairMajorant g f xy*(∫ k : PhysicalMomentum,frequencyDecay101 k)) := by
      funext xy
      have normEq : (fun nu : PhysicalMomentum => ‖squareMajorant g f (xy,nu)‖)=
          (fun nu => squareMajorant g f (xy,nu)) := by
        funext nu
        exact Real.norm_of_nonneg (squareMajorant_nonnegative g f _)
      rw [normEq]
      change (∫ nu : PhysicalMomentum,profilePairMajorant g f xy*frequencyDecay101 (nu-xy.1))=_
      rw [integral_const_mul,integral_sub_right_eq_self]
    rw [same]
    exact (profilePairMajorant_integrable g f).mul_const _

def squareIntegrand (g f : 𝓢(PhysicalMomentum,ℂ))
    (w : (PhysicalMomentum × PhysicalMomentum) × PhysicalMomentum) : ℂ :=
  conj (g w.1.1)*actualProductIntegrand w.1.1 w.1.2 w.2*f w.1.2

theorem squareIntegrand_measurable (g f : 𝓢(PhysicalMomentum,ℂ)) :
    StronglyMeasurable (squareIntegrand g f) := by
  have leftKernel := kernel_stronglyMeasurable.comp_measurable
    (by fun_prop : Measurable (fun w : (PhysicalMomentum × PhysicalMomentum) × PhysicalMomentum => (w.1.1,w.2)))
  have rightKernel := kernel_stronglyMeasurable.comp_measurable
    (by fun_prop : Measurable (fun w : (PhysicalMomentum × PhysicalMomentum) × PhysicalMomentum => (w.2,w.1.2)))
  exact ((Complex.continuous_conj.comp (g.continuous.comp (continuous_fst.fst))).stronglyMeasurable.mul
    (leftKernel.mul rightKernel)).mul (f.continuous.comp (continuous_fst.snd)).stronglyMeasurable

theorem squareIntegrand_norm_bound (g f : 𝓢(PhysicalMomentum,ℂ))
    (w : (PhysicalMomentum × PhysicalMomentum) × PhysicalMomentum) :
    ‖squareIntegrand g f w‖ ≤ squareMajorant g f w := by
  simp only [squareIntegrand,norm_mul,Complex.norm_conj]
  have bound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (actualProductIntegrand_norm_bound w.1.1 w.1.2 w.2)
      (norm_nonneg (g w.1.1))) (norm_nonneg (f w.1.2))
  apply bound.trans_eq
  simp only [sourceProductKernelBound,squareMajorant,profilePairMajorant,profileWeight]
  ring

theorem squareIntegrand_integrable (g f : 𝓢(PhysicalMomentum,ℂ)) :
    Integrable (squareIntegrand g f) ((volume.prod volume).prod volume) :=
  (squareMajorant_integrable g f).mono (squareIntegrand_measurable g f).aestronglyMeasurable
    (Eventually.of_forall (fun w => (squareIntegrand_norm_bound g f w).trans (le_abs_self _)))

end LowEnergy.PreparationVacuumQuadraticForm
