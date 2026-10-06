import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationFourierReadback
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationCompositionPhysical

set_option autoImplicit false
set_option maxHeartbeats 240000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumTaylor
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationVacuumFourierJets
open PreparationVacuumRemainder CanonicalPreparationSquareCutoff
open MeasureTheory Filter
open scoped ContDiff Topology FourierTransform RealInnerProductSpace
attribute [local irreducible] partialFourier symbolSlice

def shiftedFactor (p v k : PhysicalMomentum) (t : ℝ) : ℂ := partialFourier (p+t • v) k

def shiftedFirst (p v k : PhysicalMomentum) (t : ℝ) : ℂ :=
  fderiv ℝ (fun q : PhysicalMomentum => partialFourier q k) (p+t • v) v

def shiftedSecond (p v k : PhysicalMomentum) (t : ℝ) : ℂ :=
  fderiv ℝ (fderiv ℝ (fun q : PhysicalMomentum => partialFourier q k)) (p+t • v) v v

theorem momentumCurve_hasDerivAt (p v : PhysicalMomentum) (t : ℝ) :
    HasDerivAt (fun s : ℝ => p+s • v) v t := by
  simpa only [one_smul,id_eq] using! ((hasDerivAt_id t).smul_const v).const_add p

theorem shiftedFactor_hasDerivAt (p v k : PhysicalMomentum) (t : ℝ) :
    HasDerivAt (shiftedFactor p v k) (shiftedFirst p v k t) t := by
  have outer := ((partialFourier_momentum_smooth k).differentiable (by simp) (p+t • v)).hasFDerivAt
  simpa only [shiftedFactor,shiftedFirst,Function.comp_apply] using!
    outer.comp_hasDerivAt t (momentumCurve_hasDerivAt p v t)

theorem shiftedFirst_hasDerivAt (p v k : PhysicalMomentum) (t : ℝ) :
    HasDerivAt (shiftedFirst p v k) (shiftedSecond p v k t) t := by
  have smooth : ContDiff ℝ ∞ (fderiv ℝ (fun q : PhysicalMomentum => partialFourier q k)) :=
    (partialFourier_momentum_smooth k).fderiv_right (by simp)
  have outer := (smooth.differentiable (by simp) (p+t • v)).hasFDerivAt
  have along := outer.comp_hasDerivAt t (momentumCurve_hasDerivAt p v t)
  have evaluated := (ContinuousLinearMap.apply ℝ ℂ v).hasFDerivAt.comp_hasDerivAt t along
  simpa only [shiftedFirst,shiftedSecond,Function.comp_apply,
    ContinuousLinearMap.comp_apply] using! evaluated

def compositionFirstIntegrand (t : ℝ) (z p : PhysicalMomentum)
    (w : PhysicalMomentum × PhysicalMomentum) : ℂ :=
  𝐞 ⟪z,w.1+w.2⟫ •
    (shiftedFirst p (Real.pi • w.2) w.1 t*shiftedFactor p (-Real.pi • w.1) w.2 t+
      shiftedFactor p (Real.pi • w.2) w.1 t*shiftedFirst p (-Real.pi • w.1) w.2 t)

def compositionSecondIntegrand (t : ℝ) (z p : PhysicalMomentum)
    (w : PhysicalMomentum × PhysicalMomentum) : ℂ :=
  𝐞 ⟪z,w.1+w.2⟫ •
    (shiftedSecond p (Real.pi • w.2) w.1 t*shiftedFactor p (-Real.pi • w.1) w.2 t+
      2*(shiftedFirst p (Real.pi • w.2) w.1 t*shiftedFirst p (-Real.pi • w.1) w.2 t)+
      shiftedFactor p (Real.pi • w.2) w.1 t*shiftedSecond p (-Real.pi • w.1) w.2 t)

theorem compositionIntegrand_hasDerivAt (t : ℝ) (z p : PhysicalMomentum)
    (w : PhysicalMomentum × PhysicalMomentum) :
    HasDerivAt (fun s : ℝ => compositionIntegrand s z p w) (compositionFirstIntegrand t z p w) t := by
  have product := (shiftedFactor_hasDerivAt p (Real.pi • w.2) w.1 t).mul
    (shiftedFactor_hasDerivAt p (-Real.pi • w.1) w.2 t)
  have outer := product.const_smul (𝐞 ⟪z,w.1+w.2⟫ : ℂ)
  have same : (fun s : ℝ => compositionIntegrand s z p w)=
      (fun s => 𝐞 ⟪z,w.1+w.2⟫ •
        (shiftedFactor p (Real.pi • w.2) w.1 s*shiftedFactor p (-Real.pi • w.1) w.2 s)) := by
    funext s
    simp only [compositionIntegrand,shiftedFactor,smul_neg,smul_smul,neg_smul,sub_eq_add_neg]
  rw [same]
  simpa only [compositionFirstIntegrand,Circle.smul_def] using! outer

theorem compositionFirstIntegrand_hasDerivAt (t : ℝ) (z p : PhysicalMomentum)
    (w : PhysicalMomentum × PhysicalMomentum) :
    HasDerivAt (fun s : ℝ => compositionFirstIntegrand s z p w) (compositionSecondIntegrand t z p w) t := by
  have left := (shiftedFirst_hasDerivAt p (Real.pi • w.2) w.1 t).mul
    (shiftedFactor_hasDerivAt p (-Real.pi • w.1) w.2 t)
  have right := (shiftedFactor_hasDerivAt p (Real.pi • w.2) w.1 t).mul
    (shiftedFirst_hasDerivAt p (-Real.pi • w.1) w.2 t)
  have outer := (left.add right).const_smul (𝐞 ⟪z,w.1+w.2⟫ : ℂ)
  have rearranged :
      (shiftedSecond p (Real.pi • w.2) w.1 t*shiftedFactor p (-Real.pi • w.1) w.2 t+
        shiftedFirst p (Real.pi • w.2) w.1 t*shiftedFirst p (-Real.pi • w.1) w.2 t)+
      (shiftedFirst p (Real.pi • w.2) w.1 t*shiftedFirst p (-Real.pi • w.1) w.2 t+
        shiftedFactor p (Real.pi • w.2) w.1 t*shiftedSecond p (-Real.pi • w.1) w.2 t)=
      shiftedSecond p (Real.pi • w.2) w.1 t*shiftedFactor p (-Real.pi • w.1) w.2 t+
        2*(shiftedFirst p (Real.pi • w.2) w.1 t*shiftedFirst p (-Real.pi • w.1) w.2 t)+
        shiftedFactor p (Real.pi • w.2) w.1 t*shiftedSecond p (-Real.pi • w.1) w.2 t := by ring
  simpa only [compositionFirstIntegrand,compositionSecondIntegrand,Circle.smul_def,rearranged] using! outer

end LowEnergy.PreparationVacuumTaylor
