import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationSquareTripleBound

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

def squareWeakIntegrand (g f : 𝓢(PhysicalMomentum,ℂ)) (xy : PhysicalMomentum × PhysicalMomentum) : ℂ :=
  conj (g xy.1)*actualProductKernel xy.1 xy.2*f xy.2

theorem squareIntegrand_integral (g f : 𝓢(PhysicalMomentum,ℂ))
    (xy : PhysicalMomentum × PhysicalMomentum) :
    (∫ nu : PhysicalMomentum,squareIntegrand g f (xy,nu))=squareWeakIntegrand g f xy := by
  simp only [squareIntegrand,squareWeakIntegrand,actualProductKernel]
  rw [integral_mul_const,integral_const_mul]

theorem squareWeakIntegrand_integrable (g f : 𝓢(PhysicalMomentum,ℂ)) :
    Integrable (squareWeakIntegrand g f) (volume.prod volume) := by
  have integral := (squareIntegrand_integrable g f).integral_prod_left
  have same : (fun xy : PhysicalMomentum × PhysicalMomentum =>
      ∫ nu : PhysicalMomentum,squareIntegrand g f (xy,nu))=squareWeakIntegrand g f :=
    funext (squareIntegrand_integral g f)
  rw [same] at integral
  exact integral

def squareWeakForm (g f : 𝓢(PhysicalMomentum,ℂ)) : ℂ :=
  ∫ xy : PhysicalMomentum × PhysicalMomentum,squareWeakIntegrand g f xy ∂volume.prod volume

theorem squareWeakForm_triple (g f : 𝓢(PhysicalMomentum,ℂ)) :
    squareWeakForm g f=
      ∫ w : (PhysicalMomentum × PhysicalMomentum) × PhysicalMomentum,squareIntegrand g f w
        ∂(volume.prod volume).prod volume := by
  rw [squareWeakForm,integral_prod _ (squareIntegrand_integrable g f)]
  apply integral_congr_ae
  filter_upwards with xy
  exact (squareIntegrand_integral g f xy).symm

theorem originalLeftKernel_conjugate (g : 𝓢(PhysicalMomentum,ℂ)) (nu : PhysicalMomentum) :
    (∫ xi : PhysicalMomentum,conj (g xi)*weylKernel xi nu)=conj (fourierAction g nu) := by
  rw [fourierAction,←integral_conj]
  apply integral_congr_ae
  filter_upwards with xi
  rw [map_mul,weylKernel_hermitian]
  ring

theorem squareIntegrand_pair_integral (g f : 𝓢(PhysicalMomentum,ℂ)) (nu : PhysicalMomentum) :
    (∫ xy : PhysicalMomentum × PhysicalMomentum,squareIntegrand g f (xy,nu) ∂volume.prod volume)=
      conj (fourierAction g nu)*fourierAction f nu := by
  have same : (fun xy : PhysicalMomentum × PhysicalMomentum => squareIntegrand g f (xy,nu))=
      (fun xy => (conj (g xy.1)*weylKernel xy.1 nu)*(weylKernel nu xy.2*f xy.2)) := by
    funext xy
    simp only [squareIntegrand,actualProductIntegrand]
    ring
  rw [same,integral_prod_mul
    (fun xi : PhysicalMomentum => conj (g xi)*weylKernel xi nu)
    (fun eta : PhysicalMomentum => weylKernel nu eta*f eta),originalLeftKernel_conjugate]
  rfl

theorem squareWeakForm_original_pair (g f : 𝓢(PhysicalMomentum,ℂ)) :
    squareWeakForm g f=∫ nu : PhysicalMomentum,conj (fourierAction g nu)*fourierAction f nu := by
  rw [squareWeakForm_triple,integral_prod_symm _ (squareIntegrand_integrable g f)]
  apply integral_congr_ae
  filter_upwards with nu
  exact squareIntegrand_pair_integral g f nu

theorem actualWeylL2_square_pair (g f : 𝓢(PhysicalMomentum,ℂ)) :
    inner ℂ (fourierActionLp g) (fourierActionLp f)=squareWeakForm g f := by
  rw [L2.inner_def,squareWeakForm_original_pair]
  apply integral_congr_ae
  filter_upwards [fourierActionLp_readback g,fourierActionLp_readback f] with nu hg hf
  simp only [hg,hf,RCLike.inner_apply,mul_comm]

end LowEnergy.PreparationVacuumQuadraticForm
