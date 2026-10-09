import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.Gamma
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.MovingBasis

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
open BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient
open UnifiedOrbitals
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def gammaRate (phase : Phase) (t : ℝ) : Matrix Basis Basis ℂ :=
  -Complex.I • (FiniteActuation.electronHamiltonian (FiniteActuation.electronicRate phase t)*
      FiniteContinuation.gammaPath input phase t-
    FiniteContinuation.gammaPath input phase t*
      FiniteActuation.electronHamiltonian (FiniteActuation.electronicRate phase t))

def movingKernelJet (D : Matrix Basis Basis ℂ) (left right : MultiIndex)
    (phase : Phase) (t : ℝ) (x y : Point) : ℂ :=
  ∑ i : Basis, ∑ j : Basis, Frame.registeredAOState D i j*
    (movingJet i left phase t x : ℂ)*(movingJet j right phase t y : ℂ)

def movingGamma (phase : Phase) (t : ℝ) (x y : Point) : ℂ :=
  movingKernelJet (FiniteContinuation.gammaPath input phase t) zeroJet zeroJet phase t x y

def spatialGammaRate (phase : Phase) (t : ℝ) (x y : Point) : ℂ :=
  movingKernelJet (gammaRate phase t) zeroJet zeroJet phase t x y-
    (travelRate phase t : ℂ)*
      (movingKernelJet (FiniteContinuation.gammaPath input phase t) (raise zeroJet 0) zeroJet phase t x y+
       movingKernelJet (FiniteContinuation.gammaPath input phase t) zeroJet (raise zeroJet 0) phase t x y)

theorem registered_coefficient_derivative (phase : Phase) (t : ℝ) (i j : Basis) :
    HasDerivAt (fun time => Frame.registeredAOState (FiniteContinuation.gammaPath input phase time) i j)
      (Frame.registeredAOState (gammaRate phase t) i j) t := by
  have derivative : HasDerivAt (fun time => Frame.registeredAOState (FiniteContinuation.gammaPath input phase time))
      (Frame.registeredAOState (gammaRate phase t)) t := by
    exact ((FiniteContinuation.gamma_equation input phase t).const_mul
      (Frame.complexMatrix Frame.realInverse)).mul_const (star (Frame.complexMatrix Frame.realInverse))
  exact hasDerivAt_pi.mp (hasDerivAt_pi.mp derivative i) j

theorem spatial_gamma_equation (phase : Phase) (t : ℝ) (x y : Point) :
    HasDerivAt (fun time => movingGamma phase time x y) (spatialGammaRate phase t x y) t := by
  have each (i j : Basis) : HasDerivAt (fun time =>
      Frame.registeredAOState (FiniteContinuation.gammaPath input phase time) i j*
      (movingJet i zeroJet phase time x : ℂ)*(movingJet j zeroJet phase time y : ℂ))
      (Frame.registeredAOState (gammaRate phase t) i j*
        (movingJet i zeroJet phase t x : ℂ)*(movingJet j zeroJet phase t y : ℂ)-
        (travelRate phase t : ℂ)*
          (Frame.registeredAOState (FiniteContinuation.gammaPath input phase t) i j*
            (movingJet i (raise zeroJet 0) phase t x : ℂ)*(movingJet j zeroJet phase t y : ℂ)+
           Frame.registeredAOState (FiniteContinuation.gammaPath input phase t) i j*
            (movingJet i zeroJet phase t x : ℂ)*(movingJet j (raise zeroJet 0) phase t y : ℂ))) t := by
    have hd := ((registered_coefficient_derivative phase t i j).mul
      (moving_jet_derivative i zeroJet phase t x).ofReal_comp).mul
        (moving_jet_derivative j zeroJet phase t y).ofReal_comp
    convert! hd using 1
    dsimp only [Pi.mul_apply]
    push_cast
    ring
  have total := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => each i j))
  simpa only [movingGamma,spatialGammaRate,movingKernelJet,Finset.sum_sub_distrib,
    mul_add,Finset.mul_sum,Finset.sum_add_distrib] using total

theorem moving_gamma_source (x y : Point) : movingGamma .enter 0 x y=originalKernel input.body.realized x y := by
  have start := (FiniteContinuation.source_endpoints input input_admissible (0,0)).2.2.2.1
  simp only [movingGamma,movingKernelJet,start,moving_jet_source,originalKernel,ao]

theorem moving_gamma_target (x y : Point) : movingGamma .leave duration x y=gammaKernel x y := by
  have finish := (FiniteContinuation.target_endpoints input input_admissible (0,0)).2.2.2.1
  simp only [movingGamma,movingKernelJet,finish,moving_jet_target,gammaKernel,kernelFrom,translatedAO]
  rfl

theorem moving_gamma_junctions (x y : Point) :
    movingGamma .enter duration x y=movingGamma .drive 0 x y ∧
    movingGamma .drive duration x y=movingGamma .leave 0 x y := by
  rcases FiniteContinuation.state_junctions input with ⟨_,_,_,_,_,_,a,b,_⟩
  unfold movingGamma movingKernelJet movingJet
  rw [a,b,(moving_point_junctions x).1,(moving_point_junctions x).2,
    (moving_point_junctions y).1,(moving_point_junctions y).2]
  exact ⟨rfl,rfl⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
