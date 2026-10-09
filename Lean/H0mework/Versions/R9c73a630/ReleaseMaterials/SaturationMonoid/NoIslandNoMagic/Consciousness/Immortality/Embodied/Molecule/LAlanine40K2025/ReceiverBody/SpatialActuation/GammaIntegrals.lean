import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.GammaDynamics

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
open BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient
open UnifiedOrbitals
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem moving_kernel_continuous (D : ℝ → Matrix Basis Basis ℂ) (regular : Continuous D)
    (left right : MultiIndex) (phase : Phase) (x y : Point) :
    Continuous (fun t => movingKernelJet (D t) left right phase t x y) := by
  have coefficients (i j : Basis) : Continuous (fun t => Frame.registeredAOState (D t) i j) := by
    unfold Frame.registeredAOState
    fun_prop
  unfold movingKernelJet
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact ((coefficients i j).mul (Complex.continuous_ofReal.comp
    (moving_jet_continuous i left phase x))).mul
      (Complex.continuous_ofReal.comp (moving_jet_continuous j right phase y))

theorem gamma_rate_continuous (phase : Phase) : Continuous (gammaRate phase) := by
  have state : Continuous (FiniteContinuation.gammaPath input phase) :=
    continuous_iff_continuousAt.mpr fun t => (FiniteContinuation.gamma_equation input phase t).continuousAt
  have generator : Continuous (fun t => FiniteActuation.electronHamiltonian (FiniteActuation.electronicRate phase t)) := by
    unfold FiniteActuation.electronHamiltonian FiniteActuation.electronicRate
      FiniteActuation.onRate FiniteActuation.offRate
    cases phase <;> fun_prop
  exact ((generator.mul state).sub (state.mul generator)).const_smul (-Complex.I)

theorem spatial_gamma_rate_continuous (phase : Phase) (x y : Point) :
    Continuous (fun t => spatialGammaRate phase t x y) := by
  have state : Continuous (FiniteContinuation.gammaPath input phase) :=
    continuous_iff_continuousAt.mpr fun t => (FiniteContinuation.gamma_equation input phase t).continuousAt
  have rate : Continuous (fun t => (travelRate phase t : ℂ)) := by
    unfold travelRate shiftRate FiniteActuation.progressRate
    cases phase <;> fun_prop
  exact (moving_kernel_continuous _ (gamma_rate_continuous phase) zeroJet zeroJet phase x y).sub
    (rate.mul ((moving_kernel_continuous _ state (raise zeroJet 0) zeroJet phase x y).add
      (moving_kernel_continuous _ state zeroJet (raise zeroJet 0) phase x y)))

theorem spatial_gamma_integral (phase : Phase) (x y : Point) :
    movingGamma phase duration x y-movingGamma phase 0 x y=
      ∫ t in (0 : ℝ)..duration, spatialGammaRate phase t x y :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => spatial_gamma_equation phase t x y)
    ((spatial_gamma_rate_continuous phase x y).intervalIntegrable 0 duration)).symm

theorem total_spatial_gamma_update (x y : Point) : gammaKernel x y-originalKernel input.body.realized x y=
    (∫ t in (0 : ℝ)..duration, spatialGammaRate .enter t x y)+
    (∫ t in (0 : ℝ)..duration, spatialGammaRate .drive t x y)+
    (∫ t in (0 : ℝ)..duration, spatialGammaRate .leave t x y) := by
  rw [← spatial_gamma_integral,← spatial_gamma_integral,← spatial_gamma_integral,
    moving_gamma_source,moving_gamma_target,(moving_gamma_junctions x y).1,(moving_gamma_junctions x y).2]
  ring

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
