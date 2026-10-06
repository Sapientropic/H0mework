import H0mework.Versions.AB.Physics.LowEnergy.FiniteKernel.Profiles
import H0mework.Physics.DualVariation.MotherAction

/-! The kernel coefficients are evaluated from the original field functions
and their real spacetime derivatives, never from a supplied stencil. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FiniteKernel
open DiracExteriorMatterAction DiracCliffordRepresentation
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineDynamicBreakingVacuum StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracKineticLocalSpinDensity StageNineMatterCovariantDerivativeAffine
open StageNineEnrichedProofFreeSource StageNineGlobalIntegratedAction StageNineMatterVariation
open StageNineP286GaugeConnectionVariationDensity
noncomputable section
variable {ι ρ : Type*} [Fintype ι] [Fintype ρ]

def kineticMode (C : StageNineHolonomicConfiguration) (f : BasePoint → ℂ)
    (point : BasePoint) : FullQuantum.Mother :=
  Complex.I • ∑ mu : LorentzianIndex,
    (diracMatrixMatterAction (inverseCoframeDiracGamma
      { coframe := C.coframe point, derivative := 0 } mu)).comp
      (fieldDirectionalDerivative f point mu • (1 : FullQuantum.Mother) +
        f point • FullQuantum.connection C point mu)

def yukawaMode (C : StageNineHolonomicConfiguration) (f : BasePoint → ℂ)
    (point : BasePoint) : FullQuantum.Mother :=
  f point • diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (C.scalar point))

def diracMode (C : StageNineHolonomicConfiguration) (f : BasePoint → ℂ)
    (point : BasePoint) : FullQuantum.Mother := kineticMode C f point + yukawaMode C f point

def pointKernel (C : StageNineHolonomicConfiguration) (modes : Modes ι)
    (point : BasePoint) (a b : ι) : FullQuantum.Mother :=
  (((|(C.coframe point).det| : ℝ) : ℂ) * star (modes.value a point)) •
    diracMode C (modes.value b) point

def quadratureKernel (C : StageNineHolonomicConfiguration) (modes : Modes ι)
    (points : ρ → BasePoint) (weights : ρ → ℝ) (a b : ι) : FullQuantum.Mother :=
  ∑ q, (weights q : ℂ) • pointKernel C modes (points q) a b

def kernelAction (kernel : ι → ι → FullQuantum.Mother)
    (v : ι → DiracExteriorMatterCarrier) : ι → DiracExteriorMatterCarrier :=
  fun a => ∑ b, kernel a b (v b)

theorem complete_dirac_mode (C : StageNineHolonomicConfiguration) (modes : Modes ι)
    (v : ι → DiracExteriorMatterCarrier) (chi : ι → Module.Dual ℂ DiracExteriorMatterCarrier)
    (point : BasePoint) :
    generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (configuration C modes v chi) point) =
      ∑ b, diracMode C (modes.value b) point (v b) := by
  unfold generatedContinuumDiracDualMatterVector generatedContinuumMatterKineticVector
    generatedContinuumDiracDualYukawaVector matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [toContinuumPointField, matterDerivativeFrameRelative_zeroChart,
    scalarFrameRelativeCoordinates_zeroChart, matterFrameRelative_zeroChart]
  simp only [profile_covariant]
  simp only [configuration, profile, diracMode, kineticMode, yukawaMode,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.sum_apply,
    Module.End.one_apply, map_sum, map_smul, map_add, smul_add, Finset.smul_sum,
    Finset.sum_add_distrib]
  congr 1
  congr 1 <;> exact Finset.sum_comm

theorem original_point_density (C : StageNineHolonomicConfiguration) (modes : Modes ι)
    (v : ι → DiracExteriorMatterCarrier) (chi : ι → Module.Dual ℂ DiracExteriorMatterCarrier)
    (point : BasePoint) :
    generatedDensitizedContinuumDiracDualMatterDensity positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (configuration C modes v chi) point) =
      (∑ a, chi a (kernelAction (pointKernel C modes point) v a)).re := by
  rw [generatedDensitizedContinuumDiracDualMatterDensity_eq_vectorPairing, complete_dirac_mode]
  simp only [matterDualFrameRelative_zeroChart]
  change |(C.coframe point).det| *
    ((∑ a, star (modes.value a point) • chi a) (∑ b, diracMode C (modes.value b) point (v b))).re = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    kernelAction, pointKernel, Finset.mul_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [smul_eq_mul, mul_assoc, Complex.re_ofReal_mul]

theorem original_quadrature_density (C : StageNineHolonomicConfiguration) (modes : Modes ι)
    (v : ι → DiracExteriorMatterCarrier) (chi : ι → Module.Dual ℂ DiracExteriorMatterCarrier)
    (points : ρ → BasePoint) (weights : ρ → ℝ) :
    (∑ q, weights q * generatedDensitizedContinuumDiracDualMatterDensity
      positiveSmoothUnifiedSource 0 (points q)
      (toContinuumPointField (configuration C modes v chi) (points q))) =
      (∑ a, chi a (kernelAction (quadratureKernel C modes points weights) v a)).re := by
  simp only [original_point_density, quadratureKernel, kernelAction, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul, Complex.re_sum]
  simp only [smul_eq_mul, Complex.re_ofReal_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FiniteKernel
