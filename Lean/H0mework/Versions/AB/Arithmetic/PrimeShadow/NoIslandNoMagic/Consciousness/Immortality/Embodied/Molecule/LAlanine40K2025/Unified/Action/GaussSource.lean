import H0mework.Versions.AB.Physics.MotherSource.ChargedGauss.Euler
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.ChargedSource

/-! Original AO and D3 fields produce the matter forcing of the same U Gauss operator. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.GaussSource
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource
open StageNineHolonomicField StageNineGlobalIntegratedAction SU7MotherLieAlgebra
open StageNineP286GaugeAuxiliaryVariation StageNineFormNativeP286GaugeGeometricFirstVariation
open DiracExteriorMatterAction Stage9C.Material.SpinPair Stage9DEF
open Stage10.ChargedPreparation Stage10.TemporalGauge
open BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient
noncomputable section
attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

def preparedMatter (basis : Basis) (scale : ℝ) (point : BasePoint) : DiracExteriorMatterCarrier :=
  orbitalWeight basis scale point • preparation (Stage10.Runtime.configuration.matter point)

def preparedDual (basis : Basis) (scale : ℝ) (point : BasePoint) :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  star (orbitalWeight basis scale point) •
    (Stage10.Runtime.configuration.conjugateMatter point).comp dualPreparation

theorem prepared_current (first second : Basis) (scale : ℝ) (point : BasePoint)
    (data : P286LieBlockData) :
    preparedDual first scale point (Compatibility.currentAction 0 data (preparedMatter second scale point)) =
      star (orbitalWeight first scale point) * orbitalWeight second scale point *
        actual.conjugateMatter point
          (dualPreparation (Compatibility.currentAction 0 data (preparation (actual.matter point)))) := by
  simp only [preparedDual, preparedMatter, Stage10.Runtime.configuration_eq,
    LinearMap.smul_apply, LinearMap.comp_apply, map_smul, smul_eq_mul]
  ring

def backgroundEuler (potential : Potential) (point : BasePoint) (data : P286LieBlockData) : ℝ :=
  p286CoordinateLiePairing (p286CoordinateEquiv data)
    (holonomicFormNativeP286GaugeEulerThreeForm Stage10.Runtime.source 0
      (Stage10.TemporalGauge.configuration potential) point 3)

def preparedEuler (potential : Potential) (first second : Basis) (scale : ℝ)
    (point : BasePoint) (data : P286LieBlockData) : ℝ :=
  p286CoordinateLiePairing (p286CoordinateEquiv data)
    (holonomicFormNativeP286GaugeEulerThreeForm Stage10.Runtime.source 0
      (Stage10.ChargedGauss.withMatter potential (preparedMatter second scale) (preparedDual first scale)) point 3)

theorem prepared_euler_response (potential : Potential) (first second : Basis) (scale : ℝ)
    (point : BasePoint) (regular : ElectricDifferentiableAt potential point) (data : P286LieBlockData) :
    preparedEuler potential first second scale point data-backgroundEuler potential point data =
      (preparedDual first scale point (Compatibility.currentAction 0 data (preparedMatter second scale point))).re := by
  rw [preparedEuler, backgroundEuler,
    Stage10.ChargedGauss.gauss_projection potential _ _ point regular data,
    Stage10.TemporalGauge.gauss_projection potential point regular data]
  ring

/-- D3 contracts the matter response; the common gauge/scalar background is counted once. -/
def D3Euler (potential : Potential) (scale : ℝ) (point : BasePoint) (data : P286LieBlockData) : ℝ :=
  backgroundEuler potential point data + ∑ first : Basis, ∑ second : Basis,
    (densityMatrix first second : ℝ) *
      (preparedEuler potential first second scale point data-backgroundEuler potential point data)

theorem D3_current (scale : ℝ) (point : BasePoint) :
    (∑ first : Basis, ∑ second : Basis, (densityMatrix first second : ℝ) *
      (preparedDual first scale point (Compatibility.currentAction 0 Stage10.HyperchargeResponse.chargeDirection
        (preparedMatter second scale point))).re) =
      (ChargedSource.classicalCurrentDensity scale point).re := by
  simp only [prepared_current, ChargedSource.classicalCurrentDensity, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  simp [Complex.mul_re]

/-- The existing D3 classical-current consumer supplies the forcing in the original complete Euler equation. -/
theorem original_D3_gauss (potential : Potential) (scale : ℝ) (point : BasePoint)
    (regular : ElectricDifferentiableAt potential point) :
    D3Euler potential scale point Stage10.HyperchargeResponse.chargeDirection =
      2*lapse*p286LiePairing Stage10.HyperchargeResponse.chargeDirection (divergence potential point) -
        scalarCoordinatePairingRe (scalarCharge Stage10.HyperchargeResponse.chargeDirection)
          (scalarCharge (potential point))/lapse - 4*spinScale*sourceDensity (spatialPoint scale point) := by
  simp only [D3Euler, prepared_euler_response potential _ _ scale point regular]
  rw [D3_current, ChargedSource.classical_D3_current, backgroundEuler,
    Stage10.TemporalGauge.gauss_projection potential point regular]
  simp
  ring


theorem d3_background_counted_once (potential : Potential)
    (scale : ℝ) (point : BasePoint) (regular : ElectricDifferentiableAt potential point)
    (data : P286LieBlockData) :
    D3Euler potential scale point data = backgroundEuler potential point data +
      ∑ first : Basis, ∑ second : Basis, (densityMatrix first second : ℝ) *
        (preparedDual first scale point
          (Compatibility.currentAction 0 data (preparedMatter second scale point))).re := by
  unfold D3Euler
  congr 1
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  rw [prepared_euler_response potential first second scale point regular data]

end
end LAlanine40K2025.UnifiedAction.GaussSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
