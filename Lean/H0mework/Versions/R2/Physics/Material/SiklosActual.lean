import H0mework.Versions.R2.Physics.Material.SiklosNullMatter
import H0mework.Physics.CartanReduction.AlgebraicCartan
import H0mework.Physics.PlaneWave.GaugePotential

/-! One shared Siklos candidate generated from the exact first-assembly
source contact. Profiles remain mathematical material until the source
equations generate them. All auxiliary fields, the Cartan connection and its
reaction are written by the existing action-owned reduction. -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace SaturationMonoid.PhysicsCore.Stage9C.Material

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open Stage9C.Dynamics.PlaneWave
open Stage9C.Reduction
open StageNineCClassicalWorldAcceptance
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeJointGlobalFiveSectorClosure
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField

noncomputable section

def siklosMatterWeight (radial : ℝ) : ℝ := Real.exp (3 * radial / 2)

def siklosMaterialSeed (wave : ℝ → ℝ) : StageNineHolonomicConfiguration :=
  { firstAssemblyCartanActual with
    coframe := siklosCoframe (fun point => wave (point 2))
    scalar := fun _ => firstAssemblyCartanActual.scalar 0
    matter := fun point =>
      (siklosMatterWeight (point 2) : ℂ) • firstAssemblyCartanActual.matter 0
    conjugateMatter := fun point =>
      (siklosMatterWeight (point 2) : ℂ) • firstAssemblyCartanActual.conjugateMatter 0 }

def siklosActual (wave : ℝ → ℝ) (amplitude : ℝ → P286CoordinateCarrier) :
    StageNineHolonomicConfiguration :=
  algebraicCartanReduction positiveSmoothUnifiedSource
    (nullGaugeWrite (siklosMaterialSeed wave) amplitude)

theorem siklosActual_coframe (wave : ℝ → ℝ) (amplitude : ℝ → P286CoordinateCarrier) :
    (siklosActual wave amplitude).coframe =
      siklosCoframe (fun point => wave (point 2)) := rfl

theorem siklosActual_nondegenerate
    (wave : ℝ → ℝ) (amplitude : ℝ → P286CoordinateCarrier) :
    (siklosActual wave amplitude).Nondegenerate :=
  siklosCoframe_nondegenerate _

theorem siklosActual_scalar
    (wave : ℝ → ℝ) (amplitude : ℝ → P286CoordinateCarrier) :
    (siklosActual wave amplitude).scalar =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  funext point
  change firstAssemblyCartanActual.scalar 0 = _
  rw [firstAssemblyCartanActual_dynamicScalarSourceContact]
  exact congrFun
    StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeDynamicScalarSourceContact.positive_generatedLocalVacuumCoordinates_zero_eq_constant 0

theorem siklosActual_matter
    (wave : ℝ → ℝ) (amplitude : ℝ → P286CoordinateCarrier) (point : BasePoint) :
    (siklosActual wave amplitude).matter point =
      (siklosMatterWeight (point 2) : ℂ) • diracSpinTwoMatterProbe := by
  change (siklosMatterWeight (point 2) : ℂ) • firstAssemblyCartanActual.matter 0 = _
  have origin : firstAssemblyCartanActual.matter 0 = diracSpinTwoMatterProbe := by
    rw [firstAssemblyCartanActual_matter_eq_safeFinal]
    exact fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_matter_origin_probe
  rw [origin]

theorem siklosActual_conjugateMatter
    (wave : ℝ → ℝ) (amplitude : ℝ → P286CoordinateCarrier) (point : BasePoint) :
    (siklosActual wave amplitude).conjugateMatter point =
      (siklosMatterWeight (point 2) : ℂ) • diracSpinZeroMatterCoordinate := by
  change (siklosMatterWeight (point 2) : ℂ) • firstAssemblyCartanActual.conjugateMatter 0 = _
  have origin : firstAssemblyCartanActual.conjugateMatter 0 = diracSpinZeroMatterCoordinate := by
    rw [firstAssemblyCartanActual_conjugateMatter_eq_safeFinal]
    exact fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_conjugateMatter_origin_probe
  rw [origin]

theorem siklosActual_gaugeConnection
    (wave : ℝ → ℝ) (amplitude : ℝ → P286CoordinateCarrier)
    (point : BasePoint) (direction : LorentzianIndex) :
    (siklosActual wave amplitude).gaugeConnection point direction =
      p286CoordinateEquiv.symm
        (nullGaugeCovector direction • amplitude (point 2)) := rfl

theorem siklosActual_dynamicScalarSourceContact
    (wave : ℝ → ℝ) (amplitude : ℝ → P286CoordinateCarrier) :
    DynamicScalarSourceContactAtOrigin positiveSmoothUnifiedSource
      (siklosActual wave amplitude) :=
  firstAssemblyCartanActual_dynamicScalarSourceContact

end
end SaturationMonoid.PhysicsCore.Stage9C.Material
