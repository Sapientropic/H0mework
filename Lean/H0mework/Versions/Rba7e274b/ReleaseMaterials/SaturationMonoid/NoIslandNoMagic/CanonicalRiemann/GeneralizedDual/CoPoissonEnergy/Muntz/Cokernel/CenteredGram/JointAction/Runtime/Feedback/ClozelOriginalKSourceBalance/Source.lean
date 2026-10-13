import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteWardGram.Kernel
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DilationWard

import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalStrongAction.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceBalance
open Complex FourierTransform MeasureTheory Set Filter
open scoped InnerProductSpace Topology FourierTransform
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open OriginalRieszSource
attribute [local instance 1100] NormedSpace.complexToReal
namespace D
export OriginalKCombFirstFullSourceDynamics (raw)
end D
namespace Strong
export OriginalKCombCofinalStrongAction (actual_source_strong)
end Strong
namespace Prior
export OriginalKCombCofinalTwoDirection (coordinate coordinate_value originalK originalFourierK)
end Prior

-- Both contact primitives are the original finite programme's paid source fields.
def contactCorrection (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  Kernel.A coordinate • OriginalRieszFiniteSource.edgePrimitive coordinate -
    Kernel.beta coordinate • OriginalRieszFiniteSource.fourierPrimitive coordinate

def correctedField (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (burnolCompletedMellinRieszVector coordinate : BurnolL2) + contactCorrection coordinate

def regularSource (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  Kernel.A coordinate • (fourierL2 Response.wholeU - Response.wholeV) +
    Kernel.beta coordinate • (Response.wholeU - fourierL2 Response.wholeV) -
    (2 * (star coordinate.value - 1 / 2) * Kernel.beta coordinate) •
      OriginalRieszFiniteSource.fourierPrimitive coordinate

def correctedVelocity (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  -(star coordinate.value - 1 / 2) • correctedField coordinate + regularSource coordinate

theorem corrected_source_euler (coordinate : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (correctedField coordinate : TemperedDistribution ℝ ℂ) =
      (correctedVelocity coordinate : TemperedDistribution ℝ ℂ) := by
  have kernel := Kernel.original_kernel_euler coordinate
  have edge := OriginalRieszFiniteSource.edgePrimitive_euler coordinate
  have fourierEdge := OriginalRieszFiniteSource.fourierPrimitive_euler coordinate
  have kernelLaw := eq_sub_of_add_eq kernel
  have edgeLaw := eq_sub_of_add_eq edge
  have fourierLaw := eq_sub_of_add_eq fourierEdge
  change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 (correctedField coordinate)) =
    Lp.toTemperedDistributionCLM ℂ volume 2 (correctedVelocity coordinate)
  simp only [correctedField, contactCorrection, correctedVelocity, regularSource, map_add,
    map_sub, map_smul, Lp.toTemperedDistributionCLM_apply]
  rw [kernelLaw, edgeLaw, fourierLaw, Response.Psi_fourier]
  unfold Response.Psi
  have uFourier : 𝓕 (Response.wholeU : TemperedDistribution ℝ ℂ) =
      (fourierL2 Response.wholeU : TemperedDistribution ℝ ℂ) := Lp.fourier_toTemperedDistribution_eq _
  have vFourier : 𝓕 (Response.wholeV : TemperedDistribution ℝ ℂ) =
      (fourierL2 Response.wholeV : TemperedDistribution ℝ ℂ) := Lp.fourier_toTemperedDistribution_eq _
  rw [uFourier, vFourier]
  module

theorem corrected_source_strong (coordinate : BurnolCompletedMellinCoordinate) :
    HasDerivAt (fun shift : ℝ => burnolMultiplicativeDilation shift (correctedField coordinate))
      (correctedVelocity coordinate) 0 :=
  OriginalRieszFinitePairing.CoPoisson.Ward.DilationWard.strong_derivative _ _
    (corrected_source_euler coordinate)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

theorem actual_R_ordinary_strong :
    HasDerivAt (fun shift : ℝ => burnolMultiplicativeDilation shift
      (D.raw observation nontrivial half depth (ordinal + 1)))
      (-(observation.coordinate - 1 / 2) • D.raw observation nontrivial half depth (ordinal + 1) -
        (2 : ℂ) • D.raw observation nontrivial half depth ordinal) 0 := by
  have actual := Strong.actual_source_strong observation nontrivial half depth ordinal
  have scalar : HasDerivAt (fun shift : ℝ => -2 * shift) (-2 : ℝ) 0 :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id (0 : ℝ)).const_mul (-2)
  have composed := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) actual.hasFDerivAt scalar (by norm_num)
  convert! composed using 1
  · funext shift
    change burnolMultiplicativeDilation shift _ = burnolMultiplicativeDilation (-(-2 * shift) / 2) _
    rw [show -(-2 * shift) / 2 = shift by ring]
  · change _ = (-2 : ℝ) • ((observation.coordinate / 2 - 1 / 4) •
      D.raw observation nontrivial half depth (ordinal + 1) +
      D.raw observation nontrivial half depth ordinal)
    rw [← algebraMap_smul ℂ (-2 : ℝ)]
    simp only [map_neg, map_ofNat]
    module

-- The two actual strong actions generate the equation; K itself remains outside this assertion.
theorem actual_R_cross_ward :
    inner ℂ (correctedVelocity (Prior.coordinate observation nontrivial half))
      (D.raw observation nontrivial half depth (ordinal + 1)) +
    inner ℂ (correctedField (Prior.coordinate observation nontrivial half))
      (-(observation.coordinate - 1 / 2) • D.raw observation nontrivial half depth (ordinal + 1) -
        (2 : ℂ) • D.raw observation nontrivial half depth ordinal) = 0 := by
  have generated := (corrected_source_strong (Prior.coordinate observation nontrivial half)).inner ℂ
    (actual_R_ordinary_strong observation nontrivial half depth ordinal)
  simp only [burnolMultiplicativeDilation_zero] at generated
  have fixed : (fun shift : ℝ =>
      inner ℂ (burnolMultiplicativeDilation shift (correctedField (Prior.coordinate observation nontrivial half)))
        (burnolMultiplicativeDilation shift (D.raw observation nontrivial half depth (ordinal + 1)))) =
      fun _ : ℝ => inner ℂ (correctedField (Prior.coordinate observation nontrivial half))
        (D.raw observation nontrivial half depth (ordinal + 1)) := by
    funext shift
    exact (burnolMultiplicativeDilation shift).inner_map_map _ _
  rw [fixed] at generated
  simpa only [add_comm] using generated.unique
    (hasDerivAt_const (0 : ℝ) (inner ℂ (correctedField (Prior.coordinate observation nontrivial half))
      (D.raw observation nontrivial half depth (ordinal + 1))))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceBalance
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
