import H0mework.Versions.X.NavierStokes.MaterialStress.Source
import H0mework.Versions.X.NavierStokes.CartanAction.Jet

set_option autoImplicit false
open scoped Matrix BigOperators Matrix.Norms.Elementwise

namespace SaturationMonoid.NavierStokes.NativeCartanStress

open PhysicsCore
open MeasureTheory Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open NativeMatterCoframeStress NativeSourceCoframeStress NativeCartanCompensation
open NativePauliCoframeAction NativePhysicalFourier NativePhysicalSource NativeSourceMaterialJet

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def reactionCurrent (velocity : PhysicalSpace) : LorentzianCoframe :=
  kineticCoefficients (NativeCanonicalFluidCoframe.dual velocity) (compensatedIncrement velocity)

def current (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) : LorentzianCoframe :=
  kineticCoefficients (NativeCanonicalFluidCoframe.dual velocity) (NativeCartanSourceJet.derivative velocity jet)

def reactionStress (velocity : PhysicalSpace) : LorentzianCoframe →L[ℝ] ℝ :=
  responseCovector velocity (reactionCurrent velocity)

def stress (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) : LorentzianCoframe →L[ℝ] ℝ :=
  responseCovector velocity (current velocity jet)

/-- The full actual Cartan stress splits off a constitutive contribution generated solely by the original velocity. -/
theorem current_split (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) :
    current velocity jet = NativeSourceCoframeStress.current velocity jet + reactionCurrent velocity := by
  ext direction internal
  simp only [current, NativeSourceCoframeStress.current, reactionCurrent, kineticCoefficients,
    NativeCartanSourceJet.derivative_split, map_add, smul_add, Complex.add_re, Matrix.add_apply]

theorem stress_split (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) :
    stress velocity jet = NativeSourceCoframeStress.stress velocity jet + reactionStress velocity := by
  rw [stress, current_split, responseCovector_add]
  rfl

/-- The velocity-only reaction is an actual variation of the same matter action, with both source responses retained. -/
theorem reactionStress_hasFDerivAt (velocity : PhysicalSpace) :
    HasFDerivAt (density (reactionCurrent velocity) 0) (reactionStress velocity)
      (NativeCanonicalFluidCoframe.coframe velocity) := by
  apply density_hasFDerivAt_of_inner_zero _ _ _ (NativeCanonicalFluidCoframe.coframe_nondegenerate velocity)
  rw [add_zero, reactionCurrent, pairing_eq_kinetic]
  change (NativeCanonicalFluidCoframe.dual _ (gaugeVectorAt _ _)).re = 0
  rw [compensated_vector_zero, map_zero, Complex.zero_re]

theorem receipt_stress_hasFDerivAt {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (time : Icc (0 : ℝ) T) :
    ∀ᵐ point : Torus,
      HasFDerivAt (density (current (receiptField receipt time point) (receiptJet receipt time point)) 0)
        (stress (receiptField receipt time point) (receiptJet receipt time point))
        (NativeCanonicalFluidCoframe.coframe (receiptField receipt time point)) := by
  filter_upwards [NativeCartanSourceJet.receipt_diracDual_cartan_equations receipt time] with point equations
  have actual := (equations 0).1
  rw [NativeSourceMaterialAdjoint.source_yukawa_zero, add_zero] at actual
  apply density_hasFDerivAt_of_inner_zero _ _ _ (NativeCanonicalFluidCoframe.coframe_nondegenerate _)
  rw [add_zero, current, pairing_eq_kinetic]
  change (NativeCanonicalFluidCoframe.dual _ (gaugeVectorAt _ _)).re = 0
  rw [actual, map_zero, Complex.zero_re]

end
end SaturationMonoid.NavierStokes.NativeCartanStress
