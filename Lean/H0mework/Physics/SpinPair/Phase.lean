import H0mework.Physics.SpinPair.Parameters
import H0mework.Physics.Holonomic.HolonomicField
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open scoped ContDiff

noncomputable section

def phase (rate : ℝ) (point : BasePoint) : ℂ :=
  Complex.exp ((point 0 : ℂ) * ((rate : ℂ) * Complex.I))

def upperPhase : BasePoint → ℂ := phase frequency
def lowerPhase : BasePoint → ℂ := phase (-frequency)
def upperDualPhase (point : BasePoint) : ℂ := (spinScale : ℂ) * upperPhase point
def lowerDualPhase (point : BasePoint) : ℂ := (spinScale : ℂ) * lowerPhase point

theorem phase_smooth (rate : ℝ) : ContDiff ℝ ∞ (phase rate) := by
  have coordinate : ContDiff ℝ ∞ (fun point : BasePoint => (point 0 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (EuclideanSpace.proj (0 : Fin 4) : BasePoint →L[ℝ] ℝ).contDiff
  exact (coordinate.mul contDiff_const).cexp

theorem phase_zero (rate : ℝ) : phase rate 0 = 1 := by simp [phase]

theorem phase_opposite (rate : ℝ) (point : BasePoint) :
    phase rate point * phase (-rate) point = 1 := by
  unfold phase
  rw [← Complex.exp_add]
  simp

theorem phase_hasFDerivAt (rate : ℝ) (point : BasePoint) :
    HasFDerivAt (phase rate)
      ((EuclideanSpace.proj (0 : Fin 4) : BasePoint →L[ℝ] ℝ).smulRight
        (phase rate point * ((rate : ℂ) * Complex.I))) point := by
  have scalar : HasDerivAt
      (fun time : ℝ => Complex.exp ((time : ℂ) * ((rate : ℂ) * Complex.I)))
      (phase rate point * ((rate : ℂ) * Complex.I)) (point 0) := by
    simpa [phase] using
      (Complex.ofRealCLM.hasDerivAt.mul_const ((rate : ℂ) * Complex.I)).cexp
  have composed := scalar.hasFDerivAt.comp point
    (EuclideanSpace.proj (0 : Fin 4) : BasePoint →L[ℝ] ℝ).hasFDerivAt
  convert composed using 1 <;> rfl

theorem phase_directionalDerivative
    (rate : ℝ) (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative (phase rate) point direction =
      if direction = 0 then phase rate point * ((rate : ℂ) * Complex.I) else 0 := by
  unfold fieldDirectionalDerivative
  rw [(phase_hasFDerivAt rate point).fderiv]
  change (coordinateDirection direction) 0 •
    (phase rate point * ((rate : ℂ) * Complex.I)) = _
  by_cases same : direction = 0
  · subst direction
    simp [coordinateDirection]
  · simp [coordinateDirection, Ne.symm same, same]

theorem upper_lower_product (point : BasePoint) :
    upperPhase point * lowerPhase point = 1 := phase_opposite frequency point

theorem upperDual_lower_product (point : BasePoint) :
    upperDualPhase point * lowerPhase point = (spinScale : ℂ) := by
  rw [upperDualPhase, mul_assoc, upper_lower_product, mul_one]

theorem lowerDual_upper_product (point : BasePoint) :
    lowerDualPhase point * upperPhase point = (spinScale : ℂ) := by
  rw [lowerDualPhase, mul_assoc, mul_comm (lowerPhase point), upper_lower_product, mul_one]

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
