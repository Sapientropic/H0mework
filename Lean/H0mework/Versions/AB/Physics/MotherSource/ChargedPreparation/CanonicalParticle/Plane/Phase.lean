import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.CanonicalParticle.Evolution
import H0mework.Versions.AB.Physics.LowEnergy.FiniteKernel.Kernel

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 200000
namespace SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.CanonicalParticle.Plane
open ProofFreeRicherAnholonomicSource StageNineHolonomicField DiracExteriorMatterAction
open Stage9C.Material.SpinPair LowEnergy.FiniteKernel
open scoped ContDiff
noncomputable section

def argument (momentum : Fin 3 → ℝ) : BasePoint →L[ℝ] ℝ :=
  (∑ axis : Fin 3, momentum axis • (EuclideanSpace.proj axis.succ : BasePoint →L[ℝ] ℝ)) -
    energy momentum • (EuclideanSpace.proj (0 : Fin 4) : BasePoint →L[ℝ] ℝ)

def phase (momentum : Fin 3 → ℝ) (point : BasePoint) : ℂ :=
  Complex.exp ((argument momentum point : ℂ)*Complex.I)

theorem phase_smooth (momentum : Fin 3 → ℝ) : ContDiff ℝ ∞ (phase momentum) :=
  ((Complex.ofRealCLM.contDiff.comp (argument momentum).contDiff).mul contDiff_const).cexp

theorem phase_hasFDerivAt (momentum : Fin 3 → ℝ) (point : BasePoint) :
    HasFDerivAt (phase momentum)
      ((argument momentum).smulRight (phase momentum point*Complex.I)) point := by
  have scalar : HasDerivAt (fun time : ℝ => Complex.exp ((time : ℂ)*Complex.I))
      (phase momentum point*Complex.I) (argument momentum point) := by
    simpa [phase] using (Complex.ofRealCLM.hasDerivAt.mul_const Complex.I).cexp
  have generated := scalar.hasFDerivAt.comp point (argument momentum).hasFDerivAt
  convert generated using 1 <;> rfl

theorem argument_time (momentum : Fin 3 → ℝ) :
    argument momentum (coordinateDirection 0) = -energy momentum := by
  simp [argument, coordinateDirection]

theorem argument_space (momentum : Fin 3 → ℝ) (axis : Fin 3) :
    argument momentum (coordinateDirection axis.succ) = momentum axis := by
  simp [argument, coordinateDirection, eq_comm]

theorem phase_time (momentum : Fin 3 → ℝ) (point : BasePoint) :
    fieldDirectionalDerivative (phase momentum) point 0 =
      (-Complex.I*(energy momentum : ℂ))*phase momentum point := by
  rw [fieldDirectionalDerivative, (phase_hasFDerivAt momentum point).fderiv]
  change (argument momentum (coordinateDirection 0) : ℂ)*(phase momentum point*Complex.I) = _
  rw [argument_time]
  push_cast
  ring

theorem phase_space (momentum : Fin 3 → ℝ) (point : BasePoint) (axis : Fin 3) :
    fieldDirectionalDerivative (phase momentum) point axis.succ =
      (Complex.I*(momentum axis : ℂ))*phase momentum point := by
  rw [fieldDirectionalDerivative, (phase_hasFDerivAt momentum point).fderiv]
  change (argument momentum (coordinateDirection axis.succ) : ℂ)*(phase momentum point*Complex.I) = _
  rw [argument_space]
  ring

def modes (momentum : Fin 3 → ℝ) : Modes Unit where
  value _ := phase momentum
  smooth _ := phase_smooth momentum

theorem phase_unit (momentum : Fin 3 → ℝ) (point : BasePoint) :
    star (phase momentum point)*phase momentum point = 1 := by
  simp only [phase, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  have zero : (starRingEnd ℂ) ((argument momentum point : ℂ)*Complex.I)+
      (argument momentum point : ℂ)*Complex.I = 0 := by simp
  rw [zero, Complex.exp_zero]

end
end SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.CanonicalParticle.Plane
