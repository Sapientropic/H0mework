import H0mework.NavierStokes.Heat.Work

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.HeatCalculus

open Matrix
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger

noncomputable section

private theorem velocity_add (p : IntegerWavevector) (a b : ComplexCoordinateVector) :
    biotSavartVelocityCoefficient p (a + b) =
      biotSavartVelocityCoefficient p a + biotSavartVelocityCoefficient p b :=
  (biotSavartVelocityCLM p).map_add a b

theorem pair_add_left (p q : IntegerWavevector) (a b c : ComplexCoordinateVector) :
    HeatWork.pair p q (a + b) c = HeatWork.pair p q a c + HeatWork.pair p q b c := by
  simp only [HeatWork.pair, ReferencePair.stretching, ReferencePair.transport,
    velocity_add, dotProduct_add]
  module

theorem pair_add_right (p q : IntegerWavevector) (a b c : ComplexCoordinateVector) :
    HeatWork.pair p q a (b + c) = HeatWork.pair p q a b + HeatWork.pair p q a c := by
  simp only [HeatWork.pair, ReferencePair.stretching, ReferencePair.transport, velocity_add]
  module

theorem inner_comm (a b : ComplexCoordinateVector) :
    complexCoordinateRealInner a b = complexCoordinateRealInner b a := by
  unfold complexCoordinateRealInner
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem inner_add_left (a b c : ComplexCoordinateVector) :
    complexCoordinateRealInner (a + b) c =
      complexCoordinateRealInner a c + complexCoordinateRealInner b c := by
  rw [inner_comm, complexCoordinateRealInner_add_right]
  rw [inner_comm c a, inner_comm c b]

private theorem inner_smul_left (s : Real) (a b : ComplexCoordinateVector) :
    complexCoordinateRealInner (s • a) b = s • complexCoordinateRealInner a b := by
  rw [inner_comm, complexCoordinateRealInner_real_smul_right, inner_comm b a]
  rfl

theorem work_add_output (p q : IntegerWavevector) (a b l r : ComplexCoordinateVector) :
    HeatWork.work p q (a + b) l r = HeatWork.work p q a l r + HeatWork.work p q b l r :=
  inner_add_left a b _

theorem work_add_left (p q : IntegerWavevector) (out a b r : ComplexCoordinateVector) :
    HeatWork.work p q out (a + b) r = HeatWork.work p q out a r + HeatWork.work p q out b r := by
  simp only [HeatWork.work, pair_add_left, complexCoordinateRealInner_add_right]

theorem work_add_right (p q : IntegerWavevector) (out l a b : ComplexCoordinateVector) :
    HeatWork.work p q out l (a + b) = HeatWork.work p q out l a + HeatWork.work p q out l b := by
  simp only [HeatWork.work, pair_add_right, complexCoordinateRealInner_add_right]

def pairCLM (p q : IntegerWavevector) :
    ComplexCoordinateVector →L[Real] ComplexCoordinateVector →L[Real] ComplexCoordinateVector :=
  ((LinearMap.toContinuousLinearMap).toLinearMap.comp
    (LinearMap.mk₂ Real (HeatWork.pair p q) (pair_add_left p q)
      (HeatWork.pair_smul_left p q) (pair_add_right p q) (HeatWork.pair_smul_right p q))).toContinuousLinearMap

@[simp] theorem pairCLM_apply (p q : IntegerWavevector) (a b : ComplexCoordinateVector) :
    pairCLM p q a b = HeatWork.pair p q a b := rfl

def innerCLM : ComplexCoordinateVector →L[Real] ComplexCoordinateVector →L[Real] Real :=
  ((LinearMap.toContinuousLinearMap).toLinearMap.comp
    (LinearMap.mk₂ Real complexCoordinateRealInner inner_add_left inner_smul_left
      complexCoordinateRealInner_add_right (fun s a b =>
        complexCoordinateRealInner_real_smul_right a b s))).toContinuousLinearMap

@[simp] theorem innerCLM_apply (a b : ComplexCoordinateVector) :
    innerCLM a b = complexCoordinateRealInner a b := rfl

def frequencyCLM (q : IntegerWavevector) : ComplexCoordinateVector →L[Real] Complex :=
  let linear : ComplexCoordinateVector →ₗ[Complex] Complex :=
    { toFun := fun row => Complex.I * ((2 * Real.pi : Real) : Complex) * (complexWavevector q ⬝ᵥ row)
      map_add' := by intro a b; simp [dotProduct_add, mul_add]
      map_smul' := by intro s a; simp [dotProduct_smul]; ring }
  linear.toContinuousLinearMap.restrictScalars Real

@[simp] theorem frequencyCLM_apply (q : IntegerWavevector) (a : ComplexCoordinateVector) :
    frequencyCLM q a = Complex.I * ((2 * Real.pi : Real) : Complex) * (complexWavevector q ⬝ᵥ a) := rfl

end
end SaturationMonoid.NavierStokes.HeatCalculus
