import H0mework.Physics.LowEnergyMatterSpace.RawWeak

/-! The generated response also pays the adjoint weak equation with the source kinetic weight. -/
set_option autoImplicit false
open MeasureTheory FourierTransform
open scoped InnerProductSpace SchwartzMap Matrix
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
open Fermion Stage9C.Material.SpinPair
noncomputable section
attribute [local instance] instLinearOrderSourceIndex
attribute [local irreducible] sourceConstant sourceSpatial sourceCharge sourceHamiltonian
  hamiltonianOperator spatialDirection sourceDifferential

def chargeTest (f : 𝓢(Position,MatterFiber)) : 𝓢(Position,MatterFiber) :=
  f.postcompCLM (hamiltonianOperator sourceCharge)

private theorem operator_commute (A B : SourceMatrix) (same : A*B=B*A) (v : MatterFiber) :
    hamiltonianOperator A (hamiltonianOperator B v)=hamiltonianOperator B (hamiltonianOperator A v) := by
  have lifted := congrArg (Matrix.toEuclideanCLM (n := SourceIndex) (𝕜 := ℂ)) same
  simp only [map_mul] at lifted
  unfold hamiltonianOperator
  convert! congrArg (fun L : MatterFiber →L[ℂ] MatterFiber => L v) lifted using 1

theorem charge_differential (f : 𝓢(Position,MatterFiber)) :
    sourceDifferential (chargeTest f)=chargeTest (sourceDifferential f) := by
  apply (fourierCLE ℂ 𝓢(Position,MatterFiber)).injective
  apply SchwartzMap.ext
  intro xi
  change (𝓕 (sourceDifferential (chargeTest f))) xi=(𝓕 (chargeTest (sourceDifferential f))) xi
  rw [sourceDifferential_fourier]
  simp only [chargeTest]
  rw [constant_map_fourier_schwartz,
    constant_map_fourier_schwartz,SchwartzMap.postcompCLM_apply,SchwartzMap.postcompCLM_apply,
    sourceDifferential_fourier]
  have matrix : actualFourierHamiltonian xi*sourceCharge=sourceCharge*actualFourierHamiltonian xi :=
    (sourceHamiltonian_commutes_charge (fun j => 2*Real.pi*xi j)).symm
  exact operator_commute _ _ matrix ((𝓕 f) xi)

def spatialKineticPair (density : ℝ) (left right : MatterL2) : ℂ :=
  (density : ℂ)*inner ℂ left ((hamiltonianOperator sourceCharge).compLpL 2 volume right)

theorem spatialKineticPair_test (density : ℝ) (left : MatterL2) (test : 𝓢(Position,MatterFiber)) :
    spatialKineticPair density left (test.toLp 2)=
      (density : ℂ)*inner ℂ left ((chargeTest test).toLp 2 : MatterL2) := by
  rw [spatialKineticPair,constant_map_toLp]
  rfl

theorem duhamel_dual_weak (density : ℝ) (forcing : ℝ → MatterL2)
    (continuousForcing : Continuous forcing) (test : 𝓢(Position,MatterFiber)) (t : ℝ) :
    HasDerivAt (fun time => spatialKineticPair density (duhamel forcing time) (test.toLp 2))
      (Complex.I*spatialKineticPair density (duhamel forcing t) ((sourceDifferential test).toLp 2)+
        spatialKineticPair density (forcing t) (test.toLp 2)) t := by
  have conjugated := (duhamel_source_differential_weak forcing continuousForcing (chargeTest test) t).star
  have paired := conjugated.const_mul (density : ℂ)
  simp only [Complex.star_def,map_add,map_mul,map_neg,Complex.conj_I,neg_neg,
    inner_conj_symm,charge_differential] at paired
  simp only [spatialKineticPair_test]
  convert! paired using 1
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
