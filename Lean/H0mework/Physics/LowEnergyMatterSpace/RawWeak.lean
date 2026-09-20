import H0mework.Physics.LowEnergyMatterSpace.Weak
import H0mework.Physics.LowEnergyMatterSpace.GeneratorSchwartz

/-! The actual generated response satisfies the original spatial differential weak equation. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace SchwartzMap
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
noncomputable section
attribute [local instance] instLinearOrderSourceIndex
attribute [local irreducible] sourceConstant sourceSpatial sourceCharge sourceHamiltonian
  Fermion.hamiltonianOperator spatialDirection sourceDifferential

theorem duhamel_source_differential_weak (forcing : ℝ → MatterL2)
    (continuousForcing : Continuous forcing) (test : 𝓢(Position,MatterFiber)) (t : ℝ) :
    HasDerivAt (fun time => inner ℂ (test.toLp 2 : MatterL2) (duhamel forcing time))
      (-Complex.I*inner ℂ ((sourceDifferential test).toLp 2 : MatterL2) (duhamel forcing t) +
        inner ℂ (test.toLp 2 : MatterL2) (forcing t)) t := by
  have actual := duhamel_weak_schrodinger forcing continuousForcing
    (sourceDomainPoint (test.toLp 2) (schwartz_finite_energy test)) t
  rw [schwartz_hamiltonian_value] at actual
  exact actual

theorem duhamel_original_dirac_test (test : 𝓢(Position,MatterFiber)) :
    ((sourceDifferential test).toLp 2 : MatterL2) =ᵐ[volume] fun x =>
      Fermion.hamiltonianOperator diracTimeRead (occupiedSpatialDirac test x) := by
  filter_upwards [(sourceDifferential test).coeFn_toLp 2 volume] with x hx
  rw [hx,sourceDifferential_from_original_connection]

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
