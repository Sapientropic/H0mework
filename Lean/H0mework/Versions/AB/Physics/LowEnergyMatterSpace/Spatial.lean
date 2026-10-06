import H0mework.Physics.LowEnergyMatterSpace.Continuity
import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.Source
import H0mework.Quantum.Generator.SelfAdjoint

/-! The actual source momentum flow is transported to all of physical space by Plancherel. -/
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped InnerProductSpace LinearPMap
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
noncomputable section

local instance : LinearOrder SourceIndex :=
  LinearOrder.lift' (Fintype.equivFin SourceIndex) (Fintype.equivFin SourceIndex).injective

abbrev Position := EuclideanSpace ℝ (Fin 3)
abbrev MatterFiber := EuclideanSpace ℂ SourceIndex
abbrev MatterL2 := Lp (α := Position) MatterFiber 2 volume

def actualFourierHamiltonian (xi : Position) : SourceMatrix := fourierHamiltonian (fun j => xi j)

theorem actualFourierHamiltonian_continuous : Continuous actualFourierHamiltonian := by
  apply fourierHamiltonian_continuous.comp
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).continuous

theorem actualFourierHamiltonian_hermitian (xi : Position) :
    (actualFourierHamiltonian xi).conjTranspose=actualFourierHamiltonian xi :=
  fourierHamiltonian_hermitian _

theorem actualFourierHamiltonian_value (xi : Position) :
    actualFourierHamiltonian xi=sourceConstant+∑ j, ((2*Real.pi*xi j : ℝ) : ℂ) • sourceSpatial j := rfl

def momentumUnitary (t : ℝ) : MatterL2 ≃ₗᵢ[ℂ] MatterL2 :=
  unitary volume actualFourierHamiltonian actualFourierHamiltonian_continuous
    actualFourierHamiltonian_hermitian t

def fourier : MatterL2 ≃ₗᵢ[ℂ] MatterL2 := Lp.fourierTransformₗᵢ Position MatterFiber

def spatialUnitary (t : ℝ) : MatterL2 ≃ₗᵢ[ℂ] MatterL2 :=
  (fourier.trans (momentumUnitary t)).trans fourier.symm

theorem spatialUnitary_fourier (t : ℝ) (f : MatterL2) :
    fourier (spatialUnitary t f)=momentumUnitary t (fourier f) := by
  exact fourier.apply_symm_apply _

theorem spatialUnitary_fourier_ae (t : ℝ) (f : MatterL2) :
    fourier (spatialUnitary t f)=ᵐ[volume] fun xi =>
      Fermion.timeEvolution (sourceHamiltonian (fun j => 2*Real.pi*xi j)) t (fourier f xi) := by
  rw [spatialUnitary_fourier]
  exact applyFlow_ae volume actualFourierHamiltonian actualFourierHamiltonian_continuous
    actualFourierHamiltonian_hermitian t (fourier f)

theorem spatialUnitary_zero (f : MatterL2) : spatialUnitary 0 f=f := by
  apply fourier.injective
  rw [spatialUnitary_fourier]
  exact flow_zero volume actualFourierHamiltonian actualFourierHamiltonian_continuous
    actualFourierHamiltonian_hermitian (fourier f)

theorem spatialUnitary_add (s t : ℝ) (f : MatterL2) :
    spatialUnitary (s+t) f=spatialUnitary s (spatialUnitary t f) := by
  apply fourier.injective
  rw [spatialUnitary_fourier,spatialUnitary_fourier,spatialUnitary_fourier]
  exact flow_add volume actualFourierHamiltonian actualFourierHamiltonian_continuous
    actualFourierHamiltonian_hermitian s t (fourier f)

def spatialAction : Multiplicative ℝ →* (MatterL2 ≃ₗᵢ[ℂ] MatterL2) where
  toFun t := spatialUnitary t.toAdd
  map_one' := by apply LinearIsometryEquiv.ext; intro f; exact spatialUnitary_zero f
  map_mul' s t := by apply LinearIsometryEquiv.ext; intro f; exact spatialUnitary_add s.toAdd t.toAdd f

theorem spatialUnitary_norm (t : ℝ) (f : MatterL2) : ‖spatialUnitary t f‖=‖f‖ :=
  (spatialUnitary t).norm_map f

theorem spatialUnitary_stronglyContinuous (f : MatterL2) :
    Continuous (fun t => spatialUnitary t f) :=
  fourier.symm.continuous.comp
    (flow_stronglyContinuous volume actualFourierHamiltonian actualFourierHamiltonian_continuous
      actualFourierHamiltonian_hermitian (fourier f))

theorem spatialAction_continuous (f : MatterL2) :
    Continuous (Quantum.Generator.orbit spatialAction f) := spatialUnitary_stronglyContinuous f

def spatialHamiltonian : MatterL2 →ₗ.[ℂ] MatterL2 := Quantum.Generator.hamiltonianOperator spatialAction

theorem spatialHamiltonian_selfAdjoint : IsSelfAdjoint spatialHamiltonian :=
  Quantum.Generator.hamiltonianOperator_selfAdjoint spatialAction spatialAction_continuous

theorem spatialHamiltonian_closed : spatialHamiltonian.IsClosed :=
  Quantum.Generator.hamiltonianOperator_closed spatialAction spatialAction_continuous

theorem spatialHamiltonian_domain_dense : Dense (Quantum.Generator.domain spatialAction : Set MatterL2) :=
  Quantum.Generator.domain_dense spatialAction spatialAction_continuous

theorem spatial_domain_derivative (f : Quantum.Generator.domain spatialAction) (t : ℝ) :
    HasDerivAt (fun s => spatialUnitary s (f : MatterL2))
      (spatialUnitary t (Quantum.Generator.generator spatialAction f)) t :=
  Quantum.Generator.orbit_hasDerivAt spatialAction f t

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
