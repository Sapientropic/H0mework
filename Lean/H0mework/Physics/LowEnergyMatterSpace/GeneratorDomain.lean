import H0mework.Physics.LowEnergyMatterSpace.GeneratorCore
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! The same orbit derivative identifies the complete multiplier domain in both directions. -/
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
open Fermion
noncomputable section
variable {ι X : Type*} [Fintype ι] [LinearOrder ι]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (H : X → Matrix ι ι ℂ)
  (continuousH : Continuous H) (hermitian : ∀ k, (H k).conjTranspose=H k)

theorem orbit_derivative_ae (f g : Space (ι := ι) μ)
    (derivative : HasDerivAt (fun t => flow μ H continuousH hermitian t f) g 0) :
    g=ᵐ[μ] fun k => (-Complex.I) • energyField μ H f k := by
  let quotient := fun t : ℝ => t⁻¹ • (flow μ H continuousH hermitian t f-f)
  have limit : Tendsto quotient (𝓝[≠] (0 : ℝ)) (𝓝 g) := by
    simpa only [zero_add,flow_zero] using derivative.tendsto_slope_zero
  obtain ⟨times,times_limit,ae_limit⟩ := (tendstoInMeasure_of_tendsto_Lp limit).exists_seq_tendsto_ae'
  have readback (index : ℕ) : quotient (times index)=ᵐ[μ] fun k =>
      (times index)⁻¹ • (timeEvolution (H k) (times index) (f k)-f k) := by
    filter_upwards [applyFlow_ae μ H continuousH hermitian (times index) f,
      Lp.coeFn_sub (flow μ H continuousH hermitian (times index) f) f,
      Lp.coeFn_smul (times index)⁻¹ (flow μ H continuousH hermitian (times index) f-f)]
      with k hflow hsub hsmul
    change ((times index)⁻¹ • (flow μ H continuousH hermitian (times index) f-f)) k=_
    rw [hsmul]
    change (times index)⁻¹ • ((flow μ H continuousH hermitian (times index) f-f) k)=_
    rw [hsub]
    change (times index)⁻¹ • (applyFlow μ H continuousH hermitian (times index) f k-f k)=_
    rw [hflow]
  filter_upwards [ae_limit,ae_all_iff.mpr readback] with k hl he
  have pointwise := ((fiber_orbit_derivative H k (f k) 0).tendsto_slope_zero).comp times_limit
  simp only [zero_add,timeEvolution_zero] at pointwise
  change Tendsto (fun index => (times index)⁻¹ •
      (timeEvolution (H k) (times index) (f k)-f k)) atTop
      (𝓝 ((-Complex.I) • energyField μ H f k)) at pointwise
  have replaced : (fun index => quotient (times index) k)=
      (fun index => (times index)⁻¹ • (timeEvolution (H k) (times index) (f k)-f k)) :=
    funext he
  rw [replaced] at hl
  exact tendsto_nhds_unique hl pointwise

theorem orbit_derivative_energy (f g : Space (ι := ι) μ)
    (derivative : HasDerivAt (fun t => flow μ H continuousH hermitian t f) g 0) :
    MemLp (energyField μ H f) 2 μ := by
  have ae := orbit_derivative_ae μ H continuousH hermitian f g derivative
  have recovered : (fun k => Complex.I • g k)=ᵐ[μ] energyField μ H f := by
    filter_upwards [ae] with k hk
    rw [hk,smul_smul]
    simp
  exact ((Lp.memLp g).const_smul Complex.I).ae_eq recovered

theorem multiplier_domain_iff (f : Space (ι := ι) μ) :
    f ∈ Quantum.Generator.domain (action μ H continuousH hermitian) ↔
      MemLp (energyField μ H f) 2 μ := by
  constructor
  · intro member
    exact orbit_derivative_energy μ H continuousH hermitian f _
      (Quantum.Generator.hasDerivAt_zero (action μ H continuousH hermitian) ⟨f,member⟩)
  · intro finiteEnergy
    exact (finite_energy_orbit_derivative μ H continuousH hermitian f finiteEnergy).differentiableAt

def multiplierDomainPoint (f : Space (ι := ι) μ) (finiteEnergy : MemLp (energyField μ H f) 2 μ) :
    Quantum.Generator.domain (action μ H continuousH hermitian) :=
  ⟨f,(multiplier_domain_iff μ H continuousH hermitian f).mpr finiteEnergy⟩

theorem multiplier_hamiltonian_value (f : Space (ι := ι) μ)
    (finiteEnergy : MemLp (energyField μ H f) 2 μ) :
    Quantum.Generator.hamiltonian (action μ H continuousH hermitian)
      (multiplierDomainPoint μ H continuousH hermitian f finiteEnergy)=energyValue μ H f finiteEnergy := by
  change Complex.I • deriv (fun t => flow μ H continuousH hermitian t f) 0=_
  rw [(finite_energy_orbit_derivative μ H continuousH hermitian f finiteEnergy).deriv,smul_smul]
  simp

attribute [local instance] instLinearOrderSourceIndex

def sourceEnergyField (f : MatterL2) : Position → MatterFiber :=
  energyField volume actualFourierHamiltonian (fourier f)

theorem source_energy_derivative (f : MatterL2) (finiteEnergy : MemLp (sourceEnergyField f) 2 volume) :
    HasDerivAt (fun t => spatialUnitary t f)
      ((-Complex.I) • fourier.symm (energyValue volume actualFourierHamiltonian (fourier f) finiteEnergy)) 0 := by
  have momentum := finite_energy_orbit_derivative volume actualFourierHamiltonian
    actualFourierHamiltonian_continuous actualFourierHamiltonian_hermitian (fourier f) finiteEnergy
  have position := (fourier.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    0 momentum
  convert! position using 1
  exact (fourier.symm.map_smul (-Complex.I) _).symm

theorem source_domain_iff (f : MatterL2) :
    f ∈ Quantum.Generator.domain spatialAction ↔ MemLp (sourceEnergyField f) 2 volume := by
  constructor
  · intro member
    have original := Quantum.Generator.hasDerivAt_zero spatialAction ⟨f,member⟩
    have momentum := (fourier.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      0 original
    change HasDerivAt (fun t => fourier (spatialUnitary t f))
      (fourier (Quantum.Generator.generator spatialAction ⟨f,member⟩)) 0 at momentum
    simp only [spatialUnitary_fourier] at momentum
    exact orbit_derivative_energy volume actualFourierHamiltonian actualFourierHamiltonian_continuous
      actualFourierHamiltonian_hermitian (fourier f) _ momentum
  · intro finiteEnergy
    exact (source_energy_derivative f finiteEnergy).differentiableAt

def sourceDomainPoint (f : MatterL2) (finiteEnergy : MemLp (sourceEnergyField f) 2 volume) :
    Quantum.Generator.domain spatialAction := ⟨f,(source_domain_iff f).mpr finiteEnergy⟩

theorem source_hamiltonian_value (f : MatterL2) (finiteEnergy : MemLp (sourceEnergyField f) 2 volume) :
    Quantum.Generator.hamiltonian spatialAction (sourceDomainPoint f finiteEnergy)=
      fourier.symm (energyValue volume actualFourierHamiltonian (fourier f) finiteEnergy) := by
  change Complex.I • deriv (fun t => spatialUnitary t f) 0=_
  rw [(source_energy_derivative f finiteEnergy).deriv,smul_smul]
  simp

theorem source_hamiltonian_fourier_ae (f : MatterL2) (finiteEnergy : MemLp (sourceEnergyField f) 2 volume) :
    fourier (Quantum.Generator.hamiltonian spatialAction (sourceDomainPoint f finiteEnergy))=ᵐ[volume]
      fun xi => hamiltonianOperator (sourceHamiltonian (fun j => 2*Real.pi*xi j)) (fourier f xi) := by
  rw [source_hamiltonian_value,fourier.apply_symm_apply]
  exact energyValue_ae volume actualFourierHamiltonian (fourier f) finiteEnergy

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
