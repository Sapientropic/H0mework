import H0mework.Physics.LowEnergy.Quantum.ScalarHamiltonian

/-! Independent certification of the generic source Hamiltonian consumer.

The coefficient frame `R`, real phase Hessian `K`, spacetime point and
momentum remain explicit inputs.  This audit checks the four represented
Heisenberg mouths on actual polynomial/Fock tensor states and the original
independent-`χ` scalar source readback; it does not claim that a concrete
Python Hessian or a physical Hilbert completion has already been installed.
-/
set_option autoImplicit false
open SourceScalarHamiltonian
open SourceScalarCCR
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open DiracExteriorMatterAction QuantizationCheck.Fermion
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open Stage9C.Material.SpinPair StageNineDynamicBreakingVacuum
open scoped BigOperators TensorProduct Matrix
noncomputable section
attribute [local instance] Fermion.fullIndexOrder SourceRealScalarFock.branchOrder

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

example (R : ScalarIndex → σ → ℝ)
    (K : Matrix (σ ⊕ σ) (σ ⊕ σ) ℝ)
    (symmetric : ∀ i j, K i j = K j i)
    (point : BasePoint) (k : Fin 3 → ℝ) (a : σ)
    (f : BosonSpace σ) (ψ : Fock BranchIndex) :
    represent (evolve (position a ⊗ₜ[ℂ] (1 : FermionEnd))
      (hamiltonian R K point k)) (f ⊗ₜ[ℂ] ψ) =
      represent
        ((∑ j : σ ⊕ σ, (K (Sum.inr a) j : ℂ) • phase j) ⊗ₜ[ℂ]
          (1 : FermionEnd)) (f ⊗ₜ[ℂ] ψ) := by
  exact LinearMap.congr_fun
    (congrArg represent (position_equation R K symmetric point k a))
    (f ⊗ₜ[ℂ] ψ)

example (R : ScalarIndex → σ → ℝ)
    (K : Matrix (σ ⊕ σ) (σ ⊕ σ) ℝ)
    (symmetric : ∀ i j, K i j = K j i)
    (point : BasePoint) (k : Fin 3 → ℝ) (a : σ)
    (f : BosonSpace σ) (ψ : Fock BranchIndex) :
    represent (evolve (momentum a ⊗ₜ[ℂ] (1 : FermionEnd))
      (hamiltonian R K point k)) (f ⊗ₜ[ℂ] ψ) =
      represent
        (-((∑ j : σ ⊕ σ, (K (Sum.inl a) j : ℂ) • phase j) ⊗ₜ[ℂ]
          (1 : FermionEnd)) -
          (1 : BosonEnd σ) ⊗ₜ[ℂ] projectedDensity R a)
        (f ⊗ₜ[ℂ] ψ) := by
  exact LinearMap.congr_fun
    (congrArg represent (momentum_equation R K symmetric point k a))
    (f ⊗ₜ[ℂ] ψ)

example (R : ScalarIndex → σ → ℝ)
    (K : Matrix (σ ⊕ σ) (σ ⊕ σ) ℝ)
    (point : BasePoint) (k : Fin 3 → ℝ) (i : BranchIndex)
    (f : BosonSpace σ) (ψ : Fock BranchIndex) :
    represent (evolve ((1 : BosonEnd σ) ⊗ₜ[ℂ] Fermion.annihilation i)
      (hamiltonian R K point k)) (f ⊗ₜ[ℂ] ψ) =
      represent
        ((1 : BosonEnd σ) ⊗ₜ[ℂ]
          ((-Complex.I) • Fermion.annihilationField (fullMatterMatrix point k) i) +
          ∑ a : σ, position a ⊗ₜ[ℂ]
            ((-Complex.I) • Fermion.annihilationField (projectedMatrix R a) i))
        (f ⊗ₜ[ℂ] ψ) := by
  exact LinearMap.congr_fun
    (congrArg represent (primal_equation R K point k i))
    (f ⊗ₜ[ℂ] ψ)

example (R : ScalarIndex → σ → ℝ)
    (K : Matrix (σ ⊕ σ) (σ ⊕ σ) ℝ)
    (point : BasePoint) (k : Fin 3 → ℝ) (i : BranchIndex)
    (f : BosonSpace σ) (ψ : Fock BranchIndex) :
    represent (evolve ((1 : BosonEnd σ) ⊗ₜ[ℂ] Fermion.creation i)
      (hamiltonian R K point k)) (f ⊗ₜ[ℂ] ψ) =
      represent
        ((1 : BosonEnd σ) ⊗ₜ[ℂ] (Complex.I • momentumColumn
          (fullMatterMatrix point k) i) +
          ∑ a : σ, position a ⊗ₜ[ℂ] (Complex.I • momentumColumn
            (projectedMatrix R a) i))
        (f ⊗ₜ[ℂ] ψ) := by
  exact LinearMap.congr_fun
    (congrArg represent (independent_momentum_equation R K point k i))
    (f ⊗ₜ[ℂ] ψ)

example (R : ScalarIndex → σ → ℝ) (a : σ)
    (point : BasePoint)
    (χ : Module.Dual ℂ DiracExteriorMatterCarrier)
    (ψ : DiracExteriorMatterCarrier) :
    matrixBilinear
      (SourceRealScalarFock.normalizedMomentum
        (Quantum.dualCoordinates (FullQuantum.normalizedMomentum actual point χ)))
      (SourceRealScalarFock.normalizedPrimal (Quantum.coordinates ψ))
      (projectedMatrix R a) =
      -∑ A : ScalarIndex, (R A a : ℂ) *
        (Exchange.yukawaSource (actual.coframe point) ψ χ
          (scalarCoordinateEquiv (SourceScalarFock.scalarDirection A)) : ℂ) := by
  exact projected_original_real_source R a point χ ψ

example (R : ScalarIndex → σ → ℝ)
    (point : BasePoint) (k : Fin 3 → ℝ)
    (K : Matrix (σ ⊕ σ) (σ ⊕ σ) ℝ)
    (f : BosonSpace σ) (ψ : Fock BranchIndex) :
    represent (hamiltonian R K point k)
      (f ⊗ₜ[ℂ] ψ) =
      quadratic K f ⊗ₜ[ℂ] ψ +
      f ⊗ₜ[ℂ] quantizeLinear (fullMatterMatrix point k) ψ +
      ∑ b : σ, (MvPolynomial.X b * f) ⊗ₜ[ℂ] projectedDensity R b ψ := by
  exact represented_hamiltonian_action R K point k f ψ

example (X H : JointAlgebra σ) (state : JointSpace σ) :
    represent (evolve X H) state =
      Complex.I • (represent H (represent X state) -
        represent X (represent H state)) := by
  exact represented_heisenberg X H state

#print axioms SourceScalarHamiltonian.projected_density_original
#print axioms SourceScalarHamiltonian.frame_CCR
#print axioms SourceScalarHamiltonian.interaction_original_field
#print axioms SourceScalarHamiltonian.position_equation
#print axioms SourceScalarHamiltonian.momentum_equation
#print axioms SourceScalarHamiltonian.primal_equation
#print axioms SourceScalarHamiltonian.independent_momentum_equation
#print axioms SourceScalarHamiltonian.projected_original_real_source
#print axioms SourceScalarHamiltonian.represented_hamiltonian_action
#print axioms SourceScalarHamiltonian.represented_heisenberg
