import H0mework.Realization.Memory.ResidualReadout
import H0mework.Computation.SelfReduction.P758

/-!
# Projection theorem

`TruthFormulaCore` proves the bottom equation:

`r = K r + (I - K) r`

and the active-collapse theorem:

`fixed <-> r = 0 <-> trace = 0 <-> energy = 0`.

This file is the next layer.  It gives stable names to the projections of the
same residual carrier:

* information = forced trace `(I - K) r`;
* memory = recollectable trace production on the residual carrier;
* SAT energy = squared obstruction residual;
* Hamiltonian energy = the same squared obstruction residual.

The concrete phase carrier section proves that, on
`SATPhaseFlowState Clause Var`, all of these read the same field:

`S.obstruction : Clause -> ℝ`.
-/

noncomputable section

namespace SaturationMonoid

namespace ResidualProjection

open AffineRelaxation
open ComplexityProjection
open EnergyLedgerProjection

universe u v

/-! ## Abstract residual carrier projections -/

/-- THEOREM 2: under active transport, residual memory is exactly nonzero
residual. -/
theorem residualMemoryPotential_iff_residual_ne_zero_of_active
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) (hactive : ResidualTransportActive keep) (r : E) :
    RecollectableMemoryPotential (residualMemoryAct keep) r ↔ r ≠ 0 := by
  have htrace_zero_iff_residual_zero :
      residualInformationReadout keep r = 0 ↔ r = 0 := by
    dsimp [residualInformationReadout]
    exact
      (residualTransport_fixed_iff_zero_trace keep hactive r).symm.trans
        (residualTransport_fixed_iff_zero_residual keep hactive r)
  exact
    (residualMemoryPotential_iff_informationTrace_nonzero keep r).trans
      (not_congr htrace_zero_iff_residual_zero)

/-- THEOREM 3: under active transport and positive-definite energy, memory is
exactly nonzero energy. -/
theorem residualMemoryPotential_iff_energy_ne_zero
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) (energy : E -> ℝ)
    (hactive : ResidualTransportActive keep)
    (henergy : ∀ r : E, energy r = 0 ↔ r = 0) (r : E) :
    RecollectableMemoryPotential (residualMemoryAct keep) r ↔
      energy r ≠ 0 := by
  have hres_energy : r = 0 ↔ energy r = 0 := (henergy r).symm
  exact
    (residualMemoryPotential_iff_residual_ne_zero_of_active
      keep hactive r).trans
      (not_congr hres_energy)

/-- THEOREM 4: fixedness is exactly the absence of residual memory. -/
theorem residualFixed_iff_not_memoryPotential
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) (hactive : ResidualTransportActive keep) (r : E) :
    ResidualTransportFixed keep r ↔
      ¬ RecollectableMemoryPotential (residualMemoryAct keep) r := by
  have hfixed_residual :
      ResidualTransportFixed keep r ↔ r = 0 :=
    residualTransport_fixed_iff_zero_residual keep hactive r
  have hmemory_residual :
      RecollectableMemoryPotential (residualMemoryAct keep) r ↔ r ≠ 0 :=
    residualMemoryPotential_iff_residual_ne_zero_of_active keep hactive r
  constructor
  · intro hfixed hmemory
    exact (hmemory_residual.mp hmemory) (hfixed_residual.mp hfixed)
  · intro hnot
    exact hfixed_residual.mpr (by
      by_contra hne
      exact hnot (hmemory_residual.mpr hne))

/-- Abstract projection certificate: information, memory, and energy are
readouts of one residual carrier. -/
structure ResidualCarrierProjectionCertificate
    (K E : Type*) [Field K] [AddCommGroup E] [Module K E] : Prop where
  truth_core :
    TruthFormulaCoreCertificate K E
  memory_iff_information_trace_nonzero :
    ∀ keep : E →ₗ[K] E, ∀ r : E,
      RecollectableMemoryPotential (residualMemoryAct keep) r ↔
        residualInformationReadout keep r ≠ 0
  active_memory_iff_residual_ne_zero :
    ∀ keep : E →ₗ[K] E,
      ResidualTransportActive keep ->
        ∀ r : E,
          RecollectableMemoryPotential (residualMemoryAct keep) r ↔
            r ≠ 0
  active_memory_iff_energy_ne_zero :
    ∀ keep : E →ₗ[K] E, ∀ energy : E -> ℝ,
      ResidualTransportActive keep ->
        (∀ r : E, energy r = 0 ↔ r = 0) ->
          ∀ r : E,
            RecollectableMemoryPotential (residualMemoryAct keep) r ↔
              energy r ≠ 0
  fixed_iff_not_memory :
    ∀ keep : E →ₗ[K] E,
      ResidualTransportActive keep ->
        ∀ r : E,
          ResidualTransportFixed keep r ↔
            ¬ RecollectableMemoryPotential (residualMemoryAct keep) r

/-- THEOREM 5: canonical abstract projection certificate. -/
theorem residualCarrierProjectionCertificate
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E] :
    ResidualCarrierProjectionCertificate K E where
  truth_core := truthFormulaCoreCertificate
  memory_iff_information_trace_nonzero := by
    intro keep r
    exact residualMemoryPotential_iff_informationTrace_nonzero keep r
  active_memory_iff_residual_ne_zero := by
    intro keep hactive r
    exact residualMemoryPotential_iff_residual_ne_zero_of_active
      keep hactive r
  active_memory_iff_energy_ne_zero := by
    intro keep energy hactive henergy r
    exact residualMemoryPotential_iff_energy_ne_zero
      keep energy hactive henergy r
  fixed_iff_not_memory := by
    intro keep hactive r
    exact residualFixed_iff_not_memoryPotential keep hactive r

/-! ## Concrete SAT/Hamiltonian phase carrier projections -/

/-- The information-trace readout on the finite phase residual carrier. -/
def phaseInformationReadout
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (sigma : ℝ)
    (S : HamiltonianSATSharedEnergyCarrier Clause Var) : Clause -> ℝ :=
  residualInformationReadout (phaseResidualKeep Clause sigma) S.obstruction

/-- The memory act on the finite phase residual carrier. -/
def phaseResidualMemoryAct
    (Clause : Type u) (sigma : ℝ) :
    RecollectionAct (Clause -> ℝ) ResidualMemoryAtom :=
  residualMemoryAct (phaseResidualKeep Clause sigma)

/-- THEOREM 6: the phase information readout is exactly `sigma • residual`. -/
theorem phaseInformationReadout_eq_scalar_trace
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (sigma : ℝ)
    (S : HamiltonianSATSharedEnergyCarrier Clause Var) :
    phaseInformationReadout sigma S =
      fun c : Clause => sigma * S.obstruction c := by
  ext c
  simpa [phaseInformationReadout, residualInformationReadout,
    phaseResidualKeep]
    using congrFun
      (truthFormula_scalar_trace
        (K := ℝ) (E := Clause -> ℝ) sigma S.obstruction) c

/-- THEOREM 7: Hamiltonian energy reads the same obstruction residual field as
P722's target-zero residual ledger. -/
theorem phaseHamiltonianEnergy_eq_zeroTargetResidualEnergy
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (S : HamiltonianSATSharedEnergyCarrier Clause Var) :
    hamiltonianEnergyReadout S =
      targetResidualEnergy (fun _ : Clause => 0) S.obstruction :=
  hamiltonianEnergyReadout_eq_zeroTargetResidualEnergy S

/-- THEOREM 8: SAT energy reads the same obstruction residual field as the
same target-zero residual ledger. -/
theorem phaseSatEnergy_eq_zeroTargetResidualEnergy
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (S : HamiltonianSATSharedEnergyCarrier Clause Var) :
    satEnergyReadout S =
      targetResidualEnergy (fun _ : Clause => 0) S.obstruction :=
  satEnergyReadout_eq_zeroTargetResidualEnergy S

/-- THEOREM 9: SAT-energy and Hamiltonian-energy are identical readouts on
the same finite residual carrier. -/
theorem phaseSatEnergy_eq_hamiltonianEnergy
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (S : HamiltonianSATSharedEnergyCarrier Clause Var) :
    satEnergyReadout S = hamiltonianEnergyReadout S :=
  (hamiltonianEnergyReadout_eq_satEnergyReadout S).symm

/-- THEOREM 10: for nonzero phase rate, memory potential on the phase residual
carrier is exactly nonzero Hamiltonian energy. -/
theorem phaseMemoryPotential_iff_hamiltonianEnergy_ne_zero
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (sigma : ℝ) (hsigma : sigma ≠ 0)
    (S : HamiltonianSATSharedEnergyCarrier Clause Var) :
    RecollectableMemoryPotential
        (phaseResidualMemoryAct Clause sigma) S.obstruction ↔
      hamiltonianEnergyReadout S ≠ 0 := by
  simpa [phaseResidualMemoryAct, hamiltonianEnergyReadout]
    using
      residualMemoryPotential_iff_energy_ne_zero
        (phaseResidualKeep Clause sigma)
        (fun residual : Clause -> ℝ => phaseResidualEnergy residual)
        (phaseResidualKeep_active_of_ne_zero Clause sigma hsigma)
        (fun residual : Clause -> ℝ =>
          phaseResidualEnergy_eq_zero_iff_zero_residual residual)
        S.obstruction

/-- THEOREM 11: for nonzero phase rate, memory potential on the phase residual
carrier is exactly nonzero SAT energy. -/
theorem phaseMemoryPotential_iff_satEnergy_ne_zero
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (sigma : ℝ) (hsigma : sigma ≠ 0)
    (S : HamiltonianSATSharedEnergyCarrier Clause Var) :
    RecollectableMemoryPotential
        (phaseResidualMemoryAct Clause sigma) S.obstruction ↔
      satEnergyReadout S ≠ 0 := by
  exact
    (phaseMemoryPotential_iff_hamiltonianEnergy_ne_zero
      sigma hsigma S).trans
      (not_congr (hamiltonianEnergyReadout_zero_iff_satEnergyReadout_zero S))

/-- THEOREM 12: for nonzero phase rate, fixedness is exactly simultaneous
zero information trace, zero SAT energy, and zero Hamiltonian energy. -/
theorem phaseFixed_iff_zero_information_sat_hamiltonian
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (sigma : ℝ) (hsigma : sigma ≠ 0)
    (S : HamiltonianSATSharedEnergyCarrier Clause Var) :
    ResidualTransportFixed (phaseResidualKeep Clause sigma) S.obstruction ↔
      phaseInformationReadout sigma S = 0 ∧
        satEnergyReadout S = 0 ∧
          hamiltonianEnergyReadout S = 0 := by
  constructor
  · intro hfixed
    have hinfo :
        phaseInformationReadout sigma S = 0 := by
      simpa [phaseInformationReadout, residualInformationReadout]
        using
          (residualTransport_fixed_iff_zero_trace
            (phaseResidualKeep Clause sigma)
            (phaseResidualKeep_active_of_ne_zero Clause sigma hsigma)
            S.obstruction).mp hfixed
    have hham :
        hamiltonianEnergyReadout S = 0 := by
      exact
        (phaseResidualTransport_fixed_iff_zero_energy
          (Clause := Clause) sigma hsigma S.obstruction).mp hfixed
    have hsat :
        satEnergyReadout S = 0 :=
      (hamiltonianEnergyReadout_zero_iff_satEnergyReadout_zero S).mp hham
    exact ⟨hinfo, hsat, hham⟩
  · rintro ⟨hinfo, _hsat, _hham⟩
    exact
      (residualTransport_fixed_iff_zero_trace
        (phaseResidualKeep Clause sigma)
        (phaseResidualKeep_active_of_ne_zero Clause sigma hsigma)
        S.obstruction).mpr (by
          simpa [phaseInformationReadout, residualInformationReadout]
            using hinfo)

/-- Concrete projection theorem on the finite phase carrier. -/
structure PhaseResidualProjectionTheorem
    (Clause : Type u) (Var : Type v) [Fintype Clause] : Prop where
  abstract_projection :
    ResidualCarrierProjectionCertificate ℝ (Clause -> ℝ)
  information_is_scalar_trace :
    ∀ (sigma : ℝ),
      ∀ S : HamiltonianSATSharedEnergyCarrier Clause Var,
        phaseInformationReadout sigma S =
          fun c : Clause => sigma * S.obstruction c
  hamiltonian_energy_is_zero_target_residual :
    ∀ S : HamiltonianSATSharedEnergyCarrier Clause Var,
      hamiltonianEnergyReadout S =
        targetResidualEnergy (fun _ : Clause => 0) S.obstruction
  sat_energy_is_zero_target_residual :
    ∀ S : HamiltonianSATSharedEnergyCarrier Clause Var,
      satEnergyReadout S =
        targetResidualEnergy (fun _ : Clause => 0) S.obstruction
  sat_energy_eq_hamiltonian_energy :
    ∀ S : HamiltonianSATSharedEnergyCarrier Clause Var,
      satEnergyReadout S = hamiltonianEnergyReadout S
  memory_iff_hamiltonian_energy_nonzero :
    ∀ (sigma : ℝ), sigma ≠ 0 ->
      ∀ S : HamiltonianSATSharedEnergyCarrier Clause Var,
        RecollectableMemoryPotential
            (phaseResidualMemoryAct Clause sigma) S.obstruction ↔
          hamiltonianEnergyReadout S ≠ 0
  memory_iff_sat_energy_nonzero :
    ∀ (sigma : ℝ), sigma ≠ 0 ->
      ∀ S : HamiltonianSATSharedEnergyCarrier Clause Var,
        RecollectableMemoryPotential
            (phaseResidualMemoryAct Clause sigma) S.obstruction ↔
          satEnergyReadout S ≠ 0
  fixed_iff_zero_information_sat_hamiltonian :
    ∀ (sigma : ℝ), sigma ≠ 0 ->
      ∀ S : HamiltonianSATSharedEnergyCarrier Clause Var,
        ResidualTransportFixed
            (phaseResidualKeep Clause sigma) S.obstruction ↔
          phaseInformationReadout sigma S = 0 ∧
            satEnergyReadout S = 0 ∧
              hamiltonianEnergyReadout S = 0

/-- THEOREM 13: canonical finite phase-carrier projection theorem. -/
theorem phaseResidualProjectionTheorem
    (Clause : Type u) (Var : Type v) [Fintype Clause] :
    PhaseResidualProjectionTheorem Clause Var where
  abstract_projection := residualCarrierProjectionCertificate
  information_is_scalar_trace := by
    intro sigma S
    exact phaseInformationReadout_eq_scalar_trace sigma S
  hamiltonian_energy_is_zero_target_residual := by
    intro S
    exact phaseHamiltonianEnergy_eq_zeroTargetResidualEnergy S
  sat_energy_is_zero_target_residual := by
    intro S
    exact phaseSatEnergy_eq_zeroTargetResidualEnergy S
  sat_energy_eq_hamiltonian_energy := by
    intro S
    exact phaseSatEnergy_eq_hamiltonianEnergy S
  memory_iff_hamiltonian_energy_nonzero := by
    intro sigma hsigma S
    exact phaseMemoryPotential_iff_hamiltonianEnergy_ne_zero sigma hsigma S
  memory_iff_sat_energy_nonzero := by
    intro sigma hsigma S
    exact phaseMemoryPotential_iff_satEnergy_ne_zero sigma hsigma S
  fixed_iff_zero_information_sat_hamiltonian := by
    intro sigma hsigma S
    exact phaseFixed_iff_zero_information_sat_hamiltonian sigma hsigma S

end ResidualProjection
end SaturationMonoid
