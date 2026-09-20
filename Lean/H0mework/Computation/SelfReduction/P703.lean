import H0mework.Computation.SelfReduction.P698
import H0mework.Physics.SourceForms.P702

/-!
# Proposition 703: Hamiltonian-energy and SAT-energy share one carrier

P662 packages the guarded Hamiltonian / H¹ energy face into the central
`information = mathematics = matter = energy` projection certificate.  P698
proves that the SAT phase-flow Lyapunov energy is exactly obstruction freedom.

This file adds the missing diagonal bridge between those two uses of the word
`energy`:

* the shared carrier is the P696/P698 finite phase-flow state
  `SATPhaseFlowState Clause Var`;
* the Hamiltonian-facing energy readout and the SAT-facing energy readout are
  the same function on that carrier, namely `sum_c obstruction_c^2`;
* their zero sets, positive sets, one-step laws, finite-iterate laws, and
  producer surfaces are therefore identical;
* any accepted Hamiltonian/SAT energy producer is the canonical readout, so
  this bridge introduces no extra parameter family.

Boundary: this proves identity of the certified Hamiltonian-energy and
SAT-energy readout on the finite residual carrier.  It does not construct an
arbitrary physical Hamiltonian from an arbitrary SAT instance, prove smooth
threshold dynamics, prove polynomial SAT, prove `P = NP`, or remove the
existing runtime faithfulness boundary for reducers outside the certified
phase-flow model.
-/

noncomputable section

namespace SaturationMonoid

namespace ComplexityProjection

open scoped BigOperators

set_option linter.checkUnivs false
set_option linter.defProp false

universe u v

/-! ## Shared carrier and two readouts -/

/-- The shared finite carrier on which both energy readings live. -/
abbrev HamiltonianSATSharedEnergyCarrier (Clause : Type u) (Var : Type v)
    [Fintype Clause] : Type (max u v) :=
  SATPhaseFlowState Clause Var

/-- The Hamiltonian-facing energy readout on the shared residual carrier.

This is the finite-carrier version of the Hamiltonian/H¹ energy face: it reads
the squared residual magnitude that P698 proves is exactly obstruction freedom.
-/
def hamiltonianEnergyReadout
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (S : HamiltonianSATSharedEnergyCarrier Clause Var) : ℝ :=
  phaseResidualEnergy S.obstruction

/-- The SAT-facing Lyapunov energy readout on the same carrier. -/
def satEnergyReadout
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (S : HamiltonianSATSharedEnergyCarrier Clause Var) : ℝ :=
  S.energy

/-- THEOREM 1: Hamiltonian-energy and SAT-energy are the same scalar readout
on the same residual carrier. -/
theorem hamiltonianEnergyReadout_eq_satEnergyReadout
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (S : HamiltonianSATSharedEnergyCarrier Clause Var) :
    hamiltonianEnergyReadout S = satEnergyReadout S := by
  rfl

/-- THEOREM 2: zero Hamiltonian-energy is exactly obstruction freedom. -/
theorem hamiltonianEnergyReadout_eq_zero_iff_obstruction_free
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (S : HamiltonianSATSharedEnergyCarrier Clause Var) :
    hamiltonianEnergyReadout S = 0 ↔
      ∀ c : Clause, S.obstruction c = 0 := by
  exact phaseResidualEnergy_eq_zero_iff S.obstruction

/-- THEOREM 3: zero Hamiltonian-energy is exactly zero SAT-energy. -/
theorem hamiltonianEnergyReadout_zero_iff_satEnergyReadout_zero
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (S : HamiltonianSATSharedEnergyCarrier Clause Var) :
    hamiltonianEnergyReadout S = 0 ↔ satEnergyReadout S = 0 := by
  rw [hamiltonianEnergyReadout_eq_satEnergyReadout S]

/-- THEOREM 4: a positive residual forces positive Hamiltonian-energy. -/
theorem hamiltonianEnergyReadout_pos_of_residual_ne_zero
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (S : HamiltonianSATSharedEnergyCarrier Clause Var) {c : Clause}
    (hc : S.obstruction c ≠ 0) :
    0 < hamiltonianEnergyReadout S := by
  exact phaseResidualEnergy_pos_of_residual_ne_zero S.obstruction hc

/-! ## One-step and iterated laws transported across the diagonal -/

/-- THEOREM 5: a certified dissipative phase step multiplies the Hamiltonian
energy readout by the same factor as the SAT Lyapunov energy. -/
theorem hamiltonianEnergyReadout_dissipationStep_eq
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (sigma dt : ℝ)
    (direction : Clause -> Var -> ℝ)
    (S : HamiltonianSATSharedEnergyCarrier Clause Var) :
    hamiltonianEnergyReadout
        (phaseFlowDissipationStep sigma dt direction S) =
      (1 - sigma) ^ 2 * hamiltonianEnergyReadout S := by
  exact phaseFlowDissipationStep_energy_eq sigma dt direction S

/-- THEOREM 6: finite dissipative iteration transports to the Hamiltonian
energy readout with the same geometric law. -/
theorem hamiltonianEnergyReadout_dissipationIterate_eq
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (sigma dt : ℝ)
    (direction : Clause -> Var -> ℝ)
    (n : ℕ)
    (S : HamiltonianSATSharedEnergyCarrier Clause Var) :
    hamiltonianEnergyReadout
        (phaseFlowDissipationIterate sigma dt direction n S) =
      ((1 - sigma) ^ 2) ^ n * hamiltonianEnergyReadout S := by
  exact phaseFlowDissipationIterate_energy_eq sigma dt direction n S

/-- THEOREM 7: zero Hamiltonian-energy fixes one certified dissipative step. -/
theorem phaseFlowDissipationStep_fixed_of_hamiltonianEnergy_zero
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (sigma dt : ℝ)
    (direction : Clause -> Var -> ℝ)
    (S : HamiltonianSATSharedEnergyCarrier Clause Var)
    (hE : hamiltonianEnergyReadout S = 0) :
    phaseFlowDissipationStep sigma dt direction S = S := by
  exact phaseFlowDissipationStep_fixed_of_energy_zero
    sigma dt direction S hE

/-- THEOREM 8: zero Hamiltonian-energy fixes every certified dissipative
iterate. -/
theorem phaseFlowDissipationIterate_fixed_of_hamiltonianEnergy_zero
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (sigma dt : ℝ)
    (direction : Clause -> Var -> ℝ)
    (n : ℕ)
    (S : HamiltonianSATSharedEnergyCarrier Clause Var)
    (hE : hamiltonianEnergyReadout S = 0) :
    phaseFlowDissipationIterate sigma dt direction n S = S := by
  exact phaseFlowDissipationIterate_fixed_of_energy_zero
    sigma dt direction n S hE

/-! ## Producer surface: no extra Hamiltonian/SAT energy freedom -/

/-- A producer for a scalar energy readout on the shared carrier. -/
abbrev HamiltonianSATEnergyProducer (Clause : Type u) (Var : Type v)
    [Fintype Clause] : Type (max u v) :=
  HamiltonianSATSharedEnergyCarrier Clause Var -> ℝ

/-- The canonical shared energy producer. -/
def canonicalHamiltonianSATEnergyProducer
    (Clause : Type u) (Var : Type v) [Fintype Clause] :
    HamiltonianSATEnergyProducer Clause Var :=
  fun S => hamiltonianEnergyReadout S

/-- Accepted producer surface: a producer is faithful exactly when it reads
the shared Hamiltonian/SAT residual energy. -/
def HamiltonianSATEnergyProducerSurface
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (P : HamiltonianSATEnergyProducer Clause Var) : Prop :=
  ∀ S : HamiltonianSATSharedEnergyCarrier Clause Var,
    P S = hamiltonianEnergyReadout S

/-- THEOREM 9: the canonical producer lies on the shared energy surface. -/
theorem canonicalHamiltonianSATEnergyProducer_surface
    (Clause : Type u) (Var : Type v) [Fintype Clause] :
    HamiltonianSATEnergyProducerSurface
      (canonicalHamiltonianSATEnergyProducer Clause Var) := by
  intro S
  rfl

/-- THEOREM 10: every accepted Hamiltonian/SAT energy producer is canonical. -/
theorem eq_canonicalHamiltonianSATEnergyProducer_of_surface
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (P : HamiltonianSATEnergyProducer Clause Var)
    (hP : HamiltonianSATEnergyProducerSurface P) :
    P = canonicalHamiltonianSATEnergyProducer Clause Var := by
  funext S
  exact hP S

/-- THEOREM 11: the shared energy producer surface is exactly the canonical
producer. -/
theorem hamiltonianSATEnergyProducerSurface_iff_canonical
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (P : HamiltonianSATEnergyProducer Clause Var) :
    HamiltonianSATEnergyProducerSurface P ↔
      P = canonicalHamiltonianSATEnergyProducer Clause Var := by
  constructor
  · exact eq_canonicalHamiltonianSATEnergyProducer_of_surface P
  · intro hP
    rw [hP]
    exact canonicalHamiltonianSATEnergyProducer_surface Clause Var

/-- THEOREM 12: any two accepted shared energy producers are equal. -/
theorem hamiltonianSATEnergyProducerSurface_noFree
    {Clause : Type u} {Var : Type v} [Fintype Clause]
    (P Q : HamiltonianSATEnergyProducer Clause Var)
    (hP : HamiltonianSATEnergyProducerSurface P)
    (hQ : HamiltonianSATEnergyProducerSurface Q) :
    P = Q := by
  rw [eq_canonicalHamiltonianSATEnergyProducer_of_surface P hP,
    eq_canonicalHamiltonianSATEnergyProducer_of_surface Q hQ]

/-! ## Packaged finite-carrier certificate -/

/-- P703 local certificate: P698's SAT energy and the Hamiltonian-facing energy
readout are the same no-free producer surface on one residual carrier. -/
structure HamiltonianSATEnergySameCarrierCertificate : Prop where
  p698_energy_zero :
    SATPhaseFlowEnergyZeroObstructionCertificate.{u, v}
  readout_eq :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (S : HamiltonianSATSharedEnergyCarrier Clause Var),
      hamiltonianEnergyReadout S = satEnergyReadout S
  hamiltonian_zero_iff_obstruction_free :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (S : HamiltonianSATSharedEnergyCarrier Clause Var),
      hamiltonianEnergyReadout S = 0 ↔ ∀ c, S.obstruction c = 0
  hamiltonian_zero_iff_sat_zero :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (S : HamiltonianSATSharedEnergyCarrier Clause Var),
      hamiltonianEnergyReadout S = 0 ↔ satEnergyReadout S = 0
  hamiltonian_step_energy_eq :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (sigma dt : ℝ)
      (direction : Clause -> Var -> ℝ)
      (S : HamiltonianSATSharedEnergyCarrier Clause Var),
      hamiltonianEnergyReadout
          (phaseFlowDissipationStep sigma dt direction S) =
        (1 - sigma) ^ 2 * hamiltonianEnergyReadout S
  hamiltonian_iterate_energy_eq :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (sigma dt : ℝ)
      (direction : Clause -> Var -> ℝ)
      (n : ℕ)
      (S : HamiltonianSATSharedEnergyCarrier Clause Var),
      hamiltonianEnergyReadout
          (phaseFlowDissipationIterate sigma dt direction n S) =
        ((1 - sigma) ^ 2) ^ n * hamiltonianEnergyReadout S
  producer_surface_iff_canonical :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (P : HamiltonianSATEnergyProducer Clause Var),
      HamiltonianSATEnergyProducerSurface P ↔
        P = canonicalHamiltonianSATEnergyProducer Clause Var
  producer_no_free :
    ∀ {Clause : Type u} {Var : Type v} [Fintype Clause]
      (P Q : HamiltonianSATEnergyProducer Clause Var),
      HamiltonianSATEnergyProducerSurface P ->
      HamiltonianSATEnergyProducerSurface Q ->
        P = Q

/-- DEFINITION 1: canonical P703 local shared-energy certificate. -/
def hamiltonianSATEnergySameCarrierCertificate :
    HamiltonianSATEnergySameCarrierCertificate where
  p698_energy_zero := satPhaseFlowEnergyZeroObstructionCertificate
  readout_eq := by
    intro Clause Var _ S
    exact hamiltonianEnergyReadout_eq_satEnergyReadout S
  hamiltonian_zero_iff_obstruction_free := by
    intro Clause Var _ S
    exact hamiltonianEnergyReadout_eq_zero_iff_obstruction_free S
  hamiltonian_zero_iff_sat_zero := by
    intro Clause Var _ S
    exact hamiltonianEnergyReadout_zero_iff_satEnergyReadout_zero S
  hamiltonian_step_energy_eq := by
    intro Clause Var _ sigma dt direction S
    exact hamiltonianEnergyReadout_dissipationStep_eq
      sigma dt direction S
  hamiltonian_iterate_energy_eq := by
    intro Clause Var _ sigma dt direction n S
    exact hamiltonianEnergyReadout_dissipationIterate_eq
      sigma dt direction n S
  producer_surface_iff_canonical := by
    intro Clause Var _ P
    exact hamiltonianSATEnergyProducerSurface_iff_canonical P
  producer_no_free := by
    intro Clause Var _ P Q hP hQ
    exact hamiltonianSATEnergyProducerSurface_noFree P Q hP hQ

end ComplexityProjection

/-! ## Grand root packaging -/

namespace GrandUnification

open ComplexityProjection

set_option linter.checkUnivs false

universe w z

/-- P703 grand root: the P662/P702 central diagonal and P698 SAT energy root
share a single residual-energy carrier with no producer freedom. -/
structure HamiltonianSATEnergySameCarrierUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  p702_diagonal_no_family :
    EnergyInformationMathematicsPhysicsDiagonalNoFamilyFreedomCertificate.{w, u, v, z}
      E
  p698_phase_energy_zero :
    PhaseFlowEnergyZeroObstructionUnifiedRootCertificate.{u, v, w, z} E
  same_carrier_energy :
    _root_.SaturationMonoid.ComplexityProjection.HamiltonianSATEnergySameCarrierCertificate.{v, w}

/-- THEOREM 13: the Hamiltonian-energy / SAT-energy same-carrier grand root is
inhabited. -/
def hamiltonianSATEnergySameCarrierUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    HamiltonianSATEnergySameCarrierUnifiedRootCertificate E where
  p702_diagonal_no_family :=
    energyInformationMathematicsPhysicsDiagonalNoFamilyFreedomCertificate
      (E := E)
  p698_phase_energy_zero :=
    phaseFlowEnergyZeroObstructionUnifiedRootCertificate (E0 := E)
  same_carrier_energy :=
    _root_.SaturationMonoid.ComplexityProjection.hamiltonianSATEnergySameCarrierCertificate

end GrandUnification

end SaturationMonoid
