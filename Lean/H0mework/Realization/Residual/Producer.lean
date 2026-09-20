import H0mework.Realization.Residual.Projection

/-!
# Producer theorem

`TruthFormulaCore` proves the residual equation.
`ProjectionTheorem` proves that information, memory, energy, SAT, and
Hamiltonian readings are projections of a residual carrier.

This file starts the producer layer: a concrete system must actually supply

* a target;
* a keep operator `K`;
* a residual map;
* an update;
* the residual transport law;
* the projection certificate for that residual carrier.

Two producers are closed here:

* the scalar/module affine system;
* the finite phase/SAT-Hamiltonian system.
-/

noncomputable section

namespace SaturationMonoid
namespace ResidualProjection

open AffineRelaxation
open ComplexityProjection
open EnergyLedgerProjection

universe u v w

/-! ## Generic producer contract -/

/-- A concrete system producer for the residual carrier.

The update is not allowed to be a black box: it must transport the produced
residual by the produced keep operator. -/
structure ResidualCarrierSystemProducer
    (K E State : Type*) [Field K] [AddCommGroup E] [Module K E] where
  target : E
  keep : E →ₗ[K] E
  residual : State -> E
  update : State -> State
  residual_transport_law :
    ∀ s : State, residual (update s) = keep (residual s)
  projection :
    ResidualCarrierProjectionCertificate K E

/-! ## Generic no-static-positive-residual theorem -/

/-- A residual-system producer with an active keep operator is static under its
own update exactly at zero residual.

This is the producer-level "no absolute static positive residual" theorem:
the update is forced by `residual_transport_law`, so a residual that survives
the update unchanged is a Truth Formula fixed residual, and active transport
collapses fixedness to zero. -/
theorem residualCarrierSystemProducer_static_residual_iff_zero
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : ResidualCarrierSystemProducer K E State)
    (hactive : ResidualTransportActive P.keep)
    (s : State) :
    P.residual (P.update s) = P.residual s ↔
      P.residual s = 0 := by
  constructor
  · intro hstatic
    have hfixed :
        ResidualTransportFixed P.keep (P.residual s) := by
      dsimp [ResidualTransportFixed]
      rw [← P.residual_transport_law s]
      exact hstatic
    exact
      (residualTransport_fixed_iff_zero_residual
        P.keep hactive (P.residual s)).mp hfixed
  · intro hzero
    rw [P.residual_transport_law s, hzero]
    simp

/-- Contrapositive form: an active producer cannot leave a nonzero residual
unchanged by its own update. -/
theorem residualCarrierSystemProducer_update_residual_ne_self_of_ne_zero
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : ResidualCarrierSystemProducer K E State)
    (hactive : ResidualTransportActive P.keep)
    {s : State}
    (hnonzero : P.residual s ≠ 0) :
    P.residual (P.update s) ≠ P.residual s := by
  intro hstatic
  exact hnonzero
    ((residualCarrierSystemProducer_static_residual_iff_zero
      P hactive s).mp hstatic)

/-- Energy readout form: if an active producer is static under its own update,
any faithful zero-energy readout must read zero energy on that residual. -/
theorem residualCarrierSystemProducer_static_residual_energy_eq_zero
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : ResidualCarrierSystemProducer K E State)
    (hactive : ResidualTransportActive P.keep)
    (energy : E -> ℝ)
    (henergy : ∀ r : E, energy r = 0 ↔ r = 0)
    {s : State}
    (hstatic : P.residual (P.update s) = P.residual s) :
    energy (P.residual s) = 0 :=
  (henergy (P.residual s)).mpr
    ((residualCarrierSystemProducer_static_residual_iff_zero
      P hactive s).mp hstatic)

/-- Positive-energy contrapositive: a residual with nonzero faithful energy
cannot be an update-static residual of an active producer. -/
theorem residualCarrierSystemProducer_update_residual_ne_self_of_energy_ne_zero
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : ResidualCarrierSystemProducer K E State)
    (hactive : ResidualTransportActive P.keep)
    (energy : E -> ℝ)
    (henergy : ∀ r : E, energy r = 0 ↔ r = 0)
    {s : State}
    (henergy_nonzero : energy (P.residual s) ≠ 0) :
    P.residual (P.update s) ≠ P.residual s := by
  intro hstatic
  exact henergy_nonzero
    (residualCarrierSystemProducer_static_residual_energy_eq_zero
      P hactive energy henergy hstatic)

/-! ## Scalar/module affine producer -/

/-- The scalar/module affine producer:

* target = the supplied target;
* keep = `r ↦ (1 - sigma) • r`;
* residual = `target - x`;
* update = `x ↦ x + sigma • (target - x)`.
-/
def scalarAffineSystemProducer
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : E) (sigma : K) :
    ResidualCarrierSystemProducer K E E where
  target := target
  keep := scalarKeepLinearMap (K := K) (E := E) sigma
  residual := fun x => target - x
  update := fun x => relaxModule target sigma x
  residual_transport_law := by
    intro x
    exact target_sub_relaxModule target sigma x
  projection := residualCarrierProjectionCertificate

/-- THEOREM 1: the scalar producer emits the requested target. -/
theorem scalarAffineProducer_target_eq
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : E) (sigma : K) :
    (scalarAffineSystemProducer target sigma).target = target :=
  rfl

/-- THEOREM 2: the scalar producer emits the scalar keep operator. -/
theorem scalarAffineProducer_keep_eq
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : E) (sigma : K) :
    (scalarAffineSystemProducer target sigma).keep =
      scalarKeepLinearMap (K := K) (E := E) sigma :=
  rfl

/-- THEOREM 3: the scalar producer emits the target residual. -/
theorem scalarAffineProducer_residual_eq
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target x : E) (sigma : K) :
    (scalarAffineSystemProducer target sigma).residual x = target - x :=
  rfl

/-- THEOREM 4: the scalar producer emits the affine update. -/
theorem scalarAffineProducer_update_eq
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target x : E) (sigma : K) :
    (scalarAffineSystemProducer target sigma).update x =
      x + sigma • (target - x) :=
  rfl

/-- THEOREM 5: the scalar producer satisfies the residual transport law. -/
theorem scalarAffineProducer_residual_transport_law
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target x : E) (sigma : K) :
    (scalarAffineSystemProducer target sigma).residual
        ((scalarAffineSystemProducer target sigma).update x) =
      (scalarAffineSystemProducer target sigma).keep
        ((scalarAffineSystemProducer target sigma).residual x) :=
  (scalarAffineSystemProducer target sigma).residual_transport_law x

/-- Scalar producer component certificate. -/
structure ScalarAffineProducerCertificate
    (K E : Type*) [Field K] [AddCommGroup E] [Module K E] : Prop where
  emits_target :
    ∀ target : E, ∀ sigma : K,
      (scalarAffineSystemProducer target sigma).target = target
  emits_keep :
    ∀ target : E, ∀ sigma : K,
      (scalarAffineSystemProducer target sigma).keep =
        scalarKeepLinearMap (K := K) (E := E) sigma
  emits_residual :
    ∀ target x : E, ∀ sigma : K,
      (scalarAffineSystemProducer target sigma).residual x = target - x
  emits_affine_update :
    ∀ target x : E, ∀ sigma : K,
      (scalarAffineSystemProducer target sigma).update x =
        x + sigma • (target - x)
  residual_law :
    ∀ target x : E, ∀ sigma : K,
      (scalarAffineSystemProducer target sigma).residual
          ((scalarAffineSystemProducer target sigma).update x) =
        (scalarAffineSystemProducer target sigma).keep
          ((scalarAffineSystemProducer target sigma).residual x)
  projection :
    ResidualCarrierProjectionCertificate K E

/-- THEOREM 6: canonical scalar affine producer certificate. -/
theorem scalarAffineProducerCertificate
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E] :
    ScalarAffineProducerCertificate K E where
  emits_target := by
    intro target sigma
    exact scalarAffineProducer_target_eq target sigma
  emits_keep := by
    intro target sigma
    exact scalarAffineProducer_keep_eq target sigma
  emits_residual := by
    intro target x sigma
    exact scalarAffineProducer_residual_eq target x sigma
  emits_affine_update := by
    intro target x sigma
    exact scalarAffineProducer_update_eq target x sigma
  residual_law := by
    intro target x sigma
    exact scalarAffineProducer_residual_transport_law target x sigma
  projection := residualCarrierProjectionCertificate

/-! ## Finite phase / SAT-Hamiltonian producer -/

/-- The finite phase/SAT-Hamiltonian producer:

* target = zero residual field;
* keep = phase residual keep `r ↦ (1 - sigma) r`;
* residual = `S.obstruction`;
* update = certified dissipative phase-flow step;
* projection = `PhaseResidualProjectionTheorem`.
-/
def phaseResidualSystemProducer
    (Clause : Type u) (Var : Type v) [Fintype Clause]
    (sigma dt : ℝ)
    (direction : Clause -> Var -> ℝ) :
    ResidualCarrierSystemProducer ℝ (Clause -> ℝ)
      (HamiltonianSATSharedEnergyCarrier Clause Var) where
  target := fun _ => 0
  keep := phaseResidualKeep Clause sigma
  residual := fun S => S.obstruction
  update := fun S => phaseFlowDissipationStep sigma dt direction S
  residual_transport_law := by
    intro S
    simpa [phaseFlowDissipationStep]
      using (phaseResidualKeep_apply Clause sigma S.obstruction).symm
  projection := residualCarrierProjectionCertificate

/-- THEOREM 7: the phase producer emits target zero. -/
theorem phaseProducer_target_eq_zero
    (Clause : Type u) (Var : Type v) [Fintype Clause]
    (sigma dt : ℝ) (direction : Clause -> Var -> ℝ) :
    (phaseResidualSystemProducer Clause Var sigma dt direction).target =
      (fun _ : Clause => 0) :=
  rfl

/-- THEOREM 8: the phase producer emits the certified phase keep operator. -/
theorem phaseProducer_keep_eq
    (Clause : Type u) (Var : Type v) [Fintype Clause]
    (sigma dt : ℝ) (direction : Clause -> Var -> ℝ) :
    (phaseResidualSystemProducer Clause Var sigma dt direction).keep =
      phaseResidualKeep Clause sigma :=
  rfl

/-- THEOREM 9: the phase producer emits the obstruction residual. -/
theorem phaseProducer_residual_eq_obstruction
    (Clause : Type u) (Var : Type v) [Fintype Clause]
    (sigma dt : ℝ) (direction : Clause -> Var -> ℝ)
    (S : HamiltonianSATSharedEnergyCarrier Clause Var) :
    (phaseResidualSystemProducer Clause Var sigma dt direction).residual S =
      S.obstruction :=
  rfl

/-- THEOREM 10: the phase producer emits the certified dissipative update. -/
theorem phaseProducer_update_eq_dissipationStep
    (Clause : Type u) (Var : Type v) [Fintype Clause]
    (sigma dt : ℝ) (direction : Clause -> Var -> ℝ)
    (S : HamiltonianSATSharedEnergyCarrier Clause Var) :
    (phaseResidualSystemProducer Clause Var sigma dt direction).update S =
      phaseFlowDissipationStep sigma dt direction S :=
  rfl

/-- THEOREM 11: the phase producer satisfies the residual transport law. -/
theorem phaseProducer_residual_transport_law
    (Clause : Type u) (Var : Type v) [Fintype Clause]
    (sigma dt : ℝ) (direction : Clause -> Var -> ℝ)
    (S : HamiltonianSATSharedEnergyCarrier Clause Var) :
    (phaseResidualSystemProducer Clause Var sigma dt direction).residual
        ((phaseResidualSystemProducer Clause Var sigma dt direction).update S) =
      (phaseResidualSystemProducer Clause Var sigma dt direction).keep
        ((phaseResidualSystemProducer Clause Var sigma dt direction).residual S) :=
  (phaseResidualSystemProducer Clause Var sigma dt direction).residual_transport_law S

/-- Phase producer component certificate. -/
structure PhaseResidualProducerCertificate
    (Clause : Type u) (Var : Type v) [Fintype Clause] : Prop where
  emits_zero_target :
    ∀ sigma dt : ℝ, ∀ direction : Clause -> Var -> ℝ,
      (phaseResidualSystemProducer Clause Var sigma dt direction).target =
        (fun _ : Clause => 0)
  emits_phase_keep :
    ∀ sigma dt : ℝ, ∀ direction : Clause -> Var -> ℝ,
      (phaseResidualSystemProducer Clause Var sigma dt direction).keep =
        phaseResidualKeep Clause sigma
  emits_obstruction_residual :
    ∀ sigma dt : ℝ, ∀ direction : Clause -> Var -> ℝ,
      ∀ S : HamiltonianSATSharedEnergyCarrier Clause Var,
        (phaseResidualSystemProducer Clause Var sigma dt direction).residual S =
          S.obstruction
  emits_dissipation_update :
    ∀ sigma dt : ℝ, ∀ direction : Clause -> Var -> ℝ,
      ∀ S : HamiltonianSATSharedEnergyCarrier Clause Var,
        (phaseResidualSystemProducer Clause Var sigma dt direction).update S =
          phaseFlowDissipationStep sigma dt direction S
  residual_law :
    ∀ sigma dt : ℝ, ∀ direction : Clause -> Var -> ℝ,
      ∀ S : HamiltonianSATSharedEnergyCarrier Clause Var,
        (phaseResidualSystemProducer Clause Var sigma dt direction).residual
            ((phaseResidualSystemProducer Clause Var sigma dt direction).update S) =
          (phaseResidualSystemProducer Clause Var sigma dt direction).keep
            ((phaseResidualSystemProducer Clause Var sigma dt direction).residual S)
  projection :
    PhaseResidualProjectionTheorem Clause Var

/-- THEOREM 12: canonical phase/SAT-Hamiltonian producer certificate. -/
theorem phaseResidualProducerCertificate
    (Clause : Type u) (Var : Type v) [Fintype Clause] :
    PhaseResidualProducerCertificate Clause Var where
  emits_zero_target := by
    intro sigma dt direction
    exact phaseProducer_target_eq_zero Clause Var sigma dt direction
  emits_phase_keep := by
    intro sigma dt direction
    exact phaseProducer_keep_eq Clause Var sigma dt direction
  emits_obstruction_residual := by
    intro sigma dt direction S
    exact phaseProducer_residual_eq_obstruction Clause Var sigma dt direction S
  emits_dissipation_update := by
    intro sigma dt direction S
    exact phaseProducer_update_eq_dissipationStep Clause Var sigma dt direction S
  residual_law := by
    intro sigma dt direction S
    exact phaseProducer_residual_transport_law Clause Var sigma dt direction S
  projection := phaseResidualProjectionTheorem Clause Var

/-- The current producer theorem root: scalar affine systems and finite
phase/SAT-Hamiltonian systems both actually produce the required residual
carrier components. -/
structure ProducerTheoremRoot : Prop where
  scalar_affine :
    ∀ {K E : Type} [Field K] [AddCommGroup E] [Module K E],
      ScalarAffineProducerCertificate K E
  phase :
    ∀ (Clause Var : Type) [Fintype Clause],
      PhaseResidualProducerCertificate Clause Var

/-- THEOREM 13: canonical producer theorem root. -/
theorem producerTheoremRoot : ProducerTheoremRoot where
  scalar_affine := by
    intro K E _ _ _
    exact scalarAffineProducerCertificate (K := K) (E := E)
  phase := by
    intro Clause Var _
    exact phaseResidualProducerCertificate Clause Var

end ResidualProjection
end SaturationMonoid
