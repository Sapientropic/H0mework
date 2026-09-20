import H0mework.Realization.Residual.Process
import H0mework.Realization.Residual.Producer

/-!
# Effective residual-process projection adapter

This adapter identifies the source-native `EffectiveResidualProcess` with the
historical residual-carrier presentation.  It is deliberately outside the
authority kernel: information, memory, phase, and energy projections are
readouts of an already generated update.
-/

noncomputable section

namespace SaturationMonoid
namespace ResidualProjection

open AffineRelaxation

universe u v w

/-- Project an effective process into the historical residual-carrier view. -/
def EffectiveResidualProcess.toResidualCarrierSystemProducer
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State) :
    ResidualCarrierSystemProducer K E State where
  target := P.target
  keep := P.keep
  residual := P.residual
  update := P.update
  residual_transport_law := P.residual_transport_law
  projection := residualCarrierProjectionCertificate

/-- Forget a residual-carrier projection to its actual effective process. -/
def ResidualCarrierSystemProducer.toEffectiveResidualProcess
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : ResidualCarrierSystemProducer K E State) :
    EffectiveResidualProcess K E State where
  target := P.target
  keep := P.keep
  residual := P.residual
  update := P.update
  residual_transport_law := P.residual_transport_law

theorem effectiveProcess_toProducer_toEffectiveProcess_eq
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State) :
    P.toResidualCarrierSystemProducer.toEffectiveResidualProcess = P := by
  cases P
  rfl

theorem producer_toEffectiveProcess_toProducer_eq
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : ResidualCarrierSystemProducer K E State) :
    P.toEffectiveResidualProcess.toResidualCarrierSystemProducer = P := by
  cases P
  rfl

/-- Effective processes and residual-carrier projections are equivalent
presentations of the same generated update. -/
def effectiveProcessResidualCarrierEquiv
    (K E State : Type*) [Field K] [AddCommGroup E] [Module K E] :
    EffectiveResidualProcess K E State ≃
      ResidualCarrierSystemProducer K E State where
  toFun := EffectiveResidualProcess.toResidualCarrierSystemProducer
  invFun := ResidualCarrierSystemProducer.toEffectiveResidualProcess
  left_inv := effectiveProcess_toProducer_toEffectiveProcess_eq
  right_inv := producer_toEffectiveProcess_toProducer_eq

theorem effectiveProcess_unique_residualCarrier_reconstruction
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State) :
    ∃! Q : ResidualCarrierSystemProducer K E State,
      Q.toEffectiveResidualProcess = P := by
  refine ⟨P.toResidualCarrierSystemProducer,
    effectiveProcess_toProducer_toEffectiveProcess_eq P, ?_⟩
  intro Q hQ
  calc
    Q = Q.toEffectiveResidualProcess.toResidualCarrierSystemProducer := by
      exact (producer_toEffectiveProcess_toProducer_eq Q).symm
    _ = P.toResidualCarrierSystemProducer := by rw [hQ]

theorem effectiveProcess_toProducer_target_eq
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State) :
    P.toResidualCarrierSystemProducer.target = P.target := rfl

theorem effectiveProcess_toProducer_keep_eq
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State) :
    P.toResidualCarrierSystemProducer.keep = P.keep := rfl

theorem effectiveProcess_toProducer_residual_eq
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State) :
    P.toResidualCarrierSystemProducer.residual = P.residual := rfl

theorem effectiveProcess_toProducer_update_eq
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State) :
    P.toResidualCarrierSystemProducer.update = P.update := rfl

theorem effectiveProcess_toProducer_residual_transport_law
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E]
    (P : EffectiveResidualProcess K E State) (state : State) :
    P.toResidualCarrierSystemProducer.residual
        (P.toResidualCarrierSystemProducer.update state) =
      P.toResidualCarrierSystemProducer.keep
        (P.toResidualCarrierSystemProducer.residual state) :=
  P.residual_transport_law state

/-- Complete equivalence/readout certificate. -/
structure EffectiveResidualProcessUniversalProperty
    (K E State : Type*) [Field K] [AddCommGroup E] [Module K E] : Prop where
  to_producer_to_effective :
    ∀ P : EffectiveResidualProcess K E State,
      P.toResidualCarrierSystemProducer.toEffectiveResidualProcess = P
  producer_to_effective_to_producer :
    ∀ P : ResidualCarrierSystemProducer K E State,
      P.toEffectiveResidualProcess.toResidualCarrierSystemProducer = P
  unique_residual_carrier_reconstruction :
    ∀ P : EffectiveResidualProcess K E State,
      ∃! Q : ResidualCarrierSystemProducer K E State,
        Q.toEffectiveResidualProcess = P
  to_producer_target :
    ∀ P : EffectiveResidualProcess K E State,
      P.toResidualCarrierSystemProducer.target = P.target
  to_producer_keep :
    ∀ P : EffectiveResidualProcess K E State,
      P.toResidualCarrierSystemProducer.keep = P.keep
  to_producer_residual :
    ∀ P : EffectiveResidualProcess K E State,
      P.toResidualCarrierSystemProducer.residual = P.residual
  to_producer_update :
    ∀ P : EffectiveResidualProcess K E State,
      P.toResidualCarrierSystemProducer.update = P.update
  residual_split :
    ∀ P : EffectiveResidualProcess K E State, ∀ state : State,
      P.residual state =
        P.residual (P.update state) +
          linearResidualTrace P.keep (P.residual state)
  trace_unique :
    ∀ P : EffectiveResidualProcess K E State,
      ∀ state : State, ∀ trace : E,
        P.residual state = P.residual (P.update state) + trace ↔
          trace = linearResidualTrace P.keep (P.residual state)
  fixed_zero_trace_energy :
    ∀ P : EffectiveResidualProcess K E State, ∀ energy : E → ℝ,
      ResidualTransportActive P.keep →
        (∀ residual : E, energy residual = 0 ↔ residual = 0) →
          ∀ state : State,
            ResidualTransportFixed P.keep (P.residual state) ↔
              P.residual state = 0 ∧
                linearResidualTrace P.keep (P.residual state) = 0 ∧
                  energy (P.residual state) = 0

theorem effectiveResidualProcessUniversalProperty
    {K E State : Type*} [Field K] [AddCommGroup E] [Module K E] :
    EffectiveResidualProcessUniversalProperty K E State where
  to_producer_to_effective :=
    effectiveProcess_toProducer_toEffectiveProcess_eq
  producer_to_effective_to_producer :=
    producer_toEffectiveProcess_toProducer_eq
  unique_residual_carrier_reconstruction :=
    effectiveProcess_unique_residualCarrier_reconstruction
  to_producer_target := effectiveProcess_toProducer_target_eq
  to_producer_keep := effectiveProcess_toProducer_keep_eq
  to_producer_residual := effectiveProcess_toProducer_residual_eq
  to_producer_update := effectiveProcess_toProducer_update_eq
  residual_split := effectiveProcess_residual_eq_next_residual_add_trace
  trace_unique := effectiveProcess_trace_unique
  fixed_zero_trace_energy := by
    intro P energy active energyZero state
    exact effectiveProcess_fixed_iff_zero_residual_trace_energy
      P energy active energyZero state

end ResidualProjection
end SaturationMonoid
