import H0mework.Physics.JointSources.GrandInventory

/-!
# Proposition 820: carrier consistency gives nonempty zero fibers

P743/P744 put the grand producer theorem on one residual carrier.  This file
packages the next closure step:

* every declared grand domain has a canonical residual zero fiber;
* SAT phase obstruction has a zero fiber by threshold collapse;
* the color-loop trace / zero-energy fiber is produced by the same-carrier
  alpha-convergence bridge of P819.

The point is not another receipt for a target value.  It is the carrier
consistency theorem: once grand producer completeness and the same-carrier
convergence bridge are available, the obstruction-zero fibers of the major
projections are inhabited on the same residual spine.
-/

noncomputable section

namespace SaturationMonoid
namespace ResidualProjection

open SaturationMonoid.AffineRelaxation
open SaturationMonoid.ComplexityProjection
open SaturationMonoid.StandardModelConstraint
open SaturationMonoid.StandardModelConstraint.RunningSigmaBeta
open SaturationMonoid.GrandUnification

set_option linter.checkUnivs false
set_option linter.defProp false

/-! ## Domain-level zero fibers -/

/-- The zero fiber of a declared grand-domain residual producer. -/
structure GrandDomainObstructionZeroFiber (D : GrandDomain) : Prop where
  producer_certificate :
    GrandDomainProducerCertificate D
  zero_fiber_nonempty :
    Nonempty
      { x : GrandDomainState D //
        (grandDomainCanonicalProducer D).residual x = 0 ∧
          linearResidualTrace
              (grandDomainCanonicalProducer D).keep
              ((grandDomainCanonicalProducer D).residual x) = 0 ∧
          grandDomainEnergy D
              ((grandDomainCanonicalProducer D).residual x) = 0 }

/-- THEOREM 1: the canonical target itself inhabits every grand-domain
obstruction-zero fiber. -/
theorem grandDomainTarget_obstructionZeroFiber
    (C : GrandProducerCompletenessCertificate) (D : GrandDomain) :
    GrandDomainObstructionZeroFiber D := by
  have hres :
      (grandDomainCanonicalProducer D).residual (grandDomainTarget D) = 0 := by
    rw [grandDomainCanonicalProducer_residual_eq]
    ext i
    simp [grandDomainResidual, grandDomainTarget]
  refine
    { producer_certificate := C.domain_inventory D
      zero_fiber_nonempty := ?_ }
  refine ⟨⟨grandDomainTarget D, ?_⟩⟩
  refine ⟨hres, ?_, ?_⟩
  · rw [hres]
    simp [linearResidualTrace]
  · rw [hres]
    exact (grandDomainEnergy_eq_zero_iff_zero_residual D 0).mpr rfl

/-- THEOREM 2: Grand producer completeness yields a nonempty zero fiber in
every declared grand domain. -/
theorem grandProducerCompleteness_zeroFibers
    (C : GrandProducerCompletenessCertificate) :
    ∀ D : GrandDomain, GrandDomainObstructionZeroFiber D :=
  grandDomainTarget_obstructionZeroFiber C

/-! ## SAT phase-obstruction zero fiber -/

/-- SAT-facing zero fiber: a phase-flow state with all clause obstructions and
the shared SAT/Hamiltonian energy readout equal to zero. -/
structure SATPhaseObstructionZeroFiber
    (Clause : Type) (Var : Type) [Fintype Clause] : Prop where
  zero_fiber_nonempty :
    Nonempty
      { S : SATPhaseFlowState Clause Var //
        (∀ c : Clause, S.obstruction c = 0) ∧
          S.energy = 0 ∧
          hamiltonianEnergyReadout S = 0 }

/-- THEOREM 3: threshold collapse inhabits the SAT phase-obstruction zero
fiber for any finite clause surface. -/
theorem satPhaseObstructionZeroFiber_of_grandProducerCompleteness
    (_C : GrandProducerCompletenessCertificate)
    (Clause : Type) (Var : Type) [Fintype Clause] :
    SATPhaseObstructionZeroFiber Clause Var := by
  let S : SATPhaseFlowState Clause Var :=
    { theta := fun _ => 0
      obstruction := fun _ => 0 }
  let Z : SATPhaseFlowState Clause Var := phaseFlowThresholdCollapse S
  refine
    { zero_fiber_nonempty := ?_ }
  refine ⟨⟨Z, ?_⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro c
    exact phaseFlowThresholdCollapse_obstruction S c
  · exact phaseFlowThresholdCollapse_energy_zero S
  · rw [hamiltonianEnergyReadout_eq_satEnergyReadout Z]
    exact phaseFlowThresholdCollapse_energy_zero S

/-! ## Color-loop zero fiber under the same-carrier alpha bridge -/

/-- Color-loop zero fiber produced on the same carrier: trace-exact,
zero-energy, unit-bracket, sigma-atomic, and Lyapunov crossing faces all agree
at the canonical half-rate. -/
structure ColorLoopCarrierZeroFiber : Prop where
  trace_exact :
    ColorLoopTraceExactPrimePairProducer
  zero_energy :
    ColorLoopZeroEnergyPrimePairProducer
  unit_bracket :
    ColorLoopTraceUnitBracketProducer
  sigma_atomic_cover :
    SigmaAtomicSatOrCoversEvenCarrier (1 / 2 : ℝ)
      (ne_of_lt standardHalfRate_lt_one)
  lyapunov_even_crossing :
    ColorLoopTraceLyapunovEvenCrossingProducer (1 / 2 : ℝ)
  su7_filtered_nonobstructed_loops :
    ∀ n : ℕ, 2 <= n ->
      ∃ p q : PrimeExponent,
        ∀ X : HamiltonianSATPhysicalProducerPair (Fin 3) (Fin 3),
          HamiltonianSATCoordinateSpineProducerNailSurface
              standardModelCoordinateSpineSameCarrier X ->
            X.2.2.alphaInverseResidual = -((89000 : ℚ) / 128511) ∧
              X.2.2.yukawaMassOrder =
                [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
              X.2.2.ckmDepthSum = (386 : ℚ) ∧
              betaCoeff qcdBlockIncidenceOneLoopInput = 7 ∧
              SU7ColorAdjointRepresentationFilter
                (primeEdgeColorLoopMatrix n p q) ∧
              ¬ PrimeEdgeColorLoopObstructed n p q

/-- THEOREM 4: grand producer completeness plus the P819 same-carrier
alpha-convergence bridge inhabits the color-loop trace / zero-energy fiber. -/
theorem colorLoopCarrierZeroFiber_of_grandProducerCompleteness
    (C : GrandProducerCompletenessCertificate)
    (hcarrier : AlphaStrongExactResidualRequiresCarrierConvergence) :
    ColorLoopCarrierZeroFiber := by
  have hbridge :
      AlphaStrongExactResidualRequiresCarrierConvergence ↔
        EvenGoldbachStatement :=
    C.alpha_strong_convergence_goldbach_bridge.requires_convergence_iff_goldbach
  have htrace :
      ColorLoopTraceExactPrimePairProducer ↔ EvenGoldbachStatement :=
    C.color_loop_goldbach_zero_fiber_producer.trace_exact_producer_iff_goldbach
  have hzero :
      ColorLoopZeroEnergyPrimePairProducer ↔ EvenGoldbachStatement :=
    C.color_loop_goldbach_zero_fiber_producer.zero_energy_producer_iff_goldbach
  have hgoldbach : EvenGoldbachStatement :=
    hbridge.mp hcarrier
  have Hnail : AlphaStrongConvergentCarrierNail :=
    alphaStrongConvergentCarrierNail_of_requiresConvergence hcarrier
  refine
    { trace_exact := ?_
      zero_energy := ?_
      unit_bracket := ?_
      sigma_atomic_cover := ?_
      lyapunov_even_crossing := ?_
      su7_filtered_nonobstructed_loops := ?_ }
  · exact htrace.mpr hgoldbach
  · exact hzero.mpr hgoldbach
  · exact C.alpha_strong_convergence_goldbach_bridge.convergent_nail_forces_unit_bracket
      Hnail
  · exact C.alpha_strong_convergence_goldbach_bridge.convergent_nail_forces_sigma_atomic_cover
        standardHalfRate_pos standardHalfRate_lt_one Hnail
  · exact C.alpha_strong_convergence_goldbach_bridge.convergent_nail_forces_lyapunov_crossing
        standardHalfRate_pos standardHalfRate_lt_one Hnail
  · exact su7FilteredLoops_of_alphaStrongRequiresConvergence
      (Clause := Fin 3) (Var := Fin 3)
      standardModelCoordinateSpineSameCarrier hcarrier

/-! ## Grand carrier consistency certificate -/

/-- Carrier consistency package: every grand domain has a residual-zero fiber,
SAT has a phase-obstruction zero fiber, and the color-loop Goldbach face has a
trace / zero-energy zero fiber on the same carrier. -/
structure GrandCarrierConsistencyZeroFiberCertificate : Prop where
  grand_domain_zero_fibers :
    ∀ D : GrandDomain, GrandDomainObstructionZeroFiber D
  sat_phase_zero_fibers :
    ∀ {Clause Var : Type} [Fintype Clause],
      SATPhaseObstructionZeroFiber Clause Var
  canonical_sat_phase_zero_fiber :
    SATPhaseObstructionZeroFiber (Fin 3) (Fin 3)
  color_loop_zero_fiber :
    ColorLoopCarrierZeroFiber
  color_loop_zero_fiber_forces_goldbach :
    EvenGoldbachStatement
  alpha_convergence_iff_goldbach :
    AlphaStrongExactResidualRequiresCarrierConvergence ↔
      EvenGoldbachStatement

/-- THEOREM 5: carrier consistency theorem.

If the grand producer inventory is complete and the exact alpha residual is
required to converge on the same carrier, then every declared grand domain has
a nonempty obstruction-zero fiber; the SAT projection has a phase-obstruction
zero fiber; and the Goldbach/color-loop projection has trace-exact and
zero-energy fibers. -/
theorem grandProducerCompleteness_carrierConsistencyZeroFibers
    (C : GrandProducerCompletenessCertificate)
    (hcarrier : AlphaStrongExactResidualRequiresCarrierConvergence) :
    GrandCarrierConsistencyZeroFiberCertificate where
  grand_domain_zero_fibers :=
    grandProducerCompleteness_zeroFibers C
  sat_phase_zero_fibers := by
    intro Clause Var _
    exact satPhaseObstructionZeroFiber_of_grandProducerCompleteness C Clause Var
  canonical_sat_phase_zero_fiber :=
    satPhaseObstructionZeroFiber_of_grandProducerCompleteness C (Fin 3) (Fin 3)
  color_loop_zero_fiber :=
    colorLoopCarrierZeroFiber_of_grandProducerCompleteness C hcarrier
  color_loop_zero_fiber_forces_goldbach :=
    C.alpha_strong_convergence_goldbach_bridge.requires_convergence_iff_goldbach.mp
      hcarrier
  alpha_convergence_iff_goldbach :=
    C.alpha_strong_convergence_goldbach_bridge.requires_convergence_iff_goldbach

end ResidualProjection
end SaturationMonoid
