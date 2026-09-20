import H0mework.Realization.Faces.P820

/-!
# Proposition 821: removing the P820 carrier hypothesis is exactly Goldbach

P820 packages the desired carrier-consistency conclusion, but its color-loop
leg still requires

`AlphaStrongExactResidualRequiresCarrierConvergence`.

This file records the pressure point cleanly.  The no-extra-hypothesis version
of P820 is not a harmless packaging improvement: it is exactly the Goldbach
producer, equivalently the same-carrier alpha convergence producer from P819.

Thus the next producer debt is explicit:

* SAT phase zero fibers are already unconditional in the current formal model;
* declared grand-domain target zero fibers are already unconditional;
* the color-loop / Goldbach zero fiber is the remaining nontrivial inhabitance
  producer.
-/

noncomputable section

namespace SaturationMonoid
namespace ResidualProjection

open SaturationMonoid.AffineRelaxation
open SaturationMonoid.GrandUnification

set_option linter.checkUnivs false
set_option linter.defProp false

/-! ## The exact strength of P820 without `hcarrier` -/

/-- THEOREM 1: for any grand-completeness certificate, P820's full carrier
consistency package is equivalent to the same-carrier alpha convergence
producer. -/
theorem grandCarrierConsistencyZeroFibers_iff_alphaConvergence
    (C : GrandProducerCompletenessCertificate) :
    GrandCarrierConsistencyZeroFiberCertificate ↔
      AlphaStrongExactResidualRequiresCarrierConvergence := by
  constructor
  · intro H
    exact H.alpha_convergence_iff_goldbach.mpr
      H.color_loop_zero_fiber_forces_goldbach
  · intro hcarrier
    exact grandProducerCompleteness_carrierConsistencyZeroFibers C hcarrier

/-- THEOREM 2: for any grand-completeness certificate, P820's full carrier
consistency package is equivalent to ordinary even Goldbach.  This is the
precise reason the `hcarrier` hypothesis cannot be deleted by repackaging. -/
theorem grandCarrierConsistencyZeroFibers_iff_evenGoldbach
    (C : GrandProducerCompletenessCertificate) :
    GrandCarrierConsistencyZeroFiberCertificate ↔
      EvenGoldbachStatement := by
  constructor
  · intro H
    exact H.color_loop_zero_fiber_forces_goldbach
  · intro hgoldbach
    have hcarrier : AlphaStrongExactResidualRequiresCarrierConvergence :=
      C.alpha_strong_convergence_goldbach_bridge.requires_convergence_iff_goldbach.mpr
        hgoldbach
    exact grandProducerCompleteness_carrierConsistencyZeroFibers C hcarrier

/-- THEOREM 3: the globally quantified "GrandProducerCompleteness implies
carrier consistency with no extra assumption" statement is exactly Goldbach.

The forward direction instantiates the claim at the canonical grand certificate.
The reverse direction uses P820 after transporting Goldbach through P819. -/
theorem grandProducerCompleteness_unconditionalCarrierConsistency_iff_goldbach :
    (∀ _C : GrandProducerCompletenessCertificate,
        GrandCarrierConsistencyZeroFiberCertificate) ↔
      EvenGoldbachStatement := by
  constructor
  · intro h
    exact
      (h grandProducerCompletenessCertificate).color_loop_zero_fiber_forces_goldbach
  · intro hgoldbach C
    exact (grandCarrierConsistencyZeroFibers_iff_evenGoldbach C).mpr
      hgoldbach

/-! ## The already-unconditional faces -/

/-- THEOREM 4: the SAT phase-obstruction zero fiber is already unconditional
under grand completeness in the current formal model. -/
theorem grandProducerCompleteness_satPhaseZeroFibers_unconditional
    (C : GrandProducerCompletenessCertificate) :
    ∀ {Clause Var : Type} [Fintype Clause],
      SATPhaseObstructionZeroFiber Clause Var := by
  intro Clause Var _
  exact satPhaseObstructionZeroFiber_of_grandProducerCompleteness C Clause Var

/-- THEOREM 5: the declared grand-domain target zero fibers are already
unconditional under grand completeness. -/
theorem grandProducerCompleteness_domainZeroFibers_unconditional
    (C : GrandProducerCompletenessCertificate) :
    ∀ D : GrandDomain, GrandDomainObstructionZeroFiber D :=
  grandProducerCompleteness_zeroFibers C

end ResidualProjection
end SaturationMonoid
