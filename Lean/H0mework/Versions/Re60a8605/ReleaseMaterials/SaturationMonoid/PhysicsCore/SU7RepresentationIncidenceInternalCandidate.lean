import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.PhysicsCore.PhysicalSourcePullback
import H0mework.Physics.RepresentationSources.P462
import H0mework.Physics.JointSources.P523

/-!
# Conditional reference-SM incidence/running candidates

This module reads the conditional P523 reference receipt into the old internal
candidate interface.  Its dependency graph contains the finite
representation/incidence arithmetic and the target-free candidate interface
only.  It does not import a metric, Hodge, Plebanski variation system,
stationary family, or terminal hard gate.

The output consists of the chosen six-incidence reference carrier and the
three one-loop coupling-normalization coefficients computed from its trace
input.  All three coefficients are proved nonzero and therefore have
canonical units in `ℚˣ`.  Those are conditional reference-running units, not
measured reference-scale `g_i^2` units and not outputs of the actual P286
matter action.
-/

namespace SaturationMonoid
namespace PhysicsCore
namespace SU7RepresentationIncidenceInternalCandidate

open StandardModelConstraint
open StandardModelConstraint.RunningSigmaBeta

noncomputable section

/-- Coupling-normalization data computed from the six-incidence trace
carrier.  These are one-loop coefficients, not supplied low-energy coupling
constants. -/
structure IncidenceCouplingNormalizationCandidate where
  asymptoticB0 : StandardModelGaugeFactor → ℚ
  betaTableCoefficient : StandardModelGaugeFactor → ℚ
  asymptoticB0_generated :
    ∀ factor,
      asymptoticB0 factor =
        betaCoeff (incidenceCarrierTraceInput factor)
  betaTableCoefficient_generated :
    ∀ factor,
      betaTableCoefficient factor = -asymptoticB0 factor
  asymptoticB0_ne_zero :
    ∀ factor, asymptoticB0 factor ≠ 0

/-- Canonical one-loop normalization candidate computed directly from the
incidence carrier trace. -/
def incidenceCouplingNormalizationCandidate :
    IncidenceCouplingNormalizationCandidate where
  asymptoticB0 := fun factor =>
    betaCoeff (incidenceCarrierTraceInput factor)
  betaTableCoefficient := fun factor =>
    -(betaCoeff (incidenceCarrierTraceInput factor))
  asymptoticB0_generated := by
    intro factor
    rfl
  betaTableCoefficient_generated := by
    intro factor
    rfl
  asymptoticB0_ne_zero := by
    intro factor
    rw [standardModel_b0_from_block_incidence_carrier factor]
    cases factor with
    | colorSU3 =>
        rw [standardModelAsymptoticB0_color]
        norm_num
    | weakSU2 =>
        rw [standardModelAsymptoticB0_weak]
        norm_num
    | hyperchargeU1 =>
        rw [standardModelAsymptoticB0_hypercharge]
        norm_num

namespace IncidenceCouplingNormalizationCandidate

/-- A canonical nonzero rational normalization unit.  No choice of a physical
reference-scale coupling is made here. -/
def asymptoticB0Unit
    (candidate : IncidenceCouplingNormalizationCandidate)
    (factor : StandardModelGaugeFactor) : ℚˣ :=
  Units.mk0 (candidate.asymptoticB0 factor)
    (candidate.asymptoticB0_ne_zero factor)

@[simp] theorem coe_asymptoticB0Unit
    (candidate : IncidenceCouplingNormalizationCandidate)
    (factor : StandardModelGaugeFactor) :
    (candidate.asymptoticB0Unit factor : ℚ) =
      candidate.asymptoticB0 factor :=
  rfl

theorem betaTableCoefficient_ne_zero
    (candidate : IncidenceCouplingNormalizationCandidate)
    (factor : StandardModelGaugeFactor) :
    candidate.betaTableCoefficient factor ≠ 0 := by
  rw [candidate.betaTableCoefficient_generated factor]
  exact neg_ne_zero.mpr (candidate.asymptoticB0_ne_zero factor)

end IncidenceCouplingNormalizationCandidate

theorem incidenceCouplingNormalization_asymptotic_eq_standard
    (factor : StandardModelGaugeFactor) :
    incidenceCouplingNormalizationCandidate.asymptoticB0 factor =
      standardModelAsymptoticB0 factor :=
  standardModel_b0_from_block_incidence_carrier factor

theorem incidenceCouplingNormalization_betaTable_eq_standard
    (factor : StandardModelGaugeFactor) :
    incidenceCouplingNormalizationCandidate.betaTableCoefficient factor =
      standardModelBetaCoefficient factor :=
  standardModel_betaTableCoeff_from_block_incidence_carrier factor

abbrev ReferenceSMRepresentationIncidenceSource :=
  StandardModelConstraint.SU7RepresentationPhysicalizationReceipt

/-- Compatibility alias.  This is a conditional reference source, not an
actual SU(7) representation-restriction producer. -/
abbrev RepresentationIncidenceSource :=
  ReferenceSMRepresentationIncidenceSource

/-- The reference axis reads the chosen carrier from a conditional P523
receipt and computes the associated finite one-loop table. -/
def representationIncidenceCandidateAxis :
    InternalConstitutiveCandidateAxis ReferenceSMRepresentationIncidenceSource
      SU7BlockIncidenceMatterCarrierCertificate
      IncidenceCouplingNormalizationCandidate where
  candidateOf := fun source =>
    { internalConstitutive := source.matter_carrier
      couplingNormalization := incidenceCouplingNormalizationCandidate }

/-- Reference-axis readout theorem.  The result fields are read from the
conditional receipt; this is not a proof that the actual P286 action generates
that receipt. -/
theorem representationIncidence_generates_internalConstitutiveCandidates
    (source : ReferenceSMRepresentationIncidenceSource) :
    (representationIncidenceCandidateAxis.candidateOf source
        ).internalConstitutive = source.matter_carrier ∧
      (representationIncidenceCandidateAxis.candidateOf source
        ).couplingNormalization =
          incidenceCouplingNormalizationCandidate :=
  ⟨rfl, rfl⟩

/-- The same source-axis construction exposes three canonical nonzero
normalization units.  This is deliberately weaker than producing physical
reference-scale coupling squares. -/
theorem representationIncidence_generates_nonzeroNormalizationUnits
    (source : ReferenceSMRepresentationIncidenceSource)
    (factor : StandardModelGaugeFactor) :
    let candidate :=
      (representationIncidenceCandidateAxis.candidateOf source
        ).couplingNormalization
    (candidate.asymptoticB0Unit factor : ℚ) =
        betaCoeff (incidenceCarrierTraceInput factor) ∧
      (candidate.asymptoticB0Unit factor : ℚ) ≠ 0 := by
  dsimp only
  exact ⟨rfl, incidenceCouplingNormalizationCandidate.asymptoticB0_ne_zero
    factor⟩

def referenceSMRepresentationIncidenceSource :
    ReferenceSMRepresentationIncidenceSource :=
  StandardModelConstraint.referenceSMRepresentationPhysicalizationReceipt

/-- Compatibility name for the conditional reference source. -/
abbrev canonicalRepresentationIncidenceSource :=
  referenceSMRepresentationIncidenceSource

def referenceSMInternalConstitutiveCandidate :
    InternalConstitutiveCandidate
      SU7BlockIncidenceMatterCarrierCertificate
      IncidenceCouplingNormalizationCandidate :=
  representationIncidenceCandidateAxis.candidateOf
    referenceSMRepresentationIncidenceSource

/-- Compatibility name for the conditional reference candidate. -/
abbrev canonicalInternalConstitutiveCandidate :=
  referenceSMInternalConstitutiveCandidate

theorem canonicalInternalCandidate_has_standard_oneLoopCoefficients
    (factor : StandardModelGaugeFactor) :
    canonicalInternalConstitutiveCandidate.couplingNormalization.asymptoticB0
        factor =
      standardModelAsymptoticB0 factor ∧
    canonicalInternalConstitutiveCandidate.couplingNormalization.betaTableCoefficient
        factor =
      standardModelBetaCoefficient factor :=
  ⟨incidenceCouplingNormalization_asymptotic_eq_standard factor,
    incidenceCouplingNormalization_betaTable_eq_standard factor⟩

end
end SU7RepresentationIncidenceInternalCandidate
end PhysicsCore
end SaturationMonoid
