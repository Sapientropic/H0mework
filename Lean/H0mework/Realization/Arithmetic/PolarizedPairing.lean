import H0mework.Realization.Arithmetic.CofinalQuadratic

/-!
# Root-generated polarized pairing

The cofinal quadratic state generates its polarization.  Bilinearity and
symmetry are theorems of the quadratic state; neither is accepted as a
premise, and no matrix or basis occurs in the producer face.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace PolarizedPairing

open CofinalQuadraticEvaluation

attribute [local instance 2000] Algebra.toModule

universe t u v w p q r

/-- A root-owned pairing face is a dependent face of the exact cofinal
quadratic occurrence.  It stores no form, bilinearity or symmetry premise. -/
structure RootGeneratedPolarizedPairingAt
    {Root : Type w} {Polarization : Type q} {V : Type v}
    {Orbit : Type r} {Incidence : Type p}
    {rootOccurrence : RootedAccountedUnfolding Root}
    {polarizationOccurrence : RootedAccountedUnfolding Polarization}
    {pointOccurrences : V → RootedAccountedUnfolding V}
    {multiplicationOrbitOccurrence : RootedAccountedUnfolding Orbit}
    {localIncidenceOccurrence : V → RootedAccountedUnfolding Incidence}
    (evaluationFace : RootGeneratedCofinalQuadraticEvaluationAt rootOccurrence
      polarizationOccurrence pointOccurrences multiplicationOrbitOccurrence
      localIncidenceOccurrence) : Type where
  private mk ::

namespace RootGeneratedPolarizedPairingAt

variable {Root : Type w} {Polarization : Type q} {V : Type v}
variable {Orbit : Type r} {Incidence : Type p}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {polarizationOccurrence : RootedAccountedUnfolding Polarization}
variable {pointOccurrences : V → RootedAccountedUnfolding V}
variable {multiplicationOrbitOccurrence : RootedAccountedUnfolding Orbit}
variable {localIncidenceOccurrence : V → RootedAccountedUnfolding Incidence}
variable {evaluationFace : RootGeneratedCofinalQuadraticEvaluationAt
  rootOccurrence polarizationOccurrence pointOccurrences
  multiplicationOrbitOccurrence localIncidenceOccurrence}

def generate : RootGeneratedPolarizedPairingAt evaluationFace :=
  ⟨⟩

def evaluation
    (_face : RootGeneratedPolarizedPairingAt evaluationFace) :=
  evaluationFace

end RootGeneratedPolarizedPairingAt

/-- Mathematical realization of the structural pairing face.  The bilinear
form is calculated from the already generated cofinal quadratic state. -/
structure RootGeneratedPolarizedPairingRealizationAt
    {K : Type t} {Root : Type w} {V : Type v}
    {Polarization : Type q} {Orbit : Type r} {Incidence : Type p}
    [NontriviallyNormedField K] [CompleteSpace K] [Algebra ℤ K]
    [AddCommGroup V]
    {rootOccurrence : RootedAccountedUnfolding Root}
    {polarizationOccurrence : RootedAccountedUnfolding Polarization}
    {pointOccurrences : V → RootedAccountedUnfolding V}
    {multiplicationOrbitOccurrence : RootedAccountedUnfolding Orbit}
    {localIncidenceOccurrence : V → RootedAccountedUnfolding Incidence}
    {evaluationFace : RootGeneratedCofinalQuadraticEvaluationAt rootOccurrence
      polarizationOccurrence pointOccurrences multiplicationOrbitOccurrence
      localIncidenceOccurrence}
    {recurrence : CofinalQuadraticRecurrence K Orbit V Incidence}
    (pairingFace : RootGeneratedPolarizedPairingAt evaluationFace)
    (evaluationRealization :
      RootGeneratedCofinalQuadraticRealizationAt evaluationFace recurrence) : Type where
  private mk ::

namespace RootGeneratedPolarizedPairingRealizationAt

variable {K : Type t} {Root : Type w} {V : Type v}
variable {Polarization : Type q} {Orbit : Type r} {Incidence : Type p}
variable [NontriviallyNormedField K] [CompleteSpace K] [Algebra ℤ K]
variable [AddCommGroup V]
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {polarizationOccurrence : RootedAccountedUnfolding Polarization}
variable {pointOccurrences : V → RootedAccountedUnfolding V}
variable {multiplicationOrbitOccurrence : RootedAccountedUnfolding Orbit}
variable {localIncidenceOccurrence : V → RootedAccountedUnfolding Incidence}
variable {evaluationFace : RootGeneratedCofinalQuadraticEvaluationAt
  rootOccurrence polarizationOccurrence pointOccurrences
  multiplicationOrbitOccurrence localIncidenceOccurrence}
variable {recurrence : CofinalQuadraticRecurrence K Orbit V Incidence}
variable {pairingFace : RootGeneratedPolarizedPairingAt evaluationFace}
variable {evaluationRealization :
  RootGeneratedCofinalQuadraticRealizationAt evaluationFace recurrence}

def realize : RootGeneratedPolarizedPairingRealizationAt
    pairingFace evaluationRealization :=
  ⟨⟩

/-- Polarization readout generated from the canonical quadratic state. -/
noncomputable def pairing
    (_realization : RootGeneratedPolarizedPairingRealizationAt
      pairingFace evaluationRealization) :
    LinearMap.BilinMap ℤ V K :=
  evaluationRealization.quadraticState.polarBilin

theorem pairing_apply
    (realization : RootGeneratedPolarizedPairingRealizationAt
      pairingFace evaluationRealization)
    (left right : V) :
    realization.pairing left right =
      evaluationRealization.quadraticState (left + right) -
        evaluationRealization.quadraticState left -
        evaluationRealization.quadraticState right :=
  rfl

theorem pairing_symmetric
    (realization : RootGeneratedPolarizedPairingRealizationAt
      pairingFace evaluationRealization)
    (left right : V) :
    realization.pairing left right = realization.pairing right left :=
  QuadraticMap.polar_comm evaluationRealization.quadraticState left right

theorem pairing_add_left
    (realization : RootGeneratedPolarizedPairingRealizationAt
      pairingFace evaluationRealization)
    (left right point : V) :
    realization.pairing (left + right) point =
      realization.pairing left point + realization.pairing right point :=
  LinearMap.congr_fun (map_add realization.pairing left right) point

theorem pairing_add_right
    (realization : RootGeneratedPolarizedPairingRealizationAt
      pairingFace evaluationRealization)
    (left right point : V) :
    realization.pairing point (left + right) =
      realization.pairing point left + realization.pairing point right :=
  map_add (realization.pairing point) left right

end RootGeneratedPolarizedPairingRealizationAt

end PolarizedPairing
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
