import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import H0mework.Foundation.Source.AccountedUnfolding

/-!
# Root-generated cofinal quadratic evaluation

This is the root-owned replacement for a caller-supplied height family.  A
source exposes actual point, multiplication-orbit and local-incidence atoms.
The only finite scalar evaluation is the canonical additive fold of those
incidences.  Pointwise Cauchy convergence and vanishing finite scalar/polar
defects then generate the cofinal value and its `QuadraticForm` structure.

The public face accepts no canonical value, quadraticity, bilinearity,
symmetry, pairing matrix, basis or determinant.  Its finite observations use
the existing RootedAccountedUnfolding constructor and do not store a completed
future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalQuadraticEvaluation

open Filter
open RootedAccountedUnfolding
open scoped Topology

attribute [local instance 2000] Algebra.toModule

universe t u v w p q r

/-- Canonical evaluation of one finite local-incidence occurrence.  The
caller supplies local incidence values, not an arbitrary tree algebra: child
contributions are combined by addition. -/
def accountedIncidenceEvaluation
    {K : Type t} {Incidence : Type p} {V : Type v}
    [AddCommMonoid K]
    (localEvaluation : Incidence → V → K)
    (exposure : RootedAccountedUnfolding Incidence)
    (point : V) : K :=
  exposure.fold fun incidence children =>
    localEvaluation incidence point + children.sum

/-- Source-fixed finite evaluation dynamics.  The asymptotic laws are local
recurrence obligations; no completed quadratic output occurs in this type. -/
structure CofinalQuadraticRecurrence
    (K : Type t) (State : Type u) (V : Type v) (Incidence : Type p)
    [NontriviallyNormedField K] [CompleteSpace K] [Algebra ℤ K]
    [AddCommGroup V] where
  seed : State
  advance : State → State
  incidenceExposure : State → V → RootedAccountedUnfolding Incidence
  localEvaluation : Incidence → V → K
  pointwiseCauchy :
    ∀ point, CauchySeq fun stage =>
      accountedIncidenceEvaluation localEvaluation
        (incidenceExposure ((advance^[stage]) seed) point) point
  smulDefect_tendsto_zero :
    ∀ (integer : ℤ) (point : V),
      Tendsto
        (fun stage =>
          accountedIncidenceEvaluation localEvaluation
                (incidenceExposure ((advance^[stage]) seed) (integer • point))
                (integer • point) -
            algebraMap ℤ K (integer * integer) *
              accountedIncidenceEvaluation localEvaluation
                (incidenceExposure ((advance^[stage]) seed) point) point)
        atTop (𝓝 0)
  polarAddDefect_tendsto_zero :
    ∀ (left right point : V),
      Tendsto
        (fun stage =>
          (accountedIncidenceEvaluation localEvaluation
                (incidenceExposure ((advance^[stage]) seed)
                  ((left + right) + point))
                ((left + right) + point) -
              accountedIncidenceEvaluation localEvaluation
                (incidenceExposure ((advance^[stage]) seed) (left + right))
                (left + right) -
              accountedIncidenceEvaluation localEvaluation
                (incidenceExposure ((advance^[stage]) seed) point) point) -
            ((accountedIncidenceEvaluation localEvaluation
                  (incidenceExposure ((advance^[stage]) seed) (left + point))
                  (left + point) -
                accountedIncidenceEvaluation localEvaluation
                  (incidenceExposure ((advance^[stage]) seed) left) left -
                accountedIncidenceEvaluation localEvaluation
                  (incidenceExposure ((advance^[stage]) seed) point) point) +
              (accountedIncidenceEvaluation localEvaluation
                  (incidenceExposure ((advance^[stage]) seed) (right + point))
                  (right + point) -
                accountedIncidenceEvaluation localEvaluation
                  (incidenceExposure ((advance^[stage]) seed) right) right -
                accountedIncidenceEvaluation localEvaluation
                  (incidenceExposure ((advance^[stage]) seed) point) point)))
        atTop (𝓝 0)
  polarSmulDefect_tendsto_zero :
    ∀ (integer : ℤ) (left right : V),
      Tendsto
        (fun stage =>
          (accountedIncidenceEvaluation localEvaluation
                (incidenceExposure ((advance^[stage]) seed)
                  (integer • left + right))
                (integer • left + right) -
              accountedIncidenceEvaluation localEvaluation
                (incidenceExposure ((advance^[stage]) seed) (integer • left))
                (integer • left) -
              accountedIncidenceEvaluation localEvaluation
                (incidenceExposure ((advance^[stage]) seed) right) right) -
            algebraMap ℤ K integer *
              (accountedIncidenceEvaluation localEvaluation
                  (incidenceExposure ((advance^[stage]) seed) (left + right))
                  (left + right) -
                accountedIncidenceEvaluation localEvaluation
                  (incidenceExposure ((advance^[stage]) seed) left) left -
                accountedIncidenceEvaluation localEvaluation
                  (incidenceExposure ((advance^[stage]) seed) right) right))
        atTop (𝓝 0)

namespace CofinalQuadraticRecurrence

variable {K : Type t} {State : Type u} {V : Type v} {Incidence : Type p}
variable [NontriviallyNormedField K] [CompleteSpace K] [Algebra ℤ K]
variable [AddCommGroup V]

def stateAt (recurrence : CofinalQuadraticRecurrence K State V Incidence)
    (stage : Nat) : State :=
  (recurrence.advance^[stage]) recurrence.seed

def stageValue (recurrence : CofinalQuadraticRecurrence K State V Incidence)
    (stage : Nat) (point : V) : K :=
  accountedIncidenceEvaluation recurrence.localEvaluation
    (recurrence.incidenceExposure (recurrence.stateAt stage) point) point

/-- The cofinal value is calculated from the source recurrence. -/
noncomputable def cofinalValue
    (recurrence : CofinalQuadraticRecurrence K State V Incidence)
    (point : V) : K :=
  limUnder atTop fun stage => recurrence.stageValue stage point

theorem stageValue_tendsto
    (recurrence : CofinalQuadraticRecurrence K State V Incidence) (point : V) :
    Tendsto (fun stage => recurrence.stageValue stage point)
      atTop (𝓝 (recurrence.cofinalValue point)) :=
  recurrence.pointwiseCauchy point |>.tendsto_limUnder

omit [CompleteSpace K] [Algebra ℤ K] in
private theorem limit_eq_of_sub_tendsto_zero
    {left right : Nat → K} {leftLimit rightLimit : K}
    (left_tendsto : Tendsto left atTop (𝓝 leftLimit))
    (right_tendsto : Tendsto right atTop (𝓝 rightLimit))
    (difference_tendsto :
      Tendsto (fun stage => left stage - right stage) atTop (𝓝 0)) :
    leftLimit = rightLimit := by
  have difference_limit :
      Tendsto (fun stage => left stage - right stage)
        atTop (𝓝 (leftLimit - rightLimit)) :=
    left_tendsto.sub right_tendsto
  exact sub_eq_zero.mp
    (tendsto_nhds_unique difference_limit difference_tendsto)

theorem cofinalValue_smul
    (recurrence : CofinalQuadraticRecurrence K State V Incidence)
    (integer : ℤ) (point : V) :
    recurrence.cofinalValue (integer • point) =
      algebraMap ℤ K (integer * integer) *
        recurrence.cofinalValue point := by
  apply limit_eq_of_sub_tendsto_zero
    (recurrence.stageValue_tendsto (integer • point))
    ((recurrence.stageValue_tendsto point).const_mul
      (algebraMap ℤ K (integer * integer)))
  simpa only [stageValue, stateAt] using
    recurrence.smulDefect_tendsto_zero integer point

def stagePolar (recurrence : CofinalQuadraticRecurrence K State V Incidence)
    (stage : Nat) (left right : V) : K :=
  recurrence.stageValue stage (left + right) -
    recurrence.stageValue stage left -
    recurrence.stageValue stage right

theorem stagePolar_tendsto
    (recurrence : CofinalQuadraticRecurrence K State V Incidence)
    (left right : V) :
    Tendsto (fun stage => recurrence.stagePolar stage left right)
      atTop
      (𝓝 (QuadraticMap.polar recurrence.cofinalValue left right)) := by
  simpa only [stagePolar, QuadraticMap.polar] using
    ((recurrence.stageValue_tendsto (left + right)).sub
      (recurrence.stageValue_tendsto left)).sub
        (recurrence.stageValue_tendsto right)

theorem cofinalPolar_add_left
    (recurrence : CofinalQuadraticRecurrence K State V Incidence)
    (left right point : V) :
    QuadraticMap.polar recurrence.cofinalValue (left + right) point =
      QuadraticMap.polar recurrence.cofinalValue left point +
        QuadraticMap.polar recurrence.cofinalValue right point := by
  apply limit_eq_of_sub_tendsto_zero
    (recurrence.stagePolar_tendsto (left + right) point)
    ((recurrence.stagePolar_tendsto left point).add
      (recurrence.stagePolar_tendsto right point))
  simpa only [stagePolar, stageValue, stateAt] using
    recurrence.polarAddDefect_tendsto_zero left right point

theorem cofinalPolar_smul_left
    (recurrence : CofinalQuadraticRecurrence K State V Incidence)
    (integer : ℤ) (left right : V) :
    QuadraticMap.polar recurrence.cofinalValue (integer • left) right =
      algebraMap ℤ K integer *
        QuadraticMap.polar recurrence.cofinalValue left right := by
  apply limit_eq_of_sub_tendsto_zero
    (recurrence.stagePolar_tendsto (integer • left) right)
    ((recurrence.stagePolar_tendsto left right).const_mul
      (algebraMap ℤ K integer))
  simpa only [stagePolar, stageValue, stateAt] using
    recurrence.polarSmulDefect_tendsto_zero integer left right

/-- Canonical quadratic state generated from the recurrence. -/
noncomputable def quadraticState
    (recurrence : CofinalQuadraticRecurrence K State V Incidence) :
    QuadraticMap ℤ V K :=
  QuadraticMap.ofPolar recurrence.cofinalValue
    (fun integer point => by
      simpa only [Algebra.smul_def] using
        recurrence.cofinalValue_smul integer point)
    recurrence.cofinalPolar_add_left
    (fun integer left right => by
      simpa only [Algebra.smul_def] using
        recurrence.cofinalPolar_smul_left integer left right)

end CofinalQuadraticRecurrence

/-- Exact authority face generated from the actual motive, polarization,
point, multiplication-orbit and local-incidence occurrences.  It is
deliberately independent of topology and scalar realization, and contains no
height value or completed future. -/
structure RootGeneratedCofinalQuadraticEvaluationAt
    {Root : Type w} {Polarization : Type q} {V : Type v}
    {Orbit : Type r} {Incidence : Type p}
    (rootOccurrence : RootedAccountedUnfolding Root)
    (polarizationOccurrence : RootedAccountedUnfolding Polarization)
    (pointOccurrences : V → RootedAccountedUnfolding V)
    (multiplicationOrbitOccurrence : RootedAccountedUnfolding Orbit)
    (localIncidenceOccurrence : V → RootedAccountedUnfolding Incidence) : Type where
  private mk ::

namespace RootGeneratedCofinalQuadraticEvaluationAt

variable {Root : Type w} {Polarization : Type q} {V : Type v}
variable {Orbit : Type r} {Incidence : Type p}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {polarizationOccurrence : RootedAccountedUnfolding Polarization}
variable {pointOccurrences : V → RootedAccountedUnfolding V}
variable {multiplicationOrbitOccurrence : RootedAccountedUnfolding Orbit}
variable {localIncidenceOccurrence : V → RootedAccountedUnfolding Incidence}

def generate :
    RootGeneratedCofinalQuadraticEvaluationAt rootOccurrence
      polarizationOccurrence pointOccurrences multiplicationOrbitOccurrence
      localIncidenceOccurrence :=
  ⟨⟩

def root
    (_face : RootGeneratedCofinalQuadraticEvaluationAt rootOccurrence
      polarizationOccurrence pointOccurrences multiplicationOrbitOccurrence
      localIncidenceOccurrence) :
    RootedAccountedUnfolding Root :=
  rootOccurrence

def polarization
    (_face : RootGeneratedCofinalQuadraticEvaluationAt rootOccurrence
      polarizationOccurrence pointOccurrences multiplicationOrbitOccurrence
      localIncidenceOccurrence) :
    RootedAccountedUnfolding Polarization :=
  polarizationOccurrence

def points
    (_face : RootGeneratedCofinalQuadraticEvaluationAt rootOccurrence
      polarizationOccurrence pointOccurrences multiplicationOrbitOccurrence
      localIncidenceOccurrence) :
    V → RootedAccountedUnfolding V :=
  pointOccurrences

def multiplicationOrbit
    (_face : RootGeneratedCofinalQuadraticEvaluationAt rootOccurrence
      polarizationOccurrence pointOccurrences multiplicationOrbitOccurrence
      localIncidenceOccurrence) :
    RootedAccountedUnfolding Orbit :=
  multiplicationOrbitOccurrence

def localIncidences
    (_face : RootGeneratedCofinalQuadraticEvaluationAt rootOccurrence
      polarizationOccurrence pointOccurrences multiplicationOrbitOccurrence
      localIncidenceOccurrence) :
    V → RootedAccountedUnfolding Incidence :=
  localIncidenceOccurrence

end RootGeneratedCofinalQuadraticEvaluationAt

/-- T1 realization of the structural authority face.  Its recurrence is
anchored at the exact local-incidence occurrence, after which every finite
stage is produced by `advance` and evaluated by the canonical additive fold.
This structure is a mathematical realization/readout and carries no root
authority of its own. -/
structure RootGeneratedCofinalQuadraticRealizationAt
    {K : Type t} {Root : Type w} {V : Type v}
    {Polarization : Type q} {Orbit : Type r} {Incidence : Type p}
    [NontriviallyNormedField K] [CompleteSpace K] [Algebra ℤ K]
    [AddCommGroup V]
    {rootOccurrence : RootedAccountedUnfolding Root}
    {polarizationOccurrence : RootedAccountedUnfolding Polarization}
    {pointOccurrences : V → RootedAccountedUnfolding V}
    {multiplicationOrbitOccurrence : RootedAccountedUnfolding Orbit}
    {localIncidenceOccurrence : V → RootedAccountedUnfolding Incidence}
    (evaluationFace : RootGeneratedCofinalQuadraticEvaluationAt rootOccurrence
      polarizationOccurrence pointOccurrences multiplicationOrbitOccurrence
      localIncidenceOccurrence)
    (recurrence : CofinalQuadraticRecurrence K Orbit V Incidence) : Type where
  private mk ::
  seed_eq : recurrence.seed = multiplicationOrbitOccurrence.root
  seedExposure_eq :
    ∀ point, recurrence.incidenceExposure recurrence.seed point =
      localIncidenceOccurrence point

namespace RootGeneratedCofinalQuadraticRealizationAt

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

def realize
    (seed_eq : recurrence.seed = multiplicationOrbitOccurrence.root)
    (seedExposure_eq :
      ∀ point, recurrence.incidenceExposure recurrence.seed point =
        localIncidenceOccurrence point) :
    RootGeneratedCofinalQuadraticRealizationAt evaluationFace recurrence :=
  ⟨seed_eq, seedExposure_eq⟩

noncomputable def quadraticState
    (_realization :
      RootGeneratedCofinalQuadraticRealizationAt evaluationFace recurrence) :
    QuadraticMap ℤ V K :=
  recurrence.quadraticState

end RootGeneratedCofinalQuadraticRealizationAt

end CofinalQuadraticEvaluation
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
