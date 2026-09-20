import H0mework.Physics.Dirac.PhysicalBivectorSpinRepresentation
import H0mework.Physics.GravitySource.Obstruction

/-!
# S9-C3g6b: canonical Spin-orbit responsibility carrier

C3g5 generated one actual nonzero gravity-mouth residual, and C3g6a derived
the actual `SpinPlus13` representation on its ambient `PhysicalBivector`
carrier.  This module takes the orbit of that residual and then its real
linear span.  Thus the carrier is an output of the existing obstruction and
representation; it is not a preselected field, source slot, coupling,
normalization, branch receipt, or supplied covariance certificate.

The orbit span is proved stable under the actual action and minimal among real
submodules that contain the obstruction and have that stability.  The action
restricts to a representation on the derived subtype.  The same source sigma
then supplies the scalar keep `K`; both `K` and the forced `(I-K)` trace commute
with the restricted action.  On this covariant responsibility carrier the
framework equations remain literal:

`r' = K r`, `r = K r + (I-K) r`, `trace = (I-K) r`.

Active transport and the nonzero obstruction again rule out a fixed or
traceless naked residual sink.  The norm square below is only a positive
zero-detecting readout; no Lorentz-invariance claim is made for that norm.

This checkpoint does not prove equivariance of the source-to-obstruction
builder, a source-generated holonomic configuration successor, or the typed
bridge to the separate pre-P950 source-state continuation law.  Consequently
the orbit span is named a responsibility carrier, not a new repair field or a
completed Layer-3 producer.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNinePositiveSourceGravityMouthSpinOrbitCarrier

open AffineRelaxation
open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalBundle
open StageNinePhysicalBivectorSpinRepresentation
open StageNinePositiveSourceGravityMouthObstruction
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization

noncomputable section

set_option autoImplicit false

/-- Orbit of the actual C3g5 obstruction under the actual C3g6a
representation. -/
def positiveSourceGravityMouthSpinOrbit : Set PhysicalBivector :=
  Set.range fun groupElement : SpinPlus13 =>
    spinLorentzPhysicalBivectorRepresentation groupElement
      positiveSourceGravityMouthObstruction

/-- Real-linear closure of the generated orbit. -/
def positiveSourceGravityMouthSpinOrbitResponsibilitySubmodule :
    Submodule ℝ PhysicalBivector :=
  Submodule.span ℝ positiveSourceGravityMouthSpinOrbit

abbrev PositiveSourceGravityMouthSpinOrbitResponsibilityCarrier :=
  positiveSourceGravityMouthSpinOrbitResponsibilitySubmodule

/-- Stability predicate for a real submodule under the actual physical
bivector representation. -/
def PhysicalBivectorSpinStable
    (candidate : Submodule ℝ PhysicalBivector) : Prop :=
  ∀ groupElement bivector, bivector ∈ candidate →
    spinLorentzPhysicalBivectorRepresentation groupElement bivector ∈ candidate

/-- The original obstruction is the identity-labelled orbit point. -/
theorem positiveSourceGravityMouthObstruction_mem_spinOrbitResponsibility :
    positiveSourceGravityMouthObstruction ∈
      positiveSourceGravityMouthSpinOrbitResponsibilitySubmodule := by
  apply Submodule.subset_span
  refine ⟨1, ?_⟩
  simp

/-- Acting on an orbit generator multiplies its Spin label, so the span is
stable under the actual representation. -/
theorem positiveSourceGravityMouthSpinOrbitResponsibility_spinStable :
    PhysicalBivectorSpinStable
      positiveSourceGravityMouthSpinOrbitResponsibilitySubmodule := by
  intro groupElement bivector member
  apply (show positiveSourceGravityMouthSpinOrbitResponsibilitySubmodule ≤
      Submodule.comap
        (spinLorentzPhysicalBivectorRepresentation groupElement).toLinearMap
        positiveSourceGravityMouthSpinOrbitResponsibilitySubmodule by
    apply Submodule.span_le.mpr
    intro generator generatorMem
    rcases generatorMem with ⟨orbitElement, rfl⟩
    change spinLorentzPhysicalBivectorRepresentation groupElement
        (spinLorentzPhysicalBivectorRepresentation orbitElement
          positiveSourceGravityMouthObstruction) ∈
      positiveSourceGravityMouthSpinOrbitResponsibilitySubmodule
    have productGenerator :
        spinLorentzPhysicalBivectorRepresentation (groupElement * orbitElement)
            positiveSourceGravityMouthObstruction ∈
          positiveSourceGravityMouthSpinOrbitResponsibilitySubmodule :=
      Submodule.subset_span ⟨groupElement * orbitElement, rfl⟩
    simpa using productGenerator) member

/-- Group inverses upgrade forward stability to exact membership
invariance. -/
theorem positiveSourceGravityMouthSpinOrbitResponsibility_mem_iff
    (groupElement : SpinPlus13) (bivector : PhysicalBivector) :
    spinLorentzPhysicalBivectorRepresentation groupElement bivector ∈
        positiveSourceGravityMouthSpinOrbitResponsibilitySubmodule ↔
      bivector ∈ positiveSourceGravityMouthSpinOrbitResponsibilitySubmodule := by
  constructor
  · intro transformedMember
    have inverseMember :=
      positiveSourceGravityMouthSpinOrbitResponsibility_spinStable
        groupElement⁻¹
        (spinLorentzPhysicalBivectorRepresentation groupElement bivector)
        transformedMember
    simpa using inverseMember
  · exact positiveSourceGravityMouthSpinOrbitResponsibility_spinStable
      groupElement bivector

/-- Restriction of one ambient action map to the generated carrier. -/
def positiveSourceGravityMouthSpinOrbitCarrierLinearMap
    (groupElement : SpinPlus13) :
    PositiveSourceGravityMouthSpinOrbitResponsibilityCarrier →ₗ[ℝ]
      PositiveSourceGravityMouthSpinOrbitResponsibilityCarrier where
  toFun bivector :=
    ⟨spinLorentzPhysicalBivectorRepresentation groupElement bivector.1,
      positiveSourceGravityMouthSpinOrbitResponsibility_spinStable
        groupElement bivector.1 bivector.2⟩
  map_add' first second := by
    apply Subtype.ext
    exact (spinLorentzPhysicalBivectorRepresentation groupElement).map_add
      first.1 second.1
  map_smul' scalar bivector := by
    apply Subtype.ext
    exact (spinLorentzPhysicalBivectorRepresentation groupElement).map_smul
      scalar bivector.1

/-- The inverse restricted map is generated by the inverse Spin element. -/
def positiveSourceGravityMouthSpinOrbitCarrierLinearEquiv
    (groupElement : SpinPlus13) :
    PositiveSourceGravityMouthSpinOrbitResponsibilityCarrier ≃ₗ[ℝ]
      PositiveSourceGravityMouthSpinOrbitResponsibilityCarrier where
  toLinearMap :=
    positiveSourceGravityMouthSpinOrbitCarrierLinearMap groupElement
  invFun :=
    positiveSourceGravityMouthSpinOrbitCarrierLinearMap groupElement⁻¹
  left_inv bivector := by
    apply Subtype.ext
    change spinLorentzPhysicalBivectorRepresentation groupElement⁻¹
        (spinLorentzPhysicalBivectorRepresentation groupElement bivector.1) =
      bivector.1
    simp
  right_inv bivector := by
    apply Subtype.ext
    change spinLorentzPhysicalBivectorRepresentation groupElement
        (spinLorentzPhysicalBivectorRepresentation groupElement⁻¹ bivector.1) =
      bivector.1
    simp

/-- Actual induced representation on the derived responsibility carrier. -/
def positiveSourceGravityMouthSpinOrbitCarrierRepresentation :
    SpinPlus13 →*
      (PositiveSourceGravityMouthSpinOrbitResponsibilityCarrier ≃ₗ[ℝ]
        PositiveSourceGravityMouthSpinOrbitResponsibilityCarrier) where
  toFun := positiveSourceGravityMouthSpinOrbitCarrierLinearEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro bivector
    apply Subtype.ext
    simp [positiveSourceGravityMouthSpinOrbitCarrierLinearEquiv,
      positiveSourceGravityMouthSpinOrbitCarrierLinearMap]
  map_mul' first second := by
    apply LinearEquiv.ext
    intro bivector
    apply Subtype.ext
    change spinLorentzPhysicalBivectorRepresentation (first * second) bivector.1 =
      spinLorentzPhysicalBivectorRepresentation first
        (spinLorentzPhysicalBivectorRepresentation second bivector.1)
    rw [map_mul]
    rfl

/-- Relative minimality: every real submodule containing the actual residual
and stable under the actual Spin action contains this orbit span. -/
theorem positiveSourceGravityMouthSpinOrbitResponsibility_minimal
    (candidate : Submodule ℝ PhysicalBivector)
    (contains : positiveSourceGravityMouthObstruction ∈ candidate)
    (spinStable : PhysicalBivectorSpinStable candidate) :
    positiveSourceGravityMouthSpinOrbitResponsibilitySubmodule ≤ candidate := by
  apply Submodule.span_le.mpr
  intro generator generatorMem
  rcases generatorMem with ⟨groupElement, rfl⟩
  exact spinStable groupElement positiveSourceGravityMouthObstruction contains

/-- The earlier singleton linear responsibility carrier embeds into the
canonical Spin-stable carrier.  Strictness is not claimed. -/
theorem positiveSourceGravityMouthLinearResponsibility_le_spinOrbit :
    positiveSourceGravityMouthLinearResponsibilitySubmodule ≤
      positiveSourceGravityMouthSpinOrbitResponsibilitySubmodule :=
  positiveSourceGravityMouthLinearResponsibility_minimal
    positiveSourceGravityMouthSpinOrbitResponsibilitySubmodule
    positiveSourceGravityMouthObstruction_mem_spinOrbitResponsibility

theorem positiveSourceGravityMouthSpinOrbitResponsibility_ne_bot :
    positiveSourceGravityMouthSpinOrbitResponsibilitySubmodule ≠ ⊥ := by
  intro responsibilityBottom
  have obstructionMember :=
    positiveSourceGravityMouthObstruction_mem_spinOrbitResponsibility
  rw [responsibilityBottom] at obstructionMember
  exact positiveSourceGravityMouthObstruction_ne_zero
    (by simpa using obstructionMember)

/-- The actual residual as an element of its derived Spin-stable carrier. -/
def carriedPositiveSourceGravityMouthSpinOrbitObstruction :
    PositiveSourceGravityMouthSpinOrbitResponsibilityCarrier :=
  ⟨positiveSourceGravityMouthObstruction,
    positiveSourceGravityMouthObstruction_mem_spinOrbitResponsibility⟩

theorem carriedPositiveSourceGravityMouthSpinOrbitObstruction_ne_zero :
    carriedPositiveSourceGravityMouthSpinOrbitObstruction ≠ 0 := by
  intro carriedZero
  apply positiveSourceGravityMouthObstruction_ne_zero
  exact congrArg Subtype.val carriedZero

/-- The same source sigma supplies the scalar keep.  There is no new
coefficient or source slot. -/
def positiveSourceGravityMouthSpinOrbitResponsibilityKeep :
    PositiveSourceGravityMouthSpinOrbitResponsibilityCarrier →ₗ[ℝ]
      PositiveSourceGravityMouthSpinOrbitResponsibilityCarrier :=
  scalarKeepLinearMap positiveSmoothUnifiedSource.legacy.sigma

/-- First residual step `r' = K r` on the Spin-stable carrier. -/
def transportedPositiveSourceGravityMouthSpinOrbitObstruction :
    PositiveSourceGravityMouthSpinOrbitResponsibilityCarrier :=
  positiveSourceGravityMouthSpinOrbitResponsibilityKeep
    carriedPositiveSourceGravityMouthSpinOrbitObstruction

/-- A scalar keep commutes with the restricted Spin representation. -/
theorem positiveSourceGravityMouthSpinOrbitResponsibilityKeep_equivariant
    (groupElement : SpinPlus13)
    (bivector : PositiveSourceGravityMouthSpinOrbitResponsibilityCarrier) :
    positiveSourceGravityMouthSpinOrbitCarrierRepresentation groupElement
        (positiveSourceGravityMouthSpinOrbitResponsibilityKeep bivector) =
      positiveSourceGravityMouthSpinOrbitResponsibilityKeep
        (positiveSourceGravityMouthSpinOrbitCarrierRepresentation groupElement
          bivector) := by
  apply Subtype.ext
  change spinLorentzPhysicalBivectorRepresentation groupElement
      ((1 - positiveSmoothUnifiedSource.legacy.sigma) • bivector.1) =
    (1 - positiveSmoothUnifiedSource.legacy.sigma) •
      spinLorentzPhysicalBivectorRepresentation groupElement bivector.1
  exact (spinLorentzPhysicalBivectorRepresentation groupElement).map_smul
    (1 - positiveSmoothUnifiedSource.legacy.sigma) bivector.1

/-- Since the trace is forced as `(I-K)r`, it is equivariant as well; no
independent trace transformation law is supplied. -/
theorem positiveSourceGravityMouthSpinOrbitResponsibilityTrace_equivariant
    (groupElement : SpinPlus13)
    (bivector : PositiveSourceGravityMouthSpinOrbitResponsibilityCarrier) :
    positiveSourceGravityMouthSpinOrbitCarrierRepresentation groupElement
        (linearResidualTrace
          positiveSourceGravityMouthSpinOrbitResponsibilityKeep bivector) =
      linearResidualTrace positiveSourceGravityMouthSpinOrbitResponsibilityKeep
        (positiveSourceGravityMouthSpinOrbitCarrierRepresentation groupElement
          bivector) := by
  change positiveSourceGravityMouthSpinOrbitCarrierRepresentation groupElement
      (bivector - positiveSourceGravityMouthSpinOrbitResponsibilityKeep bivector) =
    positiveSourceGravityMouthSpinOrbitCarrierRepresentation groupElement
        bivector -
      positiveSourceGravityMouthSpinOrbitResponsibilityKeep
        (positiveSourceGravityMouthSpinOrbitCarrierRepresentation groupElement
          bivector)
  rw [map_sub,
    positiveSourceGravityMouthSpinOrbitResponsibilityKeep_equivariant]

theorem positiveSourceGravityMouthSpinOrbitResponsibilityKeep_active :
    ResidualTransportActive
      positiveSourceGravityMouthSpinOrbitResponsibilityKeep := by
  exact scalarKeepLinearMap_active_of_ne_zero
    positiveSmoothUnifiedSource.legacy.sigma
    (ne_of_gt positiveSmoothUnifiedSource.legacy.sigma_pos)

/-- Framework first formula on the actual carried obstruction. -/
theorem carriedPositiveSourceGravityMouthSpinOrbitObstruction_split :
    carriedPositiveSourceGravityMouthSpinOrbitObstruction =
      transportedPositiveSourceGravityMouthSpinOrbitObstruction +
      linearResidualTrace
        positiveSourceGravityMouthSpinOrbitResponsibilityKeep
        carriedPositiveSourceGravityMouthSpinOrbitObstruction :=
  residualTransportCore_residual_split
    positiveSourceGravityMouthSpinOrbitResponsibilityKeep
    carriedPositiveSourceGravityMouthSpinOrbitObstruction

/-- The split forces the trace; it cannot be a branch-choice datum. -/
theorem carriedPositiveSourceGravityMouthSpinOrbitObstruction_trace_unique
    (trace : PositiveSourceGravityMouthSpinOrbitResponsibilityCarrier) :
    carriedPositiveSourceGravityMouthSpinOrbitObstruction =
        transportedPositiveSourceGravityMouthSpinOrbitObstruction + trace ↔
      trace = linearResidualTrace
        positiveSourceGravityMouthSpinOrbitResponsibilityKeep
        carriedPositiveSourceGravityMouthSpinOrbitObstruction :=
  residualTransportCore_trace_unique
    positiveSourceGravityMouthSpinOrbitResponsibilityKeep
    carriedPositiveSourceGravityMouthSpinOrbitObstruction trace

/-- Positive zero detector used by the Truth Formula equivalence.  It is not
claimed to be a Lorentz-invariant physical energy. -/
def positiveSourceGravityMouthSpinOrbitResponsibilityEnergy
    (residual : PositiveSourceGravityMouthSpinOrbitResponsibilityCarrier) : ℝ :=
  ‖residual‖ ^ 2

theorem positiveSourceGravityMouthSpinOrbitResponsibilityEnergy_eq_zero_iff
    (residual : PositiveSourceGravityMouthSpinOrbitResponsibilityCarrier) :
    positiveSourceGravityMouthSpinOrbitResponsibilityEnergy residual = 0 ↔
      residual = 0 := by
  simp [positiveSourceGravityMouthSpinOrbitResponsibilityEnergy]

/-- Active transport identifies fixedness, zero residual, zero trace, and the
zero-detecting energy predicate. -/
theorem positiveSourceGravityMouthSpinOrbitResponsibility_transportEquivalence :
    TruthFormulaCoreEquivalence
      positiveSourceGravityMouthSpinOrbitResponsibilityKeep
      positiveSourceGravityMouthSpinOrbitResponsibilityEnergy
      carriedPositiveSourceGravityMouthSpinOrbitObstruction :=
  residualTransportCore_equivalence
    positiveSourceGravityMouthSpinOrbitResponsibilityKeep
    positiveSourceGravityMouthSpinOrbitResponsibilityEnergy
    positiveSourceGravityMouthSpinOrbitResponsibilityKeep_active
    positiveSourceGravityMouthSpinOrbitResponsibilityEnergy_eq_zero_iff
    carriedPositiveSourceGravityMouthSpinOrbitObstruction

theorem carriedPositiveSourceGravityMouthSpinOrbitObstruction_not_fixed :
    ¬ ResidualTransportFixed
      positiveSourceGravityMouthSpinOrbitResponsibilityKeep
      carriedPositiveSourceGravityMouthSpinOrbitObstruction := by
  exact fun fixed => carriedPositiveSourceGravityMouthSpinOrbitObstruction_ne_zero
    (positiveSourceGravityMouthSpinOrbitResponsibility_transportEquivalence
      |>.fixed_iff_zero_residual.mp fixed)

theorem carriedPositiveSourceGravityMouthSpinOrbitObstruction_trace_ne_zero :
    linearResidualTrace positiveSourceGravityMouthSpinOrbitResponsibilityKeep
        carriedPositiveSourceGravityMouthSpinOrbitObstruction ≠ 0 := by
  exact fun traceZero =>
    carriedPositiveSourceGravityMouthSpinOrbitObstruction_ne_zero
      (positiveSourceGravityMouthSpinOrbitResponsibility_transportEquivalence
        |>.zero_residual_iff_zero_trace.mpr traceZero)

/-- Residual-level no-third-sink on the minimal Spin-stable carrier.  This
does not replace the separately typed source-state continuation theorem. -/
theorem positiveSourceGravityMouthSpinOrbitObstruction_has_no_naked_residual_sink :
    (¬ ResidualTransportFixed
        positiveSourceGravityMouthSpinOrbitResponsibilityKeep
        carriedPositiveSourceGravityMouthSpinOrbitObstruction) ∧
      linearResidualTrace positiveSourceGravityMouthSpinOrbitResponsibilityKeep
          carriedPositiveSourceGravityMouthSpinOrbitObstruction ≠ 0 :=
  ⟨carriedPositiveSourceGravityMouthSpinOrbitObstruction_not_fixed,
    carriedPositiveSourceGravityMouthSpinOrbitObstruction_trace_ne_zero⟩

/-- Exact lineage qualifies the source while the covariant carrier, nonzero
residual, and nonzero forced trace retain its specific responsibility. -/
theorem positiveExactLineage_carries_spinCovariantGravityMouthResponsibility :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
        canonicalP506SourceAffineL0ObservableLineageReference ∧
      PhysicalBivectorSpinStable
        positiveSourceGravityMouthSpinOrbitResponsibilitySubmodule ∧
      carriedPositiveSourceGravityMouthSpinOrbitObstruction ≠ 0 ∧
      linearResidualTrace positiveSourceGravityMouthSpinOrbitResponsibilityKeep
          carriedPositiveSourceGravityMouthSpinOrbitObstruction ≠ 0 :=
  ⟨positiveSmoothUnifiedSource_generates_exactP506L0Lineage,
    positiveSourceGravityMouthSpinOrbitResponsibility_spinStable,
    carriedPositiveSourceGravityMouthSpinOrbitObstruction_ne_zero,
    carriedPositiveSourceGravityMouthSpinOrbitObstruction_trace_ne_zero⟩

end

end SaturationMonoid.PhysicsCore.StageNinePositiveSourceGravityMouthSpinOrbitCarrier
