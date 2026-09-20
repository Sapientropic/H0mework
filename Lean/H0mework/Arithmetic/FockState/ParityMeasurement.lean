import H0mework.Arithmetic.FockState.FactorDecay

/-!
# Ordered Z/2 species measurement on the particle face

The old joint measurement sees coherent wave data and total additive charge.
On an actual arithmetic split there is a further source-owned detector: the
ordered endpoint parities.  It is a dependent face of the same Fock state,
not a second particle carrier.

Odd prime repair factors have even shift and are invisible to this extra
coordinate.  The unique even prime factor `2` has odd shift, flips both
endpoint species, and therefore leaves the old charge kernel while becoming
visible to the refined detector.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFock

open ArithmeticGeneration
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticFullFactorRepairProducer

noncomputable section

/-- The particle species grading group. -/
abbrev SpeciesGrade := ZMod 2

def endpointSpeciesGrade (value : Nat) : SpeciesGrade := value

theorem endpointSpeciesGrade_eq_iff_mod (left right : Nat) :
    endpointSpeciesGrade left = endpointSpeciesGrade right ↔
      left % 2 = right % 2 :=
  ZMod.natCast_eq_natCast_iff' left right 2

/-- Ordered species of one actual two-particle split. -/
def orderedSpeciesGrade {index : Nat} (state : EffectiveSplitAt index) :
    SpeciesGrade × SpeciesGrade :=
  (endpointSpeciesGrade (splitLeft state),
    endpointSpeciesGrade (splitRight state))

/-- Every effective split has even total charge, hence both endpoints belong
to the same parity sector. -/
theorem orderedSpeciesGrade_diagonal {index : Nat}
    (state : EffectiveSplitAt index) :
    (orderedSpeciesGrade state).1 = (orderedSpeciesGrade state).2 := by
  apply (endpointSpeciesGrade_eq_iff_mod _ _).mpr
  have landing := split_landing state
  unfold repairTargetValue at landing
  rw [evenTargetHistory_eq_generate,
    UnitHistory.cardinalShadow_generate] at landing
  omega

abbrev AtomicJointMeasurementTarget :=
  JointMeasurementTarget × (SpeciesGrade × SpeciesGrade)

/-- Charge/coherent measurement refined by the ordered species coordinate.
This face is defined on actual arithmetic split states, where the two natural
endpoint coordinates are source data. -/
def atomicJointMeasurement {index : Nat}
    (state : EffectiveSplitAt index) : AtomicJointMeasurementTarget :=
  (jointMeasurement (splitParticleState state), orderedSpeciesGrade state)

@[simp] theorem atomicJointMeasurement_joint {index : Nat}
    (state : EffectiveSplitAt index) :
    (atomicJointMeasurement state).1 =
      jointMeasurement (splitParticleState state) :=
  rfl

@[simp] theorem atomicJointMeasurement_species {index : Nat}
    (state : EffectiveSplitAt index) :
    (atomicJointMeasurement state).2 = orderedSpeciesGrade state :=
  rfl

theorem atomicJointMeasurement_charge {index : Nat}
    (state : EffectiveSplitAt index) :
    (atomicJointMeasurement state).1 = (0, targetCharge index) :=
  jointMeasurement_splitParticleState state

private theorem leftRepair_grade_eq_of_factor_odd
    {index : Nat} {source : EffectiveSplitAt index}
    (leftNotPrime : ¬ Nat.Prime (splitLeft source))
    (selected : {p : Nat // p ∈ (splitLeft source).primeFactors})
    (factorOdd : selected.1 % 2 = 1) :
    endpointSpeciesGrade
        (splitLeft
          ((FactorRepairAlternativeAt.left leftNotPrime selected).target)) =
      endpointSpeciesGrade (splitLeft source) := by
  apply (endpointSpeciesGrade_eq_iff_mod _ _).mpr
  rw [FactorRepairAlternativeAt.left_target_left]
  have proper :=
    FactorRepairAlternativeAt.left_selectedFactorProper leftNotPrime selected
  omega

private theorem rightRepair_grade_eq_of_factor_odd
    {index : Nat} {source : EffectiveSplitAt index}
    (rightNotPrime : ¬ Nat.Prime (splitRight source))
    (selected : {p : Nat // p ∈ (splitRight source).primeFactors})
    (factorOdd : selected.1 % 2 = 1) :
    endpointSpeciesGrade
        (splitLeft
          ((FactorRepairAlternativeAt.right rightNotPrime selected).target)) =
      endpointSpeciesGrade (splitLeft source) := by
  apply (endpointSpeciesGrade_eq_iff_mod _ _).mpr
  rw [FactorRepairAlternativeAt.right_target_left]
  omega

/-- An odd prime repair factor has even shift `p - 1`, so the ordered species
coordinate is conserved. -/
theorem repair_orderedSpeciesGrade_eq_of_factor_ne_two
    {index : Nat} {source : EffectiveSplitAt index}
    (alternative : FactorRepairAlternativeAt source)
    (factorNeTwo : alternative.factor ≠ 2) :
    orderedSpeciesGrade alternative.target = orderedSpeciesGrade source := by
  have factorOdd : alternative.factor % 2 = 1 :=
    alternative.factorPrime.eq_two_or_odd.resolve_left factorNeTwo
  have firstEq :
      (orderedSpeciesGrade alternative.target).1 =
        (orderedSpeciesGrade source).1 := by
    cases alternative with
    | left leftNotPrime selected =>
        exact leftRepair_grade_eq_of_factor_odd
          leftNotPrime selected factorOdd
    | right rightNotPrime selected =>
        exact rightRepair_grade_eq_of_factor_odd
          rightNotPrime selected factorOdd
  apply Prod.ext
  · exact firstEq
  · exact
      (orderedSpeciesGrade_diagonal alternative.target).symm.trans <|
        firstEq.trans
        (orderedSpeciesGrade_diagonal source)

private theorem leftRepair_grade_ne_of_factor_two
    {index : Nat} {source : EffectiveSplitAt index}
    (leftNotPrime : ¬ Nat.Prime (splitLeft source))
    (selected : {p : Nat // p ∈ (splitLeft source).primeFactors})
    (factorTwo : selected.1 = 2) :
    endpointSpeciesGrade
        (splitLeft
          ((FactorRepairAlternativeAt.left leftNotPrime selected).target)) ≠
      endpointSpeciesGrade (splitLeft source) := by
  intro equality
  have residue := (endpointSpeciesGrade_eq_iff_mod _ _).mp equality
  rw [FactorRepairAlternativeAt.left_target_left, factorTwo] at residue
  have floor := splitLeft_atLeastTwo source
  omega

private theorem rightRepair_grade_ne_of_factor_two
    {index : Nat} {source : EffectiveSplitAt index}
    (rightNotPrime : ¬ Nat.Prime (splitRight source))
    (selected : {p : Nat // p ∈ (splitRight source).primeFactors})
    (factorTwo : selected.1 = 2) :
    endpointSpeciesGrade
        (splitLeft
          ((FactorRepairAlternativeAt.right rightNotPrime selected).target)) ≠
      endpointSpeciesGrade (splitLeft source) := by
  intro equality
  have residue := (endpointSpeciesGrade_eq_iff_mod _ _).mp equality
  rw [FactorRepairAlternativeAt.right_target_left, factorTwo] at residue
  omega

/-- The even prime repair factor flips both endpoint species. -/
theorem repair_orderedSpeciesGrade_both_flip_of_factor_eq_two
    {index : Nat} {source : EffectiveSplitAt index}
    (alternative : FactorRepairAlternativeAt source)
    (factorTwo : alternative.factor = 2) :
    (orderedSpeciesGrade alternative.target).1 ≠
        (orderedSpeciesGrade source).1 ∧
      (orderedSpeciesGrade alternative.target).2 ≠
        (orderedSpeciesGrade source).2 := by
  have leftNe :
      (orderedSpeciesGrade alternative.target).1 ≠
        (orderedSpeciesGrade source).1 := by
    cases alternative with
    | left leftNotPrime selected =>
        exact leftRepair_grade_ne_of_factor_two
          leftNotPrime selected factorTwo
    | right rightNotPrime selected =>
        exact rightRepair_grade_ne_of_factor_two
          rightNotPrime selected factorTwo
  refine ⟨leftNe, ?_⟩
  intro rightEq
  apply leftNe
  exact (orderedSpeciesGrade_diagonal alternative.target).trans <|
    rightEq.trans (orderedSpeciesGrade_diagonal source).symm

/-- Odd-factor repair remains in the refined measurement fibre. -/
theorem repair_atomicJointMeasurement_eq_of_factor_ne_two
    {index : Nat} {source : EffectiveSplitAt index}
    (alternative : FactorRepairAlternativeAt source)
    (factorNeTwo : alternative.factor ≠ 2) :
    atomicJointMeasurement alternative.target =
      atomicJointMeasurement source := by
  apply Prod.ext
  · exact (factorDecay_split_measurement_eq (.repair alternative)).symm
  · exact repair_orderedSpeciesGrade_eq_of_factor_ne_two
      alternative factorNeTwo

/-- The factor-2 repair was invisible to total charge, but it is visible to
the ordered species detector. -/
theorem repair_atomicJointMeasurement_ne_of_factor_eq_two
    {index : Nat} {source : EffectiveSplitAt index}
    (alternative : FactorRepairAlternativeAt source)
    (factorTwo : alternative.factor = 2) :
    atomicJointMeasurement alternative.target ≠
      atomicJointMeasurement source := by
  intro measurementEq
  have speciesEq := congrArg (fun value => value.2) measurementEq
  exact
    (repair_orderedSpeciesGrade_both_flip_of_factor_eq_two
      alternative factorTwo).1 (congrArg Prod.fst speciesEq)

theorem repair_atomicJointMeasurement_eq_iff_factor_ne_two
    {index : Nat} {source : EffectiveSplitAt index}
    (alternative : FactorRepairAlternativeAt source) :
    atomicJointMeasurement alternative.target = atomicJointMeasurement source ↔
      alternative.factor ≠ 2 := by
  constructor
  · intro measurementEq factorTwo
    exact repair_atomicJointMeasurement_ne_of_factor_eq_two
      alternative factorTwo measurementEq
  · exact repair_atomicJointMeasurement_eq_of_factor_ne_two alternative

/-- Ordered Z/2 current carried by a repair event. -/
def repairSpeciesFlux
    {index : Nat} {source : EffectiveSplitAt index}
    (alternative : FactorRepairAlternativeAt source) :
    SpeciesGrade × SpeciesGrade :=
  orderedSpeciesGrade alternative.target - orderedSpeciesGrade source

theorem repairSpeciesFlux_eq_zero_of_factor_ne_two
    {index : Nat} {source : EffectiveSplitAt index}
    (alternative : FactorRepairAlternativeAt source)
    (factorNeTwo : alternative.factor ≠ 2) :
    repairSpeciesFlux alternative = 0 := by
  apply sub_eq_zero.mpr
  exact repair_orderedSpeciesGrade_eq_of_factor_ne_two alternative factorNeTwo

theorem repairSpeciesFlux_ne_zero_of_factor_eq_two
    {index : Nat} {source : EffectiveSplitAt index}
    (alternative : FactorRepairAlternativeAt source)
    (factorTwo : alternative.factor = 2) :
    repairSpeciesFlux alternative ≠ 0 := by
  intro fluxZero
  have gradeEq :
      orderedSpeciesGrade alternative.target = orderedSpeciesGrade source :=
    sub_eq_zero.mp fluxZero
  exact
    (repair_orderedSpeciesGrade_both_flip_of_factor_eq_two
      alternative factorTwo).1 (congrArg Prod.fst gradeEq)

/-- Exact selection law: among prime repair factors, parity current vanishes
precisely away from the unique even species. -/
theorem repairSpeciesFlux_eq_zero_iff_factor_ne_two
    {index : Nat} {source : EffectiveSplitAt index}
    (alternative : FactorRepairAlternativeAt source) :
    repairSpeciesFlux alternative = 0 ↔ alternative.factor ≠ 2 := by
  constructor
  · intro fluxZero factorTwo
    exact repairSpeciesFlux_ne_zero_of_factor_eq_two
      alternative factorTwo fluxZero
  · exact repairSpeciesFlux_eq_zero_of_factor_ne_two alternative

/-- The old charge/coherent detector still sees the factor-2 repair as equal;
the new inequality comes solely from the missing species coordinate. -/
theorem repair_factor_two_exits_old_kernel_by_species
    {index : Nat} {source : EffectiveSplitAt index}
    (alternative : FactorRepairAlternativeAt source)
    (factorTwo : alternative.factor = 2) :
    jointMeasurement (splitParticleState source) =
        jointMeasurement (splitParticleState alternative.target) ∧
      atomicJointMeasurement source ≠
        atomicJointMeasurement alternative.target :=
  ⟨factorDecay_split_measurement_eq (.repair alternative),
    Ne.symm (repair_atomicJointMeasurement_ne_of_factor_eq_two
      alternative factorTwo)⟩

end

end ParticleWaveFock
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
