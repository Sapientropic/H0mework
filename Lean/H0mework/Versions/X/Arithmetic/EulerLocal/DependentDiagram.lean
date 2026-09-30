import H0mework.Realization.MappingCone.Functoriality
import H0mework.Versions.X.Arithmetic.EulerLocal.Operator
import H0mework.Realization.GlobalSections.DerivedState
import H0mework.Realization.HomotopyLimits.Sequential

/-!
# Exact-runtime dependent diagram of local factorization/Euler stages

One exact factorization payload is the seed.  Stage `n` is calculated from
the seed runtime by `advance n`; its prime and exponent axes are the actual
factorization support and multiplicity at that activated runtime.  The local
boundary is `id - (EulerConvolution ∘ reversal)`.

Only the successor restriction square is domain work.  The resulting
`Natᵒᵖ` diagram is handed directly to
`RootGeneratedDependentDerivedGlobalStateAt.generate`; the global state,
global cone and every local restriction are framework outputs.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationEulerDependentDiagram

open ArithmeticGeneration
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticFactorizationEulerOperator
open CanonicalUnitArithmeticRoot
open CategoryTheory
open CochainMappingCoconeFunctoriality
open DependentDerivedGlobalState
open DependentDerivedGlobalState.RootGeneratedDependentDerivedGlobalStateAt
open SequentialHomotopyLimit

noncomputable section

abbrev FactorizationPayload :=
  Σ authority : RuntimeAuthority,
    GeneratedUnitFactorizationAt (authorityWholeHistory authority)

def seedOccurrence : RootedAccountedUnfolding FactorizationPayload :=
  factorizationOccurrence 0

def runtimeFrom (seed : FactorizationPayload) (stage : Nat) : Runtime :=
  seed.1.1.advance stage

def authorityFrom (seed : FactorizationPayload) (stage : Nat) :
    RuntimeAuthority :=
  ⟨runtimeFrom seed stage, (runtimeFrom seed stage).tick⟩

theorem authorityWholeHistory_next (runtime : Runtime) :
    authorityWholeHistory
        ⟨runtime.tick.next, runtime.tick.next.tick⟩ =
      next (authorityWholeHistory ⟨runtime, runtime.tick⟩) :=
  rfl

/-- Every local stage is an exact activated runtime factorization
occurrence, not a numeric prime table. -/
def stageOccurrenceFrom (seed : FactorizationPayload) :
    (stage : Nat) → RootedAccountedUnfolding FactorizationPayload
  | 0 => RootedAccountedUnfolding.zero seed
  | stage + 1 =>
      (RootedAccountedUnfolding.zero (authorityFrom seed (stage + 1))).map
        fun authority => ⟨authority,
          GeneratedUnitFactorizationAt.generate
            (authorityWholeHistory authority)⟩

@[simp] theorem stageOccurrenceFrom_zero_authority
    (seed : FactorizationPayload) :
    (stageOccurrenceFrom seed 0).root.1 = seed.1 :=
  rfl

@[simp] theorem stageOccurrenceFrom_succ_authority
    (seed : FactorizationPayload) (stage : Nat) :
    (stageOccurrenceFrom seed (stage + 1)).root.1 =
      authorityFrom seed (stage + 1) := by
  rw [stageOccurrenceFrom]
  rfl

abbrev StageHistory (seed : FactorizationPayload) (stage : Nat) : UnitHistory :=
  authorityWholeHistory (stageOccurrenceFrom seed stage).root.1

def stageFactorization (seed : FactorizationPayload) (stage : Nat) :
    GeneratedUnitFactorizationAt (StageHistory seed stage) :=
  (stageOccurrenceFrom seed stage).root.2

@[simp] theorem stageHistory_zero (seed : FactorizationPayload) :
    StageHistory seed 0 = authorityWholeHistory seed.1 :=
  rfl

@[simp] theorem stageHistory_succ (seed : FactorizationPayload)
    (stage : Nat) :
    StageHistory seed (stage + 1) = next (StageHistory seed stage) := by
  cases stage with
  | zero =>
      unfold StageHistory
      rw [stageOccurrenceFrom_succ_authority,
        stageOccurrenceFrom_zero_authority]
      simpa [authorityFrom, runtimeFrom, LivingRuntimeState.advance] using
        authorityWholeHistory_next seed.1.1
  | succ stage =>
      unfold StageHistory
      rw [stageOccurrenceFrom_succ_authority,
        stageOccurrenceFrom_succ_authority]
      simpa [authorityFrom, runtimeFrom, LivingRuntimeState.advance] using
        authorityWholeHistory_next (seed.1.1.advance (stage + 1))

abbrev StagePrime (seed : FactorizationPayload) (stage : Nat) :=
  PrimeIndex (StageHistory seed stage)

abbrev StageExponent (seed : FactorizationPayload) (stage : Nat)
    (primeIndex : StagePrime seed stage) :=
  Fin (multiplicity (StageHistory seed stage) primeIndex + 1)

abbrev EulerIndex (seed : FactorizationPayload) (stage : Nat) :=
  Σ primeIndex : StagePrime seed stage,
    StageExponent seed stage primeIndex × Fin 2

abbrev EulerLattice (seed : FactorizationPayload) (stage : Nat) :=
  EulerIndex seed stage → ℤ

def exponentSub {seed : FactorizationPayload} {stage : Nat}
    {primeIndex : StagePrime seed stage}
    (localExponent : StageExponent seed stage primeIndex) (amount : Nat) :
    StageExponent seed stage primeIndex :=
  ⟨localExponent - amount,
    (Nat.sub_le localExponent amount).trans_lt localExponent.isLt⟩

def localEulerOperator (seed : FactorizationPayload) (stage : Nat) :
    EulerLattice seed stage →ₗ[ℤ] EulerLattice seed stage where
  toFun := fun value index =>
    ∑ amount ∈ Finset.range (index.2.1 + 1),
      (localEulerPowerSeries
          ((stageFactorization seed stage).actualPrime index.1)).coeff amount *
        value ⟨index.1, exponentSub index.2.1 amount, index.2.2⟩
  map_add' := by
    intro left right
    funext index
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro scalar value
    funext index
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro amount _membership
    simp [mul_left_comm]

theorem localEulerOperator_apply (seed : FactorizationPayload) (stage : Nat)
    (value : EulerLattice seed stage) (index : EulerIndex seed stage) :
    localEulerOperator seed stage value index =
      ∑ amount ∈ Finset.range (index.2.1 + 1),
        value ⟨index.1, exponentSub index.2.1 amount, index.2.2⟩ := by
  change
    (∑ amount ∈ Finset.range (index.2.1 + 1),
      (localEulerPowerSeries
          ((stageFactorization seed stage).actualPrime index.1)).coeff amount *
        value ⟨index.1, exponentSub index.2.1 amount, index.2.2⟩) = _
  apply Finset.sum_congr rfl
  intro amount _membership
  rw [localEulerCoefficient, one_mul]

def localPolynomialOperator (seed : FactorizationPayload) (stage : Nat) :
    EulerLattice seed stage →ₗ[ℤ] EulerLattice seed stage where
  toFun := fun value index =>
    ∑ amount ∈ Finset.range (index.2.1 + 1),
      localPolynomialCoefficient
          ((stageFactorization seed stage).actualPrime index.1) amount *
        value ⟨index.1, exponentSub index.2.1 amount, index.2.2⟩
  map_add' := by
    intro left right
    funext index
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro scalar value
    funext index
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro amount _membership
    simp [mul_left_comm]

def reversal (seed : FactorizationPayload) (stage : Nat) :
    EulerLattice seed stage →ₗ[ℤ] EulerLattice seed stage where
  toFun := fun value index =>
    value ⟨index.1, index.2.1, index.2.2.rev⟩
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

theorem reversal_involutive (seed : FactorizationPayload) (stage : Nat) :
    Function.Involutive (reversal seed stage) := by
  intro value
  funext index
  simp [reversal]

def eulerReversalAction (seed : FactorizationPayload) (stage : Nat) :
    EulerLattice seed stage →ₗ[ℤ] EulerLattice seed stage :=
  (localEulerOperator seed stage).comp (reversal seed stage)

def boundary (seed : FactorizationPayload) (stage : Nat) :
    EulerLattice seed stage →ₗ[ℤ] EulerLattice seed stage :=
  LinearMap.id - eulerReversalAction seed stage

theorem factorization_mono_succ (seed : FactorizationPayload) (stage : Nat) :
    factorization (StageHistory seed stage) ≤
      factorization (StageHistory seed (stage + 1)) := by
  rw [factorization_eq_cardinal_factorization,
    factorization_eq_cardinal_factorization]
  apply (Nat.factorization_le_iff_dvd
    (Nat.factorial_ne_zero (StageHistory seed stage).cardinalShadow)
    (Nat.factorial_ne_zero
      (StageHistory seed (stage + 1)).cardinalShadow)).2
  apply Nat.factorial_dvd_factorial
  have historyOrder :
      (StageHistory seed stage).cardinalShadow ≤
        (StageHistory seed (stage + 1)).cardinalShadow := by
    rw [stageHistory_succ, next_eq_next]
    change (StageHistory seed stage).cardinalShadow ≤
      Nat.succ (StageHistory seed stage).cardinalShadow
    exact Nat.le_succ _
  exact historyOrder

def liftPrime (seed : FactorizationPayload) (stage : Nat)
    (primeIndex : StagePrime seed stage) :
    StagePrime seed (stage + 1) := by
  refine ⟨primeIndex.1, Finsupp.mem_support_iff.mpr ?_⟩
  have oldNonzero : factorization (StageHistory seed stage) primeIndex.1 ≠ 0 :=
    Finsupp.mem_support_iff.mp primeIndex.2
  have order := factorization_mono_succ seed stage primeIndex.1
  omega

theorem liftPrime_actualPrime (seed : FactorizationPayload) (stage : Nat)
    (primeIndex : StagePrime seed stage) :
    (stageFactorization seed (stage + 1)).actualPrime
        (liftPrime seed stage primeIndex) =
      (stageFactorization seed stage).actualPrime primeIndex := by
  apply Subtype.ext
  rfl

def liftExponent (seed : FactorizationPayload) (stage : Nat)
    (primeIndex : StagePrime seed stage)
    (localExponent : StageExponent seed stage primeIndex) :
    StageExponent seed (stage + 1) (liftPrime seed stage primeIndex) := by
  refine ⟨localExponent.1, ?_⟩
  have order := factorization_mono_succ seed stage primeIndex.1
  have oldBound := localExponent.2
  change localExponent.1 <
    factorization (StageHistory seed (stage + 1)) primeIndex.1 + 1
  change localExponent.1 <
    factorization (StageHistory seed stage) primeIndex.1 + 1 at oldBound
  omega

theorem exponentSub_liftExponent (seed : FactorizationPayload) (stage : Nat)
    (primeIndex : StagePrime seed stage)
    (localExponent : StageExponent seed stage primeIndex) (amount : Nat) :
    exponentSub (liftExponent seed stage primeIndex localExponent) amount =
      liftExponent seed stage primeIndex
        (exponentSub localExponent amount) := by
  apply Fin.ext
  rfl

def liftIndex (seed : FactorizationPayload) (stage : Nat) :
    EulerIndex seed stage → EulerIndex seed (stage + 1)
  | ⟨primeIndex, localExponent, dualIndex⟩ =>
      ⟨liftPrime seed stage primeIndex,
        liftExponent seed stage primeIndex localExponent, dualIndex⟩

/-- The sole cofinal domain coherence datum: one successor restriction. -/
def restriction (seed : FactorizationPayload) (stage : Nat) :
    EulerLattice seed (stage + 1) →ₗ[ℤ] EulerLattice seed stage where
  toFun := fun value index => value (liftIndex seed stage index)
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

theorem restriction_euler_square (seed : FactorizationPayload) (stage : Nat) :
    (restriction seed stage).comp (localEulerOperator seed (stage + 1)) =
      (localEulerOperator seed stage).comp (restriction seed stage) := by
  apply LinearMap.ext
  intro value
  funext index
  rcases index with ⟨primeIndex, localExponent, dualIndex⟩
  simp only [LinearMap.comp_apply]
  change
    localEulerOperator seed (stage + 1) value
        ⟨liftPrime seed stage primeIndex,
          liftExponent seed stage primeIndex localExponent, dualIndex⟩ =
      localEulerOperator seed stage (restriction seed stage value)
        ⟨primeIndex, localExponent, dualIndex⟩
  rw [localEulerOperator_apply, localEulerOperator_apply]
  apply Finset.sum_congr rfl
  intro amount _membership
  change value ⟨liftPrime seed stage primeIndex,
      exponentSub (liftExponent seed stage primeIndex localExponent) amount,
      dualIndex⟩ =
    value ⟨liftPrime seed stage primeIndex,
      liftExponent seed stage primeIndex
        (exponentSub localExponent amount), dualIndex⟩
  rw [exponentSub_liftExponent]

theorem restriction_polynomial_square
    (seed : FactorizationPayload) (stage : Nat) :
    (restriction seed stage).comp (localPolynomialOperator seed (stage + 1)) =
      (localPolynomialOperator seed stage).comp (restriction seed stage) := by
  apply LinearMap.ext
  intro value
  funext index
  rcases index with ⟨primeIndex, localExponent, dualIndex⟩
  change
    (∑ amount ∈ Finset.range (localExponent.1 + 1),
      localPolynomialCoefficient
          ((stageFactorization seed (stage + 1)).actualPrime
            (liftPrime seed stage primeIndex)) amount *
        value ⟨liftPrime seed stage primeIndex,
          exponentSub
            (liftExponent seed stage primeIndex localExponent) amount,
          dualIndex⟩) =
    ∑ amount ∈ Finset.range (localExponent.1 + 1),
      localPolynomialCoefficient
          ((stageFactorization seed stage).actualPrime primeIndex) amount *
        value ⟨liftPrime seed stage primeIndex,
          liftExponent seed stage primeIndex
            (exponentSub localExponent amount), dualIndex⟩
  apply Finset.sum_congr rfl
  intro amount _membership
  rw [liftPrime_actualPrime, exponentSub_liftExponent]

theorem restriction_reversal_square
    (seed : FactorizationPayload) (stage : Nat) :
    (restriction seed stage).comp (reversal seed (stage + 1)) =
      (reversal seed stage).comp (restriction seed stage) := by
  apply LinearMap.ext
  intro value
  funext index
  rfl

theorem restriction_action_square
    (seed : FactorizationPayload) (stage : Nat) :
    (restriction seed stage).comp
        (eulerReversalAction seed (stage + 1)) =
      (eulerReversalAction seed stage).comp (restriction seed stage) := by
  apply LinearMap.ext
  intro value
  have eulerSquare := LinearMap.congr_fun
    (restriction_euler_square seed stage) (reversal seed (stage + 1) value)
  have reversalSquare := LinearMap.congr_fun
    (restriction_reversal_square seed stage) value
  change restriction seed stage
      (localEulerOperator seed (stage + 1)
        (reversal seed (stage + 1) value)) =
    localEulerOperator seed stage
      (reversal seed stage (restriction seed stage value))
  calc
    _ = localEulerOperator seed stage
        (restriction seed stage (reversal seed (stage + 1) value)) :=
      eulerSquare
    _ = _ := congrArg (fun current => localEulerOperator seed stage current)
      reversalSquare

theorem restriction_boundary_square
    (seed : FactorizationPayload) (stage : Nat) :
    (restriction seed stage).comp (boundary seed (stage + 1)) =
      (boundary seed stage).comp (restriction seed stage) := by
  unfold boundary
  rw [LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.comp_id, LinearMap.id_comp,
    restriction_action_square]

/-! ## Local cochain table and frozen global-state consumer -/

noncomputable abbrev StageModule (seed : FactorizationPayload) (stage : Nat) :
    ModuleCat.{0} ℤ :=
  ModuleCat.of ℤ (EulerLattice seed stage)

noncomputable abbrev stageLatticeComplex
    (seed : FactorizationPayload) (stage : Nat) : IntegralCochainComplex :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).obj
    (StageModule seed stage)

noncomputable def stageBoundaryMap
    (seed : FactorizationPayload) (stage : Nat) :
    stageLatticeComplex seed stage ⟶ stageLatticeComplex seed stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (boundary seed stage))

noncomputable abbrev stageComplex
    (seed : FactorizationPayload) (stage : Nat) : IntegralCochainComplex :=
  CochainComplex.mappingCocone (stageBoundaryMap seed stage)

noncomputable def stageRestrictionMap
    (seed : FactorizationPayload) (stage : Nat) :
    stageLatticeComplex seed (stage + 1) ⟶
      stageLatticeComplex seed stage :=
  (CochainComplex.singleFunctor (ModuleCat ℤ) 0).map
    (ModuleCat.ofHom (restriction seed stage))

theorem stageRestriction_boundary_square
    (seed : FactorizationPayload) (stage : Nat) :
    stageRestrictionMap seed stage ≫ stageBoundaryMap seed stage =
      stageBoundaryMap seed (stage + 1) ≫
        stageRestrictionMap seed stage := by
  unfold stageRestrictionMap stageBoundaryMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  apply ModuleCat.hom_ext
  exact (restriction_boundary_square seed stage).symm

noncomputable def stageTransition
    (seed : FactorizationPayload) (stage : Nat) :
    stageComplex seed (stage + 1) ⟶ stageComplex seed stage :=
  mappingCoconeMap
    (stageBoundaryMap seed (stage + 1)) (stageBoundaryMap seed stage)
    (stageRestrictionMap seed stage) (stageRestrictionMap seed stage)
    (stageRestriction_boundary_square seed stage)

noncomputable def localTableDiagram (seed : FactorizationPayload) :
    ℕᵒᵖ ⥤ IntegralCochainComplex :=
  Functor.ofOpSequence
    (X := fun stage => stageComplex seed stage)
    (stageTransition seed)

/-- The diagram is calculated from the actual seed payload carried by this
same occurrence. -/
def dependentOccurrence : RootedAccountedUnfolding
    (FactorizationPayload × (ℕᵒᵖ ⥤ IntegralCochainComplex)) :=
  seedOccurrence.map fun seed => (seed, localTableDiagram seed)

def globalFace : RootGeneratedDependentDerivedGlobalStateAt
    dependentOccurrence :=
  RootGeneratedDependentDerivedGlobalStateAt.generate

noncomputable abbrev GlobalState : IntegralCochainComplex :=
  globalFace.globalState

noncomputable def globalRestriction (stage : ℕᵒᵖ) :
    GlobalState ⟶ globalFace.actualDiagram.obj stage :=
  globalFace.restriction stage

theorem globalRestriction_naturality
    {source target : ℕᵒᵖ} (arrow : source ⟶ target) :
    globalRestriction source ≫ globalFace.actualDiagram.map arrow =
      globalRestriction target :=
  globalFace.restriction_naturality arrow

theorem globalFace_preserves_exact_seed_and_local_table :
    globalFace.root = seedOccurrence ∧
      globalFace.actualDiagram = localTableDiagram seedOccurrence.root := by
  constructor
  · rfl
  · rfl

end
end CanonicalUnitArithmeticFactorizationEulerDependentDiagram
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
