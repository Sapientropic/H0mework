import H0mework.Foundation.Cofinal.KernelCompletion

/-!
# Root-generated cofinal coverage-residual tower

The residual of a cofinal kernel completion is not an isolated quotient.
Every finite evaluator already generates its own coverage quotient, and the
actual carrier transitions generate a tower of those quotients.  The
completed coverage residual maps canonically into the limit of this finite
residual history.

The map is injective.  Indeed, a compatible carrier state whose finite
residual coordinates all vanish has unique stage lifts through the
stagewise faithful source quotients; those lifts form an element of the
source completion.  Thus no completed obstruction can disappear when the
finite/cofinal incidence history is exposed.

The mouth accepts no residual tower, lifts, compatible family, limit,
injectivity certificate or zero receipt.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalCoverageResidualTower

open CategoryTheory
open CategoryTheory.Limits
open CofinalKernelCompletion
open CofinalKernelCompletion.RootGeneratedCofinalKernelCompletionAt

noncomputable section

universe u w

structure RootGeneratedCofinalCoverageResidualTowerAt
    {Root : Type w} {Generator : Type u} [AddCommGroup Generator]
    {Carrier : Nat → Type u} [∀ stage, AddCommGroup (Carrier stage)]
    {dependentOccurrence : RootedAccountedUnfolding
      (Root × AdditiveCofinalEvaluatorData Generator Carrier)}
    (completionFace : RootGeneratedCofinalKernelCompletionAt
      dependentOccurrence)
    (calculation :
      RootGeneratedCofinalKernelCompletionAt.GeneratedCompatibilityCalculationAt
        completionFace) : Type (max u w) where
  private mk ::

namespace RootGeneratedCofinalCoverageResidualTowerAt

variable {Root : Type w} {Generator : Type u} [AddCommGroup Generator]
variable {Carrier : Nat → Type u} [∀ stage, AddCommGroup (Carrier stage)]
variable {dependentOccurrence : RootedAccountedUnfolding
  (Root × AdditiveCofinalEvaluatorData Generator Carrier)}
variable {completionFace : RootGeneratedCofinalKernelCompletionAt
  dependentOccurrence}
variable {calculation :
  RootGeneratedCofinalKernelCompletionAt.GeneratedCompatibilityCalculationAt
    completionFace}

def generate : RootGeneratedCofinalCoverageResidualTowerAt
    completionFace calculation :=
  ⟨⟩

def root
    (_face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation) :=
  completionFace.root

/-- Finite coverage residual at one actual evaluator stage. -/
abbrev StageCoverageResidual
    (_face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation)
    (stage : Nat) :=
  Carrier stage ⧸ (completionFace.evaluator stage).range

/-- The actual carrier transition descends to finite coverage residuals. -/
def residualTransition
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation)
    (stage : Nat) :
    face.StageCoverageResidual (stage + 1) →+
      face.StageCoverageResidual stage :=
  QuotientAddGroup.map
    (completionFace.evaluator (stage + 1)).range
    (completionFace.evaluator stage).range
    (completionFace.transition stage) (by
      rintro value ⟨generator, rfl⟩
      refine ⟨generator, ?_⟩
      exact (DFunLike.congr_fun (calculation.laws stage) generator).symm)

@[reducible] noncomputable def residualTower
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation) :
    ℕᵒᵖ ⥤ AddCommGrpCat :=
  Functor.ofOpSequence
    (X := fun stage ↦ AddCommGrpCat.of (face.StageCoverageResidual stage))
    (fun stage ↦ AddCommGrpCat.ofHom (face.residualTransition stage))

def stageResidualProjection
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation)
    (stage : Nat) : Carrier stage →+ face.StageCoverageResidual stage :=
  QuotientAddGroup.mk' (completionFace.evaluator stage).range

noncomputable def residualProjectionNatTrans
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation) :
    completionFace.carrierTower ⟶ face.residualTower :=
  NatTrans.ofOpSequence
    (fun stage ↦ AddCommGrpCat.ofHom (face.stageResidualProjection stage))
    (fun stage ↦ by
      simp only [RootGeneratedCofinalKernelCompletionAt.carrierTower,
        residualTower, Functor.ofOpSequence_map_homOfLE_succ]
      apply AddCommGrpCat.ext
      intro value
      rfl)

@[simp] theorem realizationNatTrans_app
    (_face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation)
    (stage : Nat) :
    (completionFace.realizationNatTrans calculation).app
        (Opposite.op stage) =
      AddCommGrpCat.ofHom (completionFace.stageRealization stage) :=
  rfl

@[simp] theorem residualProjectionNatTrans_app
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation)
    (stage : Nat) :
    face.residualProjectionNatTrans.app (Opposite.op stage) =
      AddCommGrpCat.ofHom (face.stageResidualProjection stage) :=
  rfl

noncomputable def residualLimit
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation) : AddCommGrpCat :=
  limit face.residualTower

noncomputable def residualRestriction
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation)
    (stage : Nat) :
    face.residualLimit ⟶
      AddCommGrpCat.of (face.StageCoverageResidual stage) :=
  limit.π face.residualTower (Opposite.op stage)

theorem residualTower_map_succ
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation)
    (stage : Nat) :
    face.residualTower.map (homOfLE (Nat.le_add_right stage 1)).op =
      AddCommGrpCat.ofHom (face.residualTransition stage) := by
  unfold residualTower
  change (Functor.ofOpSequence
      (X := fun current ↦
        AddCommGrpCat.of (face.StageCoverageResidual current))
      (fun current ↦ AddCommGrpCat.ofHom
        (face.residualTransition current))).map
          (homOfLE (Nat.le_add_right stage 1)).op =
    AddCommGrpCat.ofHom (face.residualTransition stage)
  exact Functor.ofOpSequence_map_homOfLE_succ
    (X := fun current ↦
      AddCommGrpCat.of (face.StageCoverageResidual current))
    (fun current ↦ AddCommGrpCat.ofHom
      (face.residualTransition current)) stage

theorem residualRestriction_step
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation)
    (stage : Nat) :
    face.residualRestriction (stage + 1) ≫
        AddCommGrpCat.ofHom (face.residualTransition stage) =
      face.residualRestriction stage := by
  rw [← face.residualTower_map_succ stage]
  exact limit.w face.residualTower
    (homOfLE (Nat.le_add_right stage 1)).op

/-- Actual compatible carrier states project to the cofinal limit of their
finite coverage residuals. -/
noncomputable def carrierToResidualLimit
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation) :
    completionFace.carrierLimit ⟶ face.residualLimit :=
  limMap face.residualProjectionNatTrans

@[reassoc (attr := simp)] theorem carrierToResidualLimit_π
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation)
    (stage : Nat) :
    face.carrierToResidualLimit ≫
        limit.π face.residualTower (Opposite.op stage) =
      completionFace.carrierRestriction stage ≫
        AddCommGrpCat.ofHom (face.stageResidualProjection stage) :=
  limMap_π face.residualProjectionNatTrans (Opposite.op stage)

theorem stageRealization_residualProjection
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation)
    (stage : Nat) :
    AddCommGrpCat.ofHom (completionFace.stageRealization stage) ≫
        AddCommGrpCat.ofHom (face.stageResidualProjection stage) = 0 := by
  apply AddCommGrpCat.ext
  intro quotient
  induction quotient using QuotientAddGroup.induction_on with
  | H generator =>
      change (completionFace.evaluator stage generator :
        face.StageCoverageResidual stage) = 0
      exact QuotientAddGroup.eq_zero_iff
        (completionFace.evaluator stage generator) |>.2 ⟨generator, rfl⟩

/-- The source completion is killed by every finite coverage quotient. -/
theorem completionRealization_carrierToResidualLimit
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation) :
    completionFace.completionRealization calculation ≫
        face.carrierToResidualLimit = 0 := by
  unfold RootGeneratedCofinalKernelCompletionAt.completionRealization
    RootGeneratedCofinalKernelCompletionAt.carrierLimit
    RootGeneratedCofinalKernelCompletionAt.completion
    carrierToResidualLimit residualLimit
  apply limit.hom_ext
  intro index
  rcases index with ⟨stage⟩
  rw [Category.assoc, limMap_π, ← Category.assoc, limMap_π,
    Category.assoc]
  rw [face.realizationNatTrans_app stage,
    face.residualProjectionNatTrans_app stage, Limits.zero_comp]
  apply AddCommGrpCat.ext
  intro sourceState
  change face.stageResidualProjection stage
      (completionFace.stageRealization stage
        ((completionFace.restriction calculation stage).hom sourceState)) = 0
  have killed := CategoryTheory.ConcreteCategory.congr_hom
    (face.stageRealization_residualProjection stage)
      ((completionFace.restriction calculation stage).hom sourceState)
  simpa using killed

/-- The remaining completed residual maps canonically into the cofinal
finite-residual history. -/
noncomputable def completionResidualToResidualLimit
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation) :
    completionFace.CompletionResidual calculation →+
      face.residualLimit :=
  QuotientAddGroup.lift
    (completionFace.completionRealization calculation).hom.range
    face.carrierToResidualLimit.hom (by
      rintro state ⟨sourceState, rfl⟩
      have zeroComposite := congrArg
        (fun morphism => morphism.hom sourceState)
        face.completionRealization_carrierToResidualLimit
      simpa using zeroComposite)

private def elementHom {Group : Type u} [AddCommGroup Group]
    (element : Group) : ULift.{u, 0} ℤ →+ Group where
  toFun integer := integer.down • element
  map_zero' := by simp
  map_add' left right := by simp [add_zsmul]

theorem stageSourceLift_exists
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation)
    (state : completionFace.carrierLimit)
    (stateKernel : state ∈ face.carrierToResidualLimit.hom.ker)
    (stage : Nat) :
    ∃ sourceStage : completionFace.StageQuotient stage,
      completionFace.stageRealization stage sourceStage =
        completionFace.carrierRestriction stage state := by
  have residualZero : face.carrierToResidualLimit state = 0 :=
    AddMonoidHom.mem_ker.mp stateKernel
  have projectedZero := congrArg
    (fun residualState =>
      (limit.π face.residualTower (Opposite.op stage)).hom residualState)
    residualZero
  have projectedZero' :
      (limit.π face.residualTower (Opposite.op stage)).hom
          (face.carrierToResidualLimit state) = 0 := by
    exact projectedZero.trans
      (map_zero (limit.π face.residualTower (Opposite.op stage)).hom)
  have projectionIdentity := CategoryTheory.ConcreteCategory.congr_hom
    (face.carrierToResidualLimit_π stage) state
  change
    (limit.π face.residualTower (Opposite.op stage)).hom
        (face.carrierToResidualLimit state) =
      face.stageResidualProjection stage
        (completionFace.carrierRestriction stage state)
    at projectionIdentity
  have stageResidualZero :
      face.stageResidualProjection stage
          (completionFace.carrierRestriction stage state) = 0 := by
    exact projectionIdentity.symm.trans projectedZero'
  have rangeMembership :
      completionFace.carrierRestriction stage state ∈
        (completionFace.evaluator stage).range :=
    QuotientAddGroup.eq_zero_iff
      (completionFace.carrierRestriction stage state) |>.1 stageResidualZero
  obtain ⟨generator, generator_eq⟩ := rangeMembership
  refine ⟨completionFace.quotientMap stage generator, ?_⟩
  change completionFace.evaluator stage generator =
    completionFace.carrierRestriction stage state
  exact generator_eq

noncomputable def stageSourceLift
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation)
    (state : completionFace.carrierLimit)
    (stateKernel : state ∈ face.carrierToResidualLimit.hom.ker)
    (stage : Nat) : completionFace.StageQuotient stage :=
  Classical.choose (face.stageSourceLift_exists state stateKernel stage)

theorem stageSourceLift_realizes
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation)
    (state : completionFace.carrierLimit)
    (stateKernel : state ∈ face.carrierToResidualLimit.hom.ker)
    (stage : Nat) :
    completionFace.stageRealization stage
        (face.stageSourceLift state stateKernel stage) =
      completionFace.carrierRestriction stage state :=
  Classical.choose_spec (face.stageSourceLift_exists state stateKernel stage)

theorem stageRealization_transition
    (_face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation)
    (stage : Nat) :
    (completionFace.stageRealization stage).comp
        (completionFace.quotientTransition calculation stage) =
      (completionFace.transition stage).comp
        (completionFace.stageRealization (stage + 1)) := by
  apply AddMonoidHom.ext
  intro quotient
  induction quotient using QuotientAddGroup.induction_on with
  | H generator =>
      change completionFace.evaluator stage generator =
        completionFace.transition stage
          (completionFace.evaluator (stage + 1) generator)
      exact (DFunLike.congr_fun (calculation.laws stage) generator).symm

theorem carrierTower_map_succ
    (_face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation)
    (stage : Nat) :
    completionFace.carrierTower.map
        (homOfLE (Nat.le_add_right stage 1)).op =
      AddCommGrpCat.ofHom (completionFace.transition stage) := by
  unfold RootGeneratedCofinalKernelCompletionAt.carrierTower
  change (Functor.ofOpSequence
      (X := fun current ↦ AddCommGrpCat.of (Carrier current))
      (fun current ↦ AddCommGrpCat.ofHom
        (completionFace.transition current))).map
          (homOfLE (Nat.le_add_right stage 1)).op =
    AddCommGrpCat.ofHom (completionFace.transition stage)
  exact Functor.ofOpSequence_map_homOfLE_succ
    (X := fun current ↦ AddCommGrpCat.of (Carrier current))
    (fun current ↦ AddCommGrpCat.ofHom
      (completionFace.transition current)) stage

theorem carrierRestriction_step
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation)
    (stage : Nat) :
    completionFace.carrierRestriction (stage + 1) ≫
        AddCommGrpCat.ofHom (completionFace.transition stage) =
      completionFace.carrierRestriction stage := by
  rw [← face.carrierTower_map_succ stage]
  exact limit.w completionFace.carrierTower
    (homOfLE (Nat.le_add_right stage 1)).op

theorem stageSourceLift_transition
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation)
    (state : completionFace.carrierLimit)
    (stateKernel : state ∈ face.carrierToResidualLimit.hom.ker)
    (stage : Nat) :
    completionFace.quotientTransition calculation stage
        (face.stageSourceLift state stateKernel (stage + 1)) =
      face.stageSourceLift state stateKernel stage := by
  apply completionFace.stageRealization_injective stage
  have realizationTransition := DFunLike.congr_fun
    (face.stageRealization_transition stage)
    (face.stageSourceLift state stateKernel (stage + 1))
  have carrierStep := CategoryTheory.ConcreteCategory.congr_hom
    (face.carrierRestriction_step stage) state
  calc
    completionFace.stageRealization stage
        (completionFace.quotientTransition calculation stage
          (face.stageSourceLift state stateKernel (stage + 1))) =
        ((completionFace.stageRealization stage).comp
          (completionFace.quotientTransition calculation stage))
            (face.stageSourceLift state stateKernel (stage + 1)) := rfl
    _ = ((completionFace.transition stage).comp
          (completionFace.stageRealization (stage + 1)))
            (face.stageSourceLift state stateKernel (stage + 1)) :=
      realizationTransition
    _ = completionFace.transition stage
          (completionFace.stageRealization (stage + 1)
            (face.stageSourceLift state stateKernel (stage + 1))) := rfl
    _ = completionFace.transition stage
          (completionFace.carrierRestriction (stage + 1) state) := by
      exact congrArg (completionFace.transition stage)
        (face.stageSourceLift_realizes state stateKernel (stage + 1))
    _ = completionFace.carrierRestriction stage state := by
      simpa using carrierStep
    _ = completionFace.stageRealization stage
          (face.stageSourceLift state stateKernel stage) :=
      (face.stageSourceLift_realizes state stateKernel stage).symm

noncomputable def kernelSourceLiftCone
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation)
    (state : completionFace.carrierLimit)
    (stateKernel : state ∈ face.carrierToResidualLimit.hom.ker) :
    Cone (completionFace.quotientTower calculation) :=
  Cone.mk (AddCommGrpCat.of (ULift.{u, 0} ℤ))
    (NatTrans.ofOpSequence
      (fun stage ↦ AddCommGrpCat.ofHom
        (elementHom (face.stageSourceLift state stateKernel stage)))
      (fun stage ↦ by
        simp only [Functor.const_obj_map,
          RootGeneratedCofinalKernelCompletionAt.quotientTower,
          Functor.ofOpSequence_map_homOfLE_succ]
        apply AddCommGrpCat.ext
        intro integer
        change ULift.{u, 0} ℤ at integer
        rcases integer with ⟨integer⟩
        change integer • face.stageSourceLift state stateKernel stage =
          completionFace.quotientTransition calculation stage
            (integer • face.stageSourceLift state stateKernel (stage + 1))
        rw [map_zsmul, face.stageSourceLift_transition state stateKernel stage]))

noncomputable def kernelSourceLift
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation)
    (state : completionFace.carrierLimit)
    (stateKernel : state ∈ face.carrierToResidualLimit.hom.ker) :
    AddCommGrpCat.of (ULift.{u, 0} ℤ) ⟶
      completionFace.completion calculation :=
  limit.lift (completionFace.quotientTower calculation)
    (face.kernelSourceLiftCone state stateKernel)

@[reassoc (attr := simp)] theorem kernelSourceLift_π
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation)
    (state : completionFace.carrierLimit)
    (stateKernel : state ∈ face.carrierToResidualLimit.hom.ker)
    (stage : Nat) :
    face.kernelSourceLift state stateKernel ≫
        completionFace.restriction calculation stage =
      AddCommGrpCat.ofHom
        (elementHom (face.stageSourceLift state stateKernel stage)) :=
  limit.lift_π (face.kernelSourceLiftCone state stateKernel)
    (Opposite.op stage)

theorem kernelSourceLift_realizes
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation)
    (state : completionFace.carrierLimit)
    (stateKernel : state ∈ face.carrierToResidualLimit.hom.ker) :
    face.kernelSourceLift state stateKernel ≫
        completionFace.completionRealization calculation =
      AddCommGrpCat.ofHom (elementHom state) := by
  apply (limit.isLimit completionFace.carrierTower).hom_ext
  intro index
  rcases index with ⟨stage⟩
  change (face.kernelSourceLift state stateKernel ≫
      completionFace.completionRealization calculation) ≫
        completionFace.carrierRestriction stage =
    AddCommGrpCat.ofHom (elementHom state) ≫
      completionFace.carrierRestriction stage
  rw [Category.assoc,
    completionFace.completionRealization_carrierRestriction,
    ← Category.assoc]
  apply AddCommGrpCat.ext
  intro integer
  change ULift.{u, 0} ℤ at integer
  have sourceProjection := CategoryTheory.ConcreteCategory.congr_hom
    (face.kernelSourceLift_π state stateKernel stage) integer
  rcases integer with ⟨integer⟩
  change completionFace.stageRealization stage
      ((completionFace.restriction calculation stage).hom
          ((face.kernelSourceLift state stateKernel).hom ⟨integer⟩)) =
    (completionFace.carrierRestriction stage).hom (integer • state)
  have sourceProjection' :
      (completionFace.restriction calculation stage).hom
          ((face.kernelSourceLift state stateKernel).hom ⟨integer⟩) =
        integer • face.stageSourceLift state stateKernel stage := by
    exact sourceProjection.trans rfl
  rw [sourceProjection']
  change completionFace.stageRealization stage
      (integer • face.stageSourceLift state stateKernel stage) =
    (completionFace.carrierRestriction stage).hom (integer • state)
  rw [map_zsmul, map_zsmul,
    face.stageSourceLift_realizes state stateKernel stage]

theorem carrierToResidualLimit_kernel_le_completion_range
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation) :
    face.carrierToResidualLimit.hom.ker ≤
      (completionFace.completionRealization calculation).hom.range := by
  intro state stateKernel
  refine ⟨(face.kernelSourceLift state stateKernel).hom (ULift.up 1), ?_⟩
  have realized := CategoryTheory.ConcreteCategory.congr_hom
    (face.kernelSourceLift_realizes state stateKernel) (ULift.up 1)
  simpa [elementHom] using realized

/-- No completed residual is lost by passage to the cofinal history of
finite coverage residuals. -/
theorem completionResidualToResidualLimit_injective
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation) :
    Function.Injective face.completionResidualToResidualLimit := by
  apply (AddMonoidHom.ker_eq_bot_iff
    face.completionResidualToResidualLimit).mp
  rw [completionResidualToResidualLimit, QuotientAddGroup.ker_lift]
  apply (AddSubgroup.map_eq_bot_iff
    face.carrierToResidualLimit.hom.ker).2
  intro state stateKernel
  exact QuotientAddGroup.eq_zero_iff state |>.2
    (face.carrierToResidualLimit_kernel_le_completion_range stateKernel)

/-- Rigidity of the generated cofinal finite-residual history is sufficient
to settle the original completed coverage residual. -/
theorem completionResidual_subsingleton_of_residualLimit_subsingleton
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation)
    (historyRigid : Subsingleton face.residualLimit) :
    Subsingleton (completionFace.CompletionResidual calculation) := by
  constructor
  intro left right
  apply face.completionResidualToResidualLimit_injective
  exact historyRigid.elim _ _

theorem generatedCoverageResidualZero_of_residualLimit_subsingleton
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation)
    (historyRigid : Subsingleton face.residualLimit) :
    RootGeneratedCofinalKernelCompletionAt.GeneratedCoverageResidualZeroAt
      completionFace calculation :=
  completionFace.generateCoverageResidualZero calculation
    (face.completionResidual_subsingleton_of_residualLimit_subsingleton
      historyRigid)

/-! ## Exact finite coordinate of a persistent history -/

structure GeneratedFiniteResidualCoordinateObstructionAt
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation) : Type u where
  private mk ::
  left : face.residualLimit
  right : face.residualLimit
  stage : Nat
  coordinate_ne :
    (face.residualRestriction stage).hom left ≠
      (face.residualRestriction stage).hom right
  coordinate_eq_before : ∀ prior, prior < stage →
    (face.residualRestriction prior).hom left =
      (face.residualRestriction prior).hom right

theorem residualLimit_exists_finite_coordinate_ne
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation)
    {left right : face.residualLimit} (distinct : left ≠ right) :
    ∃ stage,
      (face.residualRestriction stage).hom left ≠
        (face.residualRestriction stage).hom right := by
  by_contra noCoordinate
  push Not at noCoordinate
  apply distinct
  have elementHom_eq :
      (AddCommGrpCat.ofHom (elementHom left) :
          AddCommGrpCat.of (ULift.{u, 0} ℤ) ⟶ face.residualLimit) =
        AddCommGrpCat.ofHom (elementHom right) := by
    apply (limit.isLimit face.residualTower).hom_ext
    intro index
    rcases index with ⟨stage⟩
    change AddCommGrpCat.ofHom (elementHom left) ≫
        face.residualRestriction stage =
      AddCommGrpCat.ofHom (elementHom right) ≫
        face.residualRestriction stage
    apply AddCommGrpCat.ext
    intro integer
    change (face.residualRestriction stage).hom
        (elementHom left integer) =
      (face.residualRestriction stage).hom
        (elementHom right integer)
    change ULift.{u, 0} ℤ at integer
    rcases integer with ⟨integer⟩
    change (face.residualRestriction stage).hom
        (integer • left) =
      (face.residualRestriction stage).hom
        (integer • right)
    rw [map_zsmul, map_zsmul, noCoordinate stage]
  have atOne := CategoryTheory.ConcreteCategory.congr_hom
    elementHom_eq (ULift.up 1)
  have atOne' : (1 : ℤ) • left = (1 : ℤ) • right :=
    atOne.trans rfl
  simpa using atOne'

namespace GeneratedFiniteResidualCoordinateObstructionAt

variable {face : RootGeneratedCofinalCoverageResidualTowerAt
  completionFace calculation}

def residualCoordinate
    (obstruction : GeneratedFiniteResidualCoordinateObstructionAt
      (completionFace := completionFace) (calculation := calculation) face) :
    face.StageCoverageResidual obstruction.stage :=
  (face.residualRestriction obstruction.stage).hom obstruction.left -
    (face.residualRestriction obstruction.stage).hom obstruction.right

theorem residualCoordinate_ne_zero
    (obstruction : GeneratedFiniteResidualCoordinateObstructionAt
      (completionFace := completionFace) (calculation := calculation) face) :
    obstruction.residualCoordinate ≠ 0 :=
  sub_ne_zero.mpr obstruction.coordinate_ne

theorem residualCoordinate_transition_eq_zero_of_stage_eq_succ
    (obstruction : GeneratedFiniteResidualCoordinateObstructionAt
      (completionFace := completionFace) (calculation := calculation) face)
    (prior : Nat) (stage_eq : obstruction.stage = prior + 1) :
    face.residualTransition prior
        (cast (congrArg (fun stage ↦ face.StageCoverageResidual stage)
          stage_eq) obstruction.residualCoordinate) = 0 := by
  rcases obstruction with ⟨left, right, stage, coordinate_ne,
    coordinate_eq_before⟩
  dsimp only at stage_eq ⊢
  subst stage
  have leftStep := CategoryTheory.ConcreteCategory.congr_hom
    (face.residualRestriction_step prior) left
  have rightStep := CategoryTheory.ConcreteCategory.congr_hom
    (face.residualRestriction_step prior) right
  change face.residualTransition prior
      ((face.residualRestriction (prior + 1)).hom left) =
    (face.residualRestriction prior).hom left at leftStep
  change face.residualTransition prior
      ((face.residualRestriction (prior + 1)).hom right) =
    (face.residualRestriction prior).hom right at rightStep
  change face.residualTransition prior
      ((face.residualRestriction (prior + 1)).hom left -
        (face.residualRestriction (prior + 1)).hom right) = 0
  rw [map_sub]
  change face.residualTransition prior
        ((face.residualRestriction (prior + 1)).hom left) -
      face.residualTransition prior
        ((face.residualRestriction (prior + 1)).hom right) = 0
  rw [leftStep, rightStep,
    coordinate_eq_before prior (Nat.lt_add_one prior), sub_self]

/-- A representative in the actual finite carrier, generated from the
nonzero quotient coordinate. -/
noncomputable def representative
    (obstruction : GeneratedFiniteResidualCoordinateObstructionAt
      (completionFace := completionFace) (calculation := calculation) face) :
    Carrier obstruction.stage :=
  Classical.choose
    (QuotientAddGroup.mk'_surjective
      (completionFace.evaluator obstruction.stage).range
      obstruction.residualCoordinate)

theorem representative_class
    (obstruction : GeneratedFiniteResidualCoordinateObstructionAt
      (completionFace := completionFace) (calculation := calculation) face) :
    face.stageResidualProjection obstruction.stage
        obstruction.representative = obstruction.residualCoordinate :=
  Classical.choose_spec
    (QuotientAddGroup.mk'_surjective
      (completionFace.evaluator obstruction.stage).range
      obstruction.residualCoordinate)

theorem representative_not_mem_sourceRange
    (obstruction : GeneratedFiniteResidualCoordinateObstructionAt
      (completionFace := completionFace) (calculation := calculation) face) :
    obstruction.representative ∉
      (completionFace.evaluator obstruction.stage).range := by
  intro sourceRange
  have representativeZero :
      face.stageResidualProjection obstruction.stage
        obstruction.representative = 0 :=
    QuotientAddGroup.eq_zero_iff obstruction.representative |>.2 sourceRange
  exact obstruction.residualCoordinate_ne_zero
    (obstruction.representative_class.symm.trans representativeZero)

/-- The negative branch's finite representative is re-exposed with every
branch of the original rooted evaluator occurrence. -/
noncomputable def representativeOccurrence
    (obstruction : GeneratedFiniteResidualCoordinateObstructionAt
      (completionFace := completionFace) (calculation := calculation) face) :
    RootedAccountedUnfolding (Root × (Σ stage, Carrier stage)) :=
  dependentOccurrence.map fun payload ↦
    (payload.1, ⟨obstruction.stage, obstruction.representative⟩)

theorem representativeOccurrence_root
    (obstruction : GeneratedFiniteResidualCoordinateObstructionAt
      (completionFace := completionFace) (calculation := calculation) face) :
    obstruction.representativeOccurrence.map Prod.fst = face.root := by
  unfold representativeOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change dependentOccurrence.map Prod.fst = completionFace.root
  rfl

@[simp] theorem representativeOccurrence_payload
    (obstruction : GeneratedFiniteResidualCoordinateObstructionAt
      (completionFace := completionFace) (calculation := calculation) face) :
    obstruction.representativeOccurrence.root.2 =
      ⟨obstruction.stage, obstruction.representative⟩ := by
  unfold representativeOccurrence
  rw [RootedAccountedUnfolding.root_map]

end GeneratedFiniteResidualCoordinateObstructionAt

inductive ResidualHistorySettlementOutcome
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation) : Type u
  | rigid (historyRigid : Subsingleton face.residualLimit)
  | finiteCoordinateObstruction
      (obstruction : GeneratedFiniteResidualCoordinateObstructionAt face)

/-- Honest total settlement of the generated finite/cofinal history.  The
negative branch contains an actual finite carrier representative outside
the source evaluator range. -/
noncomputable def settleResidualHistory
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation) :
    ResidualHistorySettlementOutcome face := by
  classical
  by_cases historyRigid : Subsingleton face.residualLimit
  · exact .rigid historyRigid
  · letI : Nontrivial face.residualLimit :=
      not_subsingleton_iff_nontrivial.mp historyRigid
    let pairWitness := exists_pair_ne face.residualLimit
    let left := Classical.choose pairWitness
    let right := Classical.choose (Classical.choose_spec pairWitness)
    have distinct : left ≠ right :=
      Classical.choose_spec (Classical.choose_spec pairWitness)
    let coordinateWitness :=
      face.residualLimit_exists_finite_coordinate_ne distinct
    let stage := Nat.find coordinateWitness
    have coordinate_ne := Nat.find_spec coordinateWitness
    have coordinate_eq_before : ∀ prior, prior < stage →
        (face.residualRestriction prior).hom left =
          (face.residualRestriction prior).hom right := by
      intro prior prior_lt
      by_contra coordinate_ne_prior
      exact (not_lt_of_ge
        (Nat.find_min' coordinateWitness coordinate_ne_prior)) prior_lt
    exact .finiteCoordinateObstruction
      ⟨left, right, stage, coordinate_ne, coordinate_eq_before⟩

/-- The exact root and every branch are retained when the completed
residual carrier is exposed as a downstream occurrence. -/
noncomputable def completionResidualOccurrence
    (_face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation) :
    RootedAccountedUnfolding (Root × AddCommGrpCat) :=
  dependentOccurrence.map fun payload ↦
    (payload.1, AddCommGrpCat.of
      (completionFace.CompletionResidual calculation))

/-- The same branch-preserving exposure of the finite residual tower. -/
noncomputable def residualTowerOccurrence
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation) :
    RootedAccountedUnfolding (Root × (ℕᵒᵖ ⥤ AddCommGrpCat)) :=
  dependentOccurrence.map fun payload ↦ (payload.1, face.residualTower)

theorem preserves_root_residual_and_tower
    (face : RootGeneratedCofinalCoverageResidualTowerAt
      completionFace calculation) :
    (face.completionResidualOccurrence.map Prod.fst) = face.root ∧
      (face.residualTowerOccurrence.map Prod.fst) = face.root ∧
      Function.Injective face.completionResidualToResidualLimit := by
  refine ⟨?_, ?_, face.completionResidualToResidualLimit_injective⟩
  · unfold completionResidualOccurrence root
    rw [RootedAccountedUnfolding.map_map]
    change dependentOccurrence.map Prod.fst = completionFace.root
    rfl
  · unfold residualTowerOccurrence root
    rw [RootedAccountedUnfolding.map_map]
    change dependentOccurrence.map Prod.fst = completionFace.root
    rfl

end RootGeneratedCofinalCoverageResidualTowerAt
end
end CofinalCoverageResidualTower
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
