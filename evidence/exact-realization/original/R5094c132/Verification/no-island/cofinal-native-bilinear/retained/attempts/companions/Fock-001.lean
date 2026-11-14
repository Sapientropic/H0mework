import SaturationMonoid.GenericFoundation.Cofinal.Topology.Bilinear.Completion
import SaturationMonoid.LivingLawCanonicalUnitArithmeticRoot

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CanonicalUnitArithmeticRoot

open ArithmeticGeneration RootArithmeticIncidence RootArithmeticUnfoldingFace
open SourceGeneratedPrimePowerCompletion

private abbrev Charges := SourceNativeBinary.Free Current

private def point (history : Current) : Charges := Finsupp.single history 1

private abbrev actualStep (runtime : LivingRuntimeState runtimeFacade.process) :=
  recognition.generateStepAt (temporalVisit runtime.state)

private theorem operation_point (operation : Current → Current → Current) (left right : Current) :
    SourceNativeBinary.linear operation (point left) (point right) = point (operation left right) :=
  SourceNativeBinary.lift_point operation left right

/-- The two source slots of the emitted occurrence supply both operations on the original completion. -/
theorem actual_native_bilinear_completion (runtime : LivingRuntimeState runtimeFacade.process) (p : Nat.Primes) :
    let step := actualStep runtime
    let left := canonicalLinearMap p (point step.material.left)
    let right := canonicalLinearMap p (point step.material.right)
    completionBilinear (SourceNativeBinary.linear UnitHistory.parallel) p left right =
        canonicalLinearMap p (point runtime.tick.next.current.visit.current) ∧
      completionBilinear (SourceNativeBinary.linear UnitHistory.joint) p left right =
        canonicalLinearMap p (point (jointFold step)) ∧
      HEq step.generated.occurrence runtime.emittedOccurrence ∧
      HEq step.wholeLedgerWriteBack runtime.tick.generated.wholeLedgerWriteBack ∧
      step.nextCurrent = runtime.tick.nextCurrent ∧
      type_of% (RootArithmeticIncidenceStepAt.installedMaterial_factorizes step) := by
  let step := actualStep runtime
  let left := point step.material.left
  let right := point step.material.right
  have next : step.material.left.parallel step.material.right = runtime.tick.next.current.visit.current := rfl
  have sibling := (operation_point UnitHistory.parallel step.material.left step.material.right).trans
    (congrArg point next)
  have dependent := (operation_point UnitHistory.joint step.material.left step.material.right).trans
    (congrArg point (jointFold_eq step).symm)
  refine ⟨(completion_bilinear_source (SourceNativeBinary.linear UnitHistory.parallel) p left right).trans
      (congrArg (canonicalLinearMap p) sibling),
    (completion_bilinear_source (SourceNativeBinary.linear UnitHistory.joint) p left right).trans
      (congrArg (canonicalLinearMap p) dependent), ?_, ?_, ?_, step.installedMaterial_factorizes⟩
  · rfl
  · rfl
  · rfl

private theorem source_power_visible (p : Nat.Primes) (depth : Nat) (target : Current) :
    stageProjection p depth ((p.1 : ℤ)^depth • point target) ≠ 0 := by
  intro zero
  obtain ⟨divided, paid⟩ := (stageProjection_eq_zero_iff p depth _).mp zero
  have coefficient := congrArg (fun word : Charges => word target) paid
  change ((p.1 : ℤ)^(depth+1) • divided) target = ((p.1 : ℤ)^depth • point target) target at coefficient
  simp only [Finsupp.smul_apply, point, Finsupp.single_eq_same, smul_eq_mul, mul_one] at coefficient
  have divides : (p.1 : ℤ)^(depth+1) ∣ (p.1 : ℤ)^depth := ⟨divided target, coefficient.symm⟩
  have primeNonzero : (p.1 : ℤ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have bound := Int.natAbs_le_of_dvd_ne_zero divides (pow_ne_zero depth primeNonzero)
  simp only [Int.natAbs_pow, Int.natAbs_natCast] at bound
  exact (Nat.pow_lt_pow_right p.property.one_lt (Nat.lt_succ_self depth)).not_ge bound

/-- The original parallel output detects the first visible depth of the joint increment. -/
theorem actual_native_parallel_joint_depth (runtime : LivingRuntimeState runtimeFacade.process)
    (p : Nat.Primes) (j k : Nat) :
    let step := actualStep runtime
    let left := (p.1 : ℤ)^(j+1) • point step.material.left
    let right := (p.1 : ℤ)^(k+1) • point step.material.right
    let effect := SourceNativeBinary.linear UnitHistory.parallel left right
    stageProjection p (j+k+1) effect = 0 ∧ stageProjection p (j+k+2) effect ≠ 0 := by
  let step := actualStep runtime
  let left := point step.material.left
  let right := point step.material.right
  let act := SourceNativeBinary.linear UnitHistory.parallel
  let a := (p.1 : ℤ)^(j+1)
  let b := (p.1 : ℤ)^(k+1)
  have output : act left right = point runtime.tick.next.current.visit.current :=
    operation_point UnitHistory.parallel step.material.left step.material.right
  have leftZero : stageProjection p j (a • left) = 0 :=
    (stageProjection_eq_zero_iff p j _).mpr ⟨left, rfl⟩
  have rightZero : stageProjection p k (b • right) = 0 :=
    (stageProjection_eq_zero_iff p k _).mpr ⟨right, rfl⟩
  refine ⟨stage_bilinear_joint_vanish act p j k _ _ leftZero rightZero, ?_⟩
  have exactEffect : act (a • left) (b • right) =
      (p.1 : ℤ)^(j+k+2) • point runtime.tick.next.current.visit.current := by
    calc
      _ = a • act left (b • right) := LinearMap.congr_fun (map_smul act a left) _
      _ = a • (b • act left right) := congrArg (fun value => a • value) (map_smul (act left) b right)
      _ = _ := by
        rw [output]
        dsimp only [a,b]
        rw [smul_smul, ← pow_add, show j+1+(k+1) = j+k+2 by omega]
  intro invisible
  exact source_power_visible p (j+k+2) runtime.tick.next.current.visit.current
    ((congrArg (stageProjection p (j+k+2)) exactEffect).symm.trans invisible)

end CanonicalUnitArithmeticRoot
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
