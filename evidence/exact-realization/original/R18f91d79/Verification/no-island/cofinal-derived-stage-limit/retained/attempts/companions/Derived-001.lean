import SaturationMonoid.GenericFoundation.Cofinal.Topology.Cochain.SequentialKernel
import SaturationMonoid.GenericFoundation.Cofinal.Topology.Cochain.Tower
import SaturationMonoid.CochainMappingCoconeShortExact

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe w
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedPrimePowerCompletion

open CategoryTheory CategoryTheory.Limits SequentialHomotopyLimit RootGeneratedSequentialHomotopyLimitAt

private theorem stage_transition_surjective {A : Type} [AddCommGroup A] (p : Nat.Primes) (stage : Nat) :
    Function.Surjective (transition (L := A) p stage) := by
  intro lower
  obtain ⟨source, read⟩ := (powerRange (L := A) p stage).mkQ_surjective lower
  exact ⟨stageProjection p (stage+1) source, (LinearMap.congr_fun (transition_projection p stage) source).trans read⟩

variable {Root : Type w} (root : RootedAccountedUnfolding Root)
variable (p : Nat.Primes) (source : CochainComplex AddCommGrpCat ℤ)

local notation "shape" => ComplexShape.up ℤ
local notation "towerAt" => cochainStageTower shape p source
local notation "coneAt" => cochainCompletionCone shape p source

/-- The original cochain tower is a dependent projection of the same source occurrence. -/
def cochainDerivedLimitFace :=
  RootGeneratedSequentialHomotopyLimitAt.generate
    (dependentOccurrence := root.map (fun material => (material, towerAt)))

theorem cochain_derived_limit_root : (cochainDerivedLimitFace root p source).root = root := by
  change (root.map (fun material => (material, towerAt))).map Prod.fst = root
  exact (RootedAccountedUnfolding.map_map Prod.fst (fun material => (material, towerAt)) root).trans
    (RootedAccountedUnfolding.map_id root)

private theorem actual_cochain_transitions_onto (degree : ℤ) (stage : Nat) :
    Function.Surjective (((cochainDerivedLimitFace root p source).transitionAt stage).f degree) := by
  have written : (cochainDerivedLimitFace root p source).transitionAt stage =
      ((stageFunctorTransition p stage).mapHomologicalComplex shape).app source :=
    Functor.ofOpSequence_map_homOfLE_succ _ stage
  rw [written]
  exact stage_transition_surjective (A := source.X degree) p stage

/-- The strict cochain completion maps into the original generated homotopy limit. -/
def cochainDerivedLimitMap : (coneAt).pt ⟶ (cochainDerivedLimitFace root p source).homotopyLimit :=
  CochainMappingCoconeShortExact.liftShortComplex (limitDifferenceSequence (cochainDerivedLimitFace root p source) coneAt)

theorem cochain_derived_limit_quasiIso : QuasiIso (cochainDerivedLimitMap root p source) :=
  CochainMappingCoconeShortExact.quasiIso_liftShortComplex _
    (limit_difference_short_exact (cochainDerivedLimitFace root p source) coneAt
      (cochainCompletionIsLimit shape p source) (actual_cochain_transitions_onto root p source))

theorem cochain_derived_limit_stage (stage : Nat) :
    cochainDerivedLimitMap root p source ≫ (cochainDerivedLimitFace root p source).restriction stage =
      (coneAt).π.app (Opposite.op stage) := by
  let face := cochainDerivedLimitFace root p source
  let sequence := limitDifferenceSequence face coneAt
  exact (Category.assoc (cochainDerivedLimitMap root p source)
    (CochainComplex.mappingCocone.fst face.difference) (face.productProjection stage)).symm.trans
    ((congrArg (fun read => read ≫ face.productProjection stage)
      (CochainMappingCoconeShortExact.liftShortComplex_fst sequence)).trans
      (limit_product_projection face coneAt stage))

end SourceGeneratedPrimePowerCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
