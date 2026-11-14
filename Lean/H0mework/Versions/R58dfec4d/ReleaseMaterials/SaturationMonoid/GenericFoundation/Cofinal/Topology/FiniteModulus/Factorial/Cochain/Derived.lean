import H0mework.Versions.R58dfec4d.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.FiniteModulus.Factorial.Cochain.Tower
import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Cochain.DerivedNaturality

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalAllPrimeTopology

open CategoryTheory CategoryTheory.Limits SequentialHomotopyLimit SequentialHomotopyLimitNaturality
open RootGeneratedSequentialHomotopyLimitAt CochainMappingCoconeShortExact
open private limit_product_naturality lift_short_complex_naturality from
  H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Cochain.DerivedNaturality

local notation "shape" => ComplexShape.up ℤ
variable {Root : Type u} (root : RootedAccountedUnfolding Root) (source : CochainComplex AddCommGrpCat ℤ)

local notation "towerAt" => factorialCochainTower shape source
local notation "coneAt" => factorialCochainCone shape source

/-- The original root carries the whole factorial cochain tower in its dependent projection. -/
def factorialDerivedLimitFace :=
  RootGeneratedSequentialHomotopyLimitAt.generate (dependentOccurrence := .occur (root.root, towerAt)
    (RootedAccountedUnfolding.mapBranches (fun material => (material, towerAt)) root.branches))

theorem factorial_derived_limit_root : (factorialDerivedLimitFace root source).root = root := by
  cases root with
  | occur material branches =>
    let occurrence : RootedAccountedUnfolding Root := .occur material branches
    change (occurrence.map (fun label => (label, towerAt))).map Prod.fst = occurrence
    exact (RootedAccountedUnfolding.map_map Prod.fst (fun label => (label, towerAt)) occurrence).trans
      (RootedAccountedUnfolding.map_id occurrence)

private theorem factorial_transition_degree_onto (degree : ℤ) (stage : Nat) :
    Function.Surjective (((factorialDerivedLimitFace root source).transitionAt stage).f degree) := by
  have written : (factorialDerivedLimitFace root source).transitionAt stage =
      ((factorialStageTransition stage).mapHomologicalComplex shape).app source :=
    Functor.ofOpSequence_map_homOfLE_succ _ stage
  rw [written]
  exact factorial_stage_transition_surjective (source.X degree) stage

/-- The strict factorial limit maps into the actual generated homotopy limit. -/
def factorialDerivedLimitMap : (coneAt).pt ⟶ (factorialDerivedLimitFace root source).homotopyLimit :=
  liftShortComplex (limitDifferenceSequence (factorialDerivedLimitFace root source) coneAt)

theorem factorial_derived_limit_quasiIso : QuasiIso (factorialDerivedLimitMap root source) :=
  quasiIso_liftShortComplex _ (limit_difference_short_exact (factorialDerivedLimitFace root source) coneAt
    (factorialCochainIsLimit shape source) (factorial_transition_degree_onto root source))

theorem factorial_derived_limit_stage (stage : Nat) :
    factorialDerivedLimitMap root source ≫ (factorialDerivedLimitFace root source).restriction stage =
      (coneAt).π.app (Opposite.op stage) := by
  let face := factorialDerivedLimitFace root source
  let sequence := limitDifferenceSequence face coneAt
  exact (Category.assoc (factorialDerivedLimitMap root source)
    (CochainComplex.mappingCocone.fst face.difference) (face.productProjection stage)).symm.trans
    ((congrArg (fun read => read ≫ face.productProjection stage) (liftShortComplex_fst sequence)).trans
      (limit_product_projection face coneAt stage))

variable {source} {NextRoot : Type v} (next : RootedAccountedUnfolding NextRoot)
variable {target : CochainComplex AddCommGrpCat ℤ}

local notation "prior" => factorialDerivedLimitFace root source
local notation "later" => factorialDerivedLimitFace next target

def factorialDerivedAction (action : source ⟶ target) : (prior).homotopyLimit ⟶ (later).homotopyLimit :=
  homotopyLimitMap prior later (factorialCochainTowerMap shape action)

/-- The actual action commutes with the comparison on the entire factorial cocone. -/
theorem factorial_derived_limit_naturality (action : source ⟶ target) :
    factorialDerivedLimitMap root source ≫ factorialDerivedAction root next action =
      (factorialCompletionFunctor.mapHomologicalComplex shape).map action ≫ factorialDerivedLimitMap next target := by
  let oldCone := factorialCochainCone shape source
  let nextCone := factorialCochainCone shape target
  let written := factorialCochainTowerMap shape action
  let products := productMap prior later written
  let completed := (factorialCompletionFunctor.mapHomologicalComplex shape).map action
  have kernelSquare := limit_product_naturality prior later oldCone nextCone written completed
    (factorial_cochain_map_restriction shape action)
  exact lift_short_complex_naturality (limitDifferenceSequence prior oldCone)
    (limitDifferenceSequence later nextCone) completed products products kernelSquare
    (SequentialHomotopyLimitNaturality.differenceSquare prior later written)

theorem factorial_derived_action_quasiIso (action : HomotopyEquiv source target) :
    QuasiIso (factorialDerivedAction root next action.hom) := by
  let first := factorialDerivedLimitMap root source
  let last := factorialDerivedLimitMap next target
  let moved := factorialDerivedAction root next action.hom
  let completed := factorialCompletionFunctor.mapHomotopyEquiv action
  have compared : first ≫ moved = completed.hom ≫ last :=
    factorial_derived_limit_naturality root next action.hom
  have firstIso := factorial_derived_limit_quasiIso root source
  have lastIso := factorial_derived_limit_quasiIso next target
  have crossed := quasiIso_comp completed.hom last (hφ := completed.quasiIso_hom) (hφ' := lastIso)
  exact quasiIso_of_comp_left first moved (hφ := firstIso)
    (hφφ' := (congrArg (fun map => QuasiIso map) compared).mpr crossed)

end CofinalAllPrimeTopology
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
