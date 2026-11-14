import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedFiniteFlow
import H0mework.Versions.Rdf421ff6.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Words.Programme

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedProgramTrace

open BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open scoped BigOperators

namespace Programme
export SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceWordOrbit.NativeWordProgramme
  (Value Var environment programme programme_value programme_budget)
end Programme

open private phase scaleMass orbit meshTail_apply from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedMassMesh
open private scale from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedWord
open private tail from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedFiniteFlow

local notation "End" => (BurnolL2 →L[ℂ] BurnolL2)
local notation "U" => burnolMultiplicativeDilation
local notation "Index" => BoundaryCountedContinuousInverse.index
local notation "word" => BoundaryCountedFiniteFlow.word

abbrev Stock := BurnolL2 × (BurnolL2 × BurnolL2)
abbrev Letter (mesh : Nat) := Fin mesh ⊕ PUnit.{1}

private def seed : BurnolL2 →ₗ[ℤ] Stock :=
  LinearMap.id.prod 0

private abbrev input : Stock →ₗ[ℤ] BurnolL2 :=
  LinearMap.fst ℤ BurnolL2 (BurnolL2 × BurnolL2)

private abbrev iterate : Stock →ₗ[ℤ] BurnolL2 :=
  (LinearMap.fst ℤ BurnolL2 BurnolL2).comp (LinearMap.snd ℤ BurnolL2 (BurnolL2 × BurnolL2))

private abbrev accumulated : Stock →ₗ[ℤ] BurnolL2 :=
  (LinearMap.snd ℤ BurnolL2 BurnolL2).comp (LinearMap.snd ℤ BurnolL2 (BurnolL2 × BurnolL2))

private def sample (N mesh j : Nat) : End :=
  (N : ℝ) • scaleMass N • (mesh : ℝ)⁻¹ •
    (U (-phase N (SourceGeneratedUnitMesh.node mesh (j+1)))).toContinuousLinearEquiv.toContinuousLinearMap

/-- Each letter either accumulates one original weighted dilation or closes that same finite cell. -/
def action (coordinate : ℂ) (n mesh : Nat) : Letter mesh → Stock →ₗ[ℤ] Stock
  | .inl j =>
      input.prod (iterate.prod (accumulated + ((sample (Index coordinate n) mesh j).toLinearMap.restrictScalars ℤ).comp iterate))
  | .inr _ =>
      let damp : BurnolL2 →ₗ[ℤ] BurnolL2 :=
        (((scale coordinate n)⁻¹ • (1 : End)).toLinearMap.restrictScalars ℤ)
      input.prod ((damp.comp (input + accumulated)).prod 0)

private theorem sample_action (coordinate : ℂ) (n mesh : Nat) (j : Fin mesh) (b x y : BurnolL2) :
    action coordinate n mesh (.inl j) (b,x,y) = (b,x,y + sample (Index coordinate n) mesh j x) := rfl

private theorem close_action (coordinate : ℂ) (n mesh : Nat) (b x y : BurnolL2) :
    action coordinate n mesh (.inr PUnit.unit) (b,x,y) =
      (b,(scale coordinate n)⁻¹ • (b+y),0) := rfl

private def samples (mesh : Nat) : List (Fin mesh) := List.ofFn id

private def round (mesh : Nat) : List (Letter mesh) :=
  (samples mesh).map Sum.inl ++ [.inr PUnit.unit]

def letters (mesh length : Nat) : List (Letter mesh) :=
  (List.replicate length (round mesh)).flatten

private theorem letters_succ (mesh length : Nat) : letters mesh (length+1) = letters mesh length ++ round mesh := by
  simp only [letters, List.replicate_succ', List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil]

theorem letters_length (mesh length : Nat) : (letters mesh length).length = length*(mesh+1) := by
  induction length with
  | zero => simp [letters]
  | succ length previous =>
    rw [letters_succ, List.length_append, previous]
    simp only [round, samples, List.length_append, List.length_map, List.length_ofFn, List.length_singleton,
      Nat.succ_mul]

private theorem run_samples (coordinate : ℂ) (n mesh : Nat) (indices : List (Fin mesh)) (b x y : BurnolL2) :
    SourceGeneratedActionWords.run (action coordinate n mesh) (indices.map Sum.inl) (b,x,y) =
      (b,x,y + (indices.map (fun j : Fin mesh => sample (Index coordinate n) mesh j.val x)).sum) := by
  induction indices generalizing y with
  | nil => simp [SourceGeneratedActionWords.run]
  | cons j rest previous =>
    rw [List.map_cons, SourceGeneratedActionWords.run, Module.End.mul_apply, sample_action, previous]
    simp only [List.map_cons, List.sum_cons, add_assoc]

private theorem sum_samples (N mesh : Nat) (x : BurnolL2) :
    ((samples mesh).map (fun j : Fin mesh => sample N mesh j.val x)).sum = BoundaryCountedMassMesh.meshTail N mesh x := by
  rw [samples, List.map_ofFn, List.sum_ofFn, meshTail_apply, SourceGeneratedUnitMesh.average]
  simp only [Function.comp_apply, id_eq]
  rw [Fin.sum_univ_eq_sum_range (fun j => sample N mesh j x)]
  simp only [Finset.smul_sum, sample, smul_apply, orbit,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe]

private theorem run_round (coordinate : ℂ) (n mesh : Nat) (b x : BurnolL2) :
    SourceGeneratedActionWords.run (action coordinate n mesh) (round mesh) (b,x,0) =
      (b,(scale coordinate n)⁻¹ • (b+tail coordinate n mesh x),0) := by
  rw [round, SourceGeneratedActionWords.run_append, Module.End.mul_apply, run_samples, zero_add, sum_samples]
  change action coordinate n mesh (.inr PUnit.unit) (b,x,tail coordinate n mesh x) = _
  exact close_action coordinate n mesh b x _

private theorem word_succ (coordinate : ℂ) (n mesh length : Nat) (b : BurnolL2) :
    word coordinate n mesh (length+1) b =
      (scale coordinate n)⁻¹ • (b + tail coordinate n mesh (word coordinate n mesh length b)) := by
  let β := scale coordinate n
  let d := tail coordinate n mesh
  let q := SourceGeneratedFiniteInverseWord.relative β d
  let s : End := ∑ j ∈ Finset.range length, q^j
  change (β⁻¹ • ∑ j ∈ Finset.range (length+1), q^j : End) b =
    β⁻¹ • (b+d ((β⁻¹ • s : End) b))
  rw [geom_sum_succ, smul_add]
  change β⁻¹ • q (s b) + β⁻¹ • b = β⁻¹ • (b+d (β⁻¹ • s b))
  rw [map_smul, smul_add]
  exact add_comm _ _

theorem run_word (coordinate : ℂ) (n mesh length : Nat) (b : BurnolL2) :
    SourceGeneratedActionWords.run (action coordinate n mesh) (letters mesh length) (seed b) =
      (b,word coordinate n mesh length b,0) := by
  induction length with
  | zero =>
    change (b,0,0) = _
    simp only [BoundaryCountedFiniteFlow.word, SourceGeneratedFiniteInverseWord.word, Finset.range_zero,
      Finset.sum_empty, smul_zero, zero_apply]
  | succ length previous =>
    rw [letters_succ, SourceGeneratedActionWords.run_append, Module.End.mul_apply, previous, run_round, word_succ]

abbrev Value := Programme.Value (I:=BurnolL2) (O:=Stock)
abbrev Var := Programme.Var
abbrev Slot := SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceOrbit.NativeOrbitProgramme.Slot
namespace Slot
export SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceOrbit.NativeOrbitProgramme.Slot (orbit)
end Slot

def environment (b : BurnolL2) : Env Value Var := Programme.environment seed.toAddMonoidHom b

def expression (coordinate : ℂ) (n mesh length : Nat) : Expr Value Var Slot.orbit :=
  Programme.programme seed (action coordinate n mesh) (letters mesh length)

theorem expression_eval (coordinate : ℂ) (n mesh length : Nat) (b : BurnolL2) :
    (expression coordinate n mesh length).eval (environment b) = (b,word coordinate n mesh length b,0) :=
  (Programme.programme_value seed (action coordinate n mesh) (letters mesh length) b).trans
    (run_word coordinate n mesh length b)

theorem expression_budget (coordinate : ℂ) (n mesh length : Nat) :
    remaining (expression coordinate n mesh length) = length*(mesh+1)+2 := by
  rw [expression, Programme.programme_budget, letters_length]

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedProgramTrace
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
