import H0mework.Realization.Topology.CompressedUnitaryDefectPort
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedCompressedUnitaryDefectPort.Feedback

open scoped InnerProductSpace

section Resolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def geometric (A : E →L[ℂ] E) (z : ℂ) : E →L[ℂ] E := ∑' n : Nat, (z • A)^n

omit [CompleteSpace E] in
private theorem contraction (A : E →L[ℂ] E) (bounded : ‖A‖ ≤ 1) {z : ℂ} (disk : ‖z‖ < 1) :
    ‖z • A‖ < 1 := by
  rw [norm_smul]
  exact (mul_le_of_le_one_right (norm_nonneg z) bounded).trans_lt disk

theorem geometric_solve (A : E →L[ℂ] E) (bounded : ‖A‖ ≤ 1)
    {z : ℂ} (disk : ‖z‖ < 1) (source : E) :
    geometric A z source - z • A (geometric A z source) = source := by
  have solved := congrArg (fun M : E →L[ℂ] E => M source)
    (mul_neg_geom_series (z • A) (contraction A bounded disk))
  exact solved

theorem eq_geometric_of_solve (A : E →L[ℂ] E) (bounded : ‖A‖ ≤ 1)
    {z : ℂ} (disk : ‖z‖ < 1) {source solution : E}
    (solves : solution - z • A solution = source) : solution = geometric A z source := by
  have inverse := congrArg (fun M : E →L[ℂ] E => M solution)
    (geom_series_mul_neg (z • A) (contraction A bounded disk))
  change geometric A z (solution - z • A solution) = solution at inverse
  rw [solves] at inverse
  exact inverse.symm

end Resolvent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (face : ClosedSubmodule ℂ E) (action : E →ₗᵢ[ℂ] E)

local instance : CompleteSpace face.toSubmodule := face.isClosed.isComplete.completeSpace_coe

local notation "K" => ClosedSubmodule.toSubmodule face
local notation "P" => Submodule.starProjection K
local notation "Q" => Submodule.starProjection (Submodule.orthogonal K)
local notation "S" => LinearIsometry.toContinuousLinearMap action

omit [CompleteSpace E] in
theorem action_bound : ‖S‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    change ‖action x‖ ≤ 1*‖x‖
    rw [action.norm_map, one_mul])

/-- The complete hidden update is the original action followed by its orthogonal residual. -/
def hidden : E →L[ℂ] E := ContinuousLinearMap.comp Q S

local notation "H" => hidden face action

theorem hidden_bound : ‖H‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    change ‖Q (action x)‖ ≤ 1*‖x‖
    rw [one_mul, ← action.norm_map x]
    exact Submodule.norm_starProjection_apply_le _ _)

private theorem hidden_mem (x : E) : H x ∈ Kᗮ := Submodule.starProjection_apply_mem _ _

private theorem geometric_hidden_mem {z : ℂ} (disk : ‖z‖ < 1) {source : E} (inHidden : source ∈ Kᗮ) :
    geometric H z source ∈ Kᗮ := by
  let moved := geometric H z source
  have update : moved = source + z • H moved :=
    sub_eq_iff_eq_add.mp (geometric_solve H (hidden_bound face action) disk source)
  change moved ∈ Kᗮ
  rw [update]
  exact (Kᗮ).add_mem inHidden ((Kᗮ).smul_mem z (hidden_mem face action moved))

def returnStock (z : ℂ) (x : K) : E := geometric H z (H (x : E))

/-- Both oriented channels of the same isometry generate the observed transfer. -/
def transfer (z : ℂ) : K →L[ℂ] K :=
  compression face action + z • ((K).orthogonalProjectionOnto.comp
    (ContinuousLinearMap.comp S ((geometric H z).comp (ContinuousLinearMap.comp H (K).subtypeL))))

theorem feedback_output {z : ℂ} (disk : ‖z‖ < 1) (x : K) :
    ((transfer face action z x : K) : E) + returnStock face action z x =
      action ((x : E) + z • returnStock face action z x) := by
  let stock := returnStock face action z x
  let output := action ((x : E) + z • stock)
  have inPort : P output = (transfer face action z x : E) := by
    change P (action ((x : E) + z • stock)) = _
    rw [map_add, map_smul, map_add, map_smul]
    rfl
  have outPort : Q output = stock := by
    change H ((x : E) + z • stock) = stock
    rw [map_add, map_smul]
    exact (sub_eq_iff_eq_add.mp
      (geometric_solve H (hidden_bound face action) disk (H (x : E)))).symm
  calc
    _ = P output + Q output := congrArg₂ (· + ·) inPort.symm outPort.symm
    _ = output := Submodule.starProjection_add_starProjection_orthogonal _
    _ = _ := rfl

/-- The contraction has the exact energy cost of the original hidden return. -/
theorem transfer_energy {z : ℂ} (disk : ‖z‖ < 1) (x : K) :
    ‖transfer face action z x‖^2 +
      (1-‖z‖^2)*‖returnStock face action z x‖^2 = ‖x‖^2 := by
  let stock := returnStock face action z x
  let visible := transfer face action z x
  have outside : stock ∈ Kᗮ := geometric_hidden_mem face action disk (hidden_mem face action _)
  have inputOrth : inner ℂ (x : E) (z • stock) = 0 :=
    ((Kᗮ).smul_mem z outside) _ x.property
  have outputOrth : inner ℂ (visible : E) stock = 0 := outside _ visible.property
  have equal : ‖(visible : E) + stock‖^2 = ‖(x : E) + z • stock‖^2 := by
    change ‖(transfer face action z x : E) + returnStock face action z x‖^2 = _
    rw [feedback_output face action disk, action.norm_map]
  have outputSquares : ‖(visible : E) + stock‖^2 = ‖(visible : E)‖^2 + ‖stock‖^2 := by
    simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ outputOrth
  have inputSquares : ‖(x : E) + z • stock‖^2 = ‖(x : E)‖^2 + ‖z • stock‖^2 := by
    simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ inputOrth
  rw [outputSquares, inputSquares, norm_smul, mul_pow] at equal
  change ‖visible‖^2 + ‖stock‖^2 = ‖x‖^2 + ‖z‖^2*‖stock‖^2 at equal
  linarith only [equal]

theorem transfer_bound {z : ℂ} (disk : ‖z‖ < 1) :
    ‖transfer face action z‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have loss : 0 ≤ (1-‖z‖^2)*‖returnStock face action z x‖^2 :=
    mul_nonneg (sub_nonneg.mpr (pow_le_one₀ (norm_nonneg _) disk.le)) (sq_nonneg _)
  linarith only [transfer_energy face action disk x, loss]

/-- The initial hidden field is advanced as its own forcing term. -/
def external (z : ℂ) (source : E) : E := geometric H z (Q source)

def visible (z : ℂ) (source : E) : K :=
  geometric (transfer face action z) z
    ((K).orthogonalProjectionOnto source +
      z • (K).orthogonalProjectionOnto (action (external face action z source)))

def field (z : ℂ) (source : E) : E :=
  (visible face action z source : E) + external face action z source +
    z • returnStock face action z (visible face action z source)

theorem field_source {z : ℂ} (disk : ‖z‖ < 1) (source : E) :
    field face action z source = geometric S z source := by
  let p := visible face action z source
  let a := external face action z source
  let b := returnStock face action z p
  let y := transfer face action z p
  have read : p - z • y = (K).orthogonalProjectionOnto source +
      z • (K).orthogonalProjectionOnto (action a) :=
    geometric_solve (transfer face action z) (transfer_bound face action disk) disk _
  have readValue : (p : E) - z • (y : E) = P source + z • P (action a) :=
    congrArg Subtype.val read
  have hiddenRead : a - z • Q (action a) = Q source :=
    geometric_solve H (hidden_bound face action) disk _
  have out : action ((p : E) + a + z • b) = (y : E) + b + action a := by
    have move : (p : E) + a + z • b = ((p : E) + z • b) + a := by module
    rw [move, map_add, ← feedback_output face action disk p]
  apply eq_geometric_of_solve S (action_bound action) disk
  change (p : E) + a + z • b - z • action ((p : E) + a + z • b) = source
  rw [out]
  calc
    _ = ((p : E) - z • (y : E)) + (a - z • action a) := by module
    _ = P source + (a - z • Q (action a)) := by
      have cut : P (action a) + Q (action a) = action a :=
        Submodule.starProjection_add_starProjection_orthogonal _
      have scaled : z • action a = z • P (action a) + z • Q (action a) :=
        (congrArg (fun value : E => z • value) cut.symm).trans (smul_add _ _ _)
      rw [readValue, scaled]
      module
    _ = P source + Q source := congrArg (P source + ·) hiddenRead
    _ = source := Submodule.starProjection_add_starProjection_orthogonal source

theorem field_visible {z : ℂ} (disk : ‖z‖ < 1) (source : E) :
    P (field face action z source) = (visible face action z source : E) := by
  have outer : external face action z source ∈ Kᗮ :=
    geometric_hidden_mem face action disk (Submodule.starProjection_apply_mem _ _)
  have returned : returnStock face action z (visible face action z source) ∈ Kᗮ :=
    geometric_hidden_mem face action disk (hidden_mem face action _)
  have zero (value : E) (mem : value ∈ Kᗮ) : P value = 0 := by
    rw [Submodule.starProjection_apply, Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal mem]
    rfl
  simp only [field, map_add, map_smul, zero _ outer, zero _ returned, smul_zero, add_zero]
  exact Submodule.starProjection_eq_self_iff.mpr (visible face action z source).property

end SourceGeneratedCompressedUnitaryDefectPort.Feedback
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
