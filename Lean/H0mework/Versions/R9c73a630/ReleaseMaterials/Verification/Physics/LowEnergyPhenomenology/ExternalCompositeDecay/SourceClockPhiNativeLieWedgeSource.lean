import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiRemainingClockPayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentGeometricPayer
open GaussNativePotential SourceQuantumScalarChart SourceQuantumGaugeCenterMagnetic SourceCartanCubic
open SaturationMonoid.PhysicsCore.StageNineP286BracketCalculus
open scoped InnerProductSpace
private local instance nativeEndNorm : NormedAddCommGroup (NativeLie →L[ℝ] NativeLie) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance nativeEndSpace : NormedSpace ℝ (NativeLie →L[ℝ] NativeLie) :=
  ContinuousLinearMap.toNormedSpace
private def bracketLinear : NativeLie →ₗ[ℝ] (NativeLie →L[ℝ] NativeLie) where
  toFun a := (nativeBracket a).toContinuousLinearMap
  map_add' a b := by
    apply ContinuousLinearMap.ext
    intro q
    exact LinearMap.congr_fun (map_add nativeBracket a b) q
  map_smul' r a := by
    apply ContinuousLinearMap.ext
    intro q
    exact LinearMap.congr_fun (map_smul nativeBracket r a) q
private abbrev B : NativeLie →L[ℝ] (NativeLie →L[ℝ] NativeLie) := bracketLinear.toContinuousLinearMap
/-- This fixed coefficient belongs to the original finite native Lie action. -/
def nativeLiePrice : ℝ := ‖B‖^2
private theorem bracket_self(a:NativeLie):nativeBracket a a=0:=by
  have h:=coordinateBracket_skew a a
  change nativeBracket a a= -nativeBracket a a at h
  have hz:(2:ℝ) • nativeBracket a a=0:=by linear_combination (norm:=module) h
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
private theorem perpendicular_square(a b:NativeLie)(ha:a≠0):
    ‖a‖^2*‖b-(inner ℝ a b/‖a‖^2) • a‖^2=
      ‖a‖^2*‖b‖^2-(inner ℝ a b)^2:=by
  rw [norm_sub_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,real_inner_smul_right,
    real_inner_comm b a]
  have hn:‖a‖≠0:=norm_ne_zero_iff.mpr ha
  field_simp [hn]
  ring

/-- Antisymmetry removes the parallel leg before the actual native bracket is estimated. -/
theorem actual_native_lie_wedge_bound(a b:NativeLie):
    ‖nativeBracket a b‖^2 ≤ nativeLiePrice*(‖a‖^2*‖b‖^2-(inner ℝ a b)^2):=by
  by_cases ha:a=0
  · subst a
    simp [nativeBracket]
  let q:=b-(inner ℝ a b/‖a‖^2) • a
  have hq:nativeBracket a q=nativeBracket a b:=by
    simp only[q,map_sub,map_smul,bracket_self,smul_zero,sub_zero]
  have h:=B.le_opNorm₂ a q
  change ‖nativeBracket a q‖ ≤ ‖B‖*‖a‖*‖q‖ at h
  rw [hq] at h
  have h2:=pow_le_pow_left₀ (norm_nonneg _) h 2
  have hp:=perpendicular_square a b ha
  change ‖a‖^2*‖q‖^2=‖a‖^2*‖b‖^2-(inner ℝ a b)^2 at hp
  calc
    _ ≤ nativeLiePrice*(‖a‖^2*‖q‖^2):=by simpa only[nativeLiePrice,mul_pow,mul_assoc] using h2
    _=nativeLiePrice*(‖a‖^2*‖b‖^2-(inner ℝ a b)^2):=by rw [hp]

def nativeRowWedge(A:Fin 3→NativeLie):ℝ:=
  (∑i:Fin 3,inner ℝ (A i) (A i))^2-∑i:Fin 3,∑j:Fin 3,(inner ℝ (A i) (A j))^2
private theorem row_wedge(A:Fin 3→NativeLie):nativeRowWedge A=
    2*((‖A 0‖^2*‖A 1‖^2-(inner ℝ (A 0) (A 1))^2)+
      (‖A 1‖^2*‖A 2‖^2-(inner ℝ (A 1) (A 2))^2)+
      (‖A 2‖^2*‖A 0‖^2-(inner ℝ (A 2) (A 0))^2)):=by
  simp only[nativeRowWedge,Fin.sum_univ_three,real_inner_self_eq_norm_sq]
  rw [real_inner_comm (A 1) (A 0),real_inner_comm (A 0) (A 2),real_inner_comm (A 2) (A 1)]
  ring

/-- The original three magnetic brackets are paid by their full source Gram wedge, including zero columns. -/
theorem actual_native_magnetic_wedge_source(A:Fin 3→NativeLie):
    (∑i:Fin 3,‖magneticOfConnection A i‖^2) ≤ (nativeLiePrice/2)*nativeRowWedge A:=by
  have h01:=actual_native_lie_wedge_bound (A 0) (A 1)
  have h12:=actual_native_lie_wedge_bound (A 1) (A 2)
  have h20:=actual_native_lie_wedge_bound (A 2) (A 0)
  rw [row_wedge]
  simp only [Fin.sum_univ_three,magneticOfConnection,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  change ‖nativeBracket (A 1) (A 2)‖^2+‖nativeBracket (A 2) (A 0)‖^2+
    ‖nativeBracket (A 0) (A 1)‖^2 ≤ _
  nlinarith only[h01,h12,h20]
end LowEnergy.FirstCurrentGeometricPayer
