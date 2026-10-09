import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateVertexEntries

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
namespace LowEnergy.ActualCandidateVertexValues
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ActualCandidateVertexEntries MixedSpectatorCandidate
open MixedSpectatorContactVertices DiracCliffordRepresentation
open SU7MotherLieAlgebra SU7ExteriorMatterRestriction Stage9C.Material.SpinPair
open Stage9C.Dynamics.Homogeneous PointwiseDiracSpinConnectionLift
open scoped Matrix BigOperators
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

theorem lapse_value : (lapse : ℂ) = (3/25 : ℂ) * (Real.sqrt 30 : ℂ) := by
  have h : lapse = (3/25 : ℝ) * Real.sqrt 30 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 30 by norm_num)
    have hn := Real.sqrt_nonneg (30 : ℝ)
    nlinarith [lapse_sq,lapse_pos]
  rw [h]
  push_cast
  ring

theorem primitive_gauge (a : Fin 97) (h9 : ¬a.val < 9) (h57 : a.val < 57)
    (i j : Support) :
    primitiveEntry 0 false a i j =
      (lapse : ℂ) * (if (⟨(a.val-9)/12,by omega⟩ : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
      (diracGammaZero * diracGamma ⟨(a.val-9)/12,by omega⟩) i.1 j.1 *
      gaugeEntry (nativeMother ⟨(a.val-9)%12,Nat.mod_lt _ (by decide)⟩)
        i.2 (supportNamed i).2.2 j.2 (supportNamed j).2.2 := by
  simp only [primitiveEntry, Bool.false_eq_true, ite_false, rawEntry,dif_neg h9,dif_pos h57,
    internalEntry, mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [Matrix.mul_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  dsimp only [supportNamed]
  split_ifs <;> ring

theorem p286_entry (D : P286LieBlockData) (c d : Fin 3) (h k : Fin 2) :
    gaugeEntry (p286LieBlockEmbed D) c h d k =
    (if h = k then D.1.val c d else 0) +
    (if c = d then
      (if h = 0 then (if k = 0 then D.2.2.val else 0)
       else (if k = 1 then D.2.1.val 0 0 else 0)) else 0) := by
  fin_cases h <;> fin_cases k <;> rfl

theorem native_color (a : Fin 12) :
    (nativeData a).1.val = if h : a.val < 8 then colorRaw ⟨a.val,h⟩ else 0 := by
  unfold nativeData
  split_ifs <;> rfl

theorem native_weak (a : Fin 12) :
    (nativeData a).2.1.val = if h : 8 ≤ a.val ∧ a.val < 11 then weakRaw ⟨a.val-8,by omega⟩ else 0 := by
  unfold nativeData
  split_ifs <;> try omega
  all_goals rfl

theorem native_hyper (a : Fin 12) :
    (nativeData a).2.2.val = if a.val = 11 then Complex.I else 0 := by
  unfold nativeData
  split_ifs <;> try omega
  all_goals rfl

theorem lapse_scale (mu : Fin 4) :
    (lapse : ℂ) * (if mu = 0 then Complex.I / (lapse : ℂ) else Complex.I) =
      if mu = 0 then Complex.I else ((3/25 : ℂ) * (Real.sqrt 30 : ℂ)) * Complex.I := by
  have ln : (lapse : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt lapse_pos
  split_ifs
  · field_simp
  · rw [lapse_value]


def sourceColorTable (a : Fin 8) : Matrix (Fin 3) (Fin 3) ℂ :=
  match a.val with
  | 0 => !![0,1,0; -1,0,0; 0,0,0]
  | 1 => !![0,Complex.I,0; Complex.I,0,0; 0,0,0]
  | 2 => !![0,0,1; 0,0,0; -1,0,0]
  | 3 => !![0,0,Complex.I; 0,0,0; Complex.I,0,0]
  | 4 => !![0,0,0; 0,0,1; 0,-1,0]
  | 5 => !![0,0,0; 0,0,Complex.I; 0,Complex.I,0]
  | 6 => !![Complex.I,0,0; 0,0,0; 0,0,-Complex.I]
  | 7 => !![0,0,0; 0,Complex.I,0; 0,0,-Complex.I]
  | _ => 0

theorem sourceColorTable_original (a : Fin 8) : colorRaw a = sourceColorTable a := by
  fin_cases a <;> rfl

end LowEnergy.ActualCandidateVertexValues
