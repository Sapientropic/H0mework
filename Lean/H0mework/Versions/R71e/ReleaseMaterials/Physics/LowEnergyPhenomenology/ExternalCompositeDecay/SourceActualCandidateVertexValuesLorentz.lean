import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateVertexValueKernel
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateVertexLiterals

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unreachableTactic false
set_option linter.unreachableTactic false
noncomputable section
namespace LowEnergy.ActualCandidateVertexValues
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ActualCandidateVertexEntries ActualCandidateVertexLiterals MixedSpectatorCandidate
open MixedSpectatorContactVertices DiracCliffordRepresentation
open SU7MotherLieAlgebra SU7ExteriorMatterRestriction Stage9C.Material.SpinPair
open Stage9C.Dynamics.Homogeneous PointwiseDiracSpinConnectionLift
open scoped Matrix BigOperators
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

theorem spin_entry_factor (S : DiracMatrix) (i j : NamedMode) :
    spinEntry S i j = S i.1 j.1 * (if i.2 = j.2 then 1 else 0) := by
  rcases i with ⟨s,c,h⟩
  rcases j with ⟨t,d,k⟩
  by_cases h : (c,h) = (d,k)
  · simp [ActualCandidateVertexEntries.spinEntry,basisEntry,h]
  · simp [ActualCandidateVertexEntries.spinEntry,basisEntry,h]

theorem primitive_lorentz (a : Fin 97) (h73 : 73 ≤ a.val) (i j : Support) :
    primitiveEntry 0 false a i j =
      (lapse : ℂ) * (if (⟨(a.val-73)/6,by omega⟩ : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
      (diracGammaZero * diracGamma ⟨(a.val-73)/6,by omega⟩ *
        lorentzMatrix ⟨(a.val-73)%6,Nat.mod_lt _ (by decide)⟩) i.1 j.1 *
      (if (supportNamed i).2 = (supportNamed j).2 then 1 else 0) := by
  have h9 : ¬a.val < 9 := by omega
  have h57 : ¬a.val < 57 := by omega
  have h73' : ¬a.val < 73 := by omega
  simp only [primitiveEntry, Bool.false_eq_true, ite_false, rawEntry,
    dif_neg h9,dif_neg h57,dif_neg h73',spin_entry_factor]
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro u _
  dsimp only [supportNamed]
  split_ifs <;> ring

private theorem support_explicit (i : Support) :
    supportNamed i = (i.1,i.2,(![0,0,1,1] : Fin 4 → Fin 2) i.1) := by
  rcases i with ⟨s,c⟩
  fin_cases s <;> rfl

private def lorentzTable (a : Fin 6) : DiracMatrix :=
  match a.val with
  | 0 => (1/2 : ℂ) • (diracGamma 0 * diracGamma 1)
  | 1 => (1/2 : ℂ) • (diracGamma 0 * diracGamma 2)
  | 2 => (1/2 : ℂ) • (diracGamma 0 * diracGamma 3)
  | 3 => (1/2 : ℂ) • (diracGamma 2 * diracGamma 3)
  | 4 => (1/2 : ℂ) • (diracGamma 3 * diracGamma 1)
  | 5 => (1/2 : ℂ) • (diracGamma 1 * diracGamma 2)
  | _ => 0

private theorem lorentzTable_original (a : Fin 6) : lorentzMatrix a = lorentzTable a := by
  fin_cases a <;> rfl

private def row_73 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 53
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 53
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 53
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 53
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 53
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 53
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 54
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 54
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 54
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 54
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 54
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 54
  else 0

private theorem row_73_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 73 s t c d = row_73 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_73 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 73 (s,c) (t,d) = primalLiteral 73 s t c d := by
  rw [primitive_lorentz 73 (by decide)]
  change (lapse : ℂ) * (if (0 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 0 * lorentzMatrix 0) s t *
    (if (supportNamed (s,c)).2 = (supportNamed (t,d)).2 then 1 else 0) = _
  rw [lapse_scale,row_73_original]
  simp only [support_explicit,lorentzTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_73,lorentzTable,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_74 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 55
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 55
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 55
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 56
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 56
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 56
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 56
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 56
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 56
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 55
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 55
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 55
  else 0

private theorem row_74_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 74 s t c d = row_74 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_74 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 74 (s,c) (t,d) = primalLiteral 74 s t c d := by
  rw [primitive_lorentz 74 (by decide)]
  change (lapse : ℂ) * (if (0 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 0 * lorentzMatrix 1) s t *
    (if (supportNamed (s,c)).2 = (supportNamed (t,d)).2 then 1 else 0) = _
  rw [lapse_scale,row_74_original]
  simp only [support_explicit,lorentzTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_74,lorentzTable,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_75 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 53
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 53
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 53
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 54
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 54
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 54
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 54
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 54
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 54
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 53
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 53
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 53
  else 0

private theorem row_75_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 75 s t c d = row_75 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_75 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 75 (s,c) (t,d) = primalLiteral 75 s t c d := by
  rw [primitive_lorentz 75 (by decide)]
  change (lapse : ℂ) * (if (0 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 0 * lorentzMatrix 2) s t *
    (if (supportNamed (s,c)).2 = (supportNamed (t,d)).2 then 1 else 0) = _
  rw [lapse_scale,row_75_original]
  simp only [support_explicit,lorentzTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_75,lorentzTable,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_76 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 56
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 56
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 56
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 56
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 56
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 56
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 56
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 56
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 56
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 56
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 56
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 56
  else 0

private theorem row_76_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 76 s t c d = row_76 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_76 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 76 (s,c) (t,d) = primalLiteral 76 s t c d := by
  rw [primitive_lorentz 76 (by decide)]
  change (lapse : ℂ) * (if (0 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 0 * lorentzMatrix 3) s t *
    (if (supportNamed (s,c)).2 = (supportNamed (t,d)).2 then 1 else 0) = _
  rw [lapse_scale,row_76_original]
  simp only [support_explicit,lorentzTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_76,lorentzTable,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_77 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 53
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 53
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 53
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 54
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 54
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 54
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 53
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 53
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 53
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 54
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 54
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 54
  else 0

private theorem row_77_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 77 s t c d = row_77 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_77 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 77 (s,c) (t,d) = primalLiteral 77 s t c d := by
  rw [primitive_lorentz 77 (by decide)]
  change (lapse : ℂ) * (if (0 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 0 * lorentzMatrix 4) s t *
    (if (supportNamed (s,c)).2 = (supportNamed (t,d)).2 then 1 else 0) = _
  rw [lapse_scale,row_77_original]
  simp only [support_explicit,lorentzTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_77,lorentzTable,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_78 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 56
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 56
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 56
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 55
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 55
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 55
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 56
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 56
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 56
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 55
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 55
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 55
  else 0

private theorem row_78_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 78 s t c d = row_78 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_78 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 78 (s,c) (t,d) = primalLiteral 78 s t c d := by
  rw [primitive_lorentz 78 (by decide)]
  change (lapse : ℂ) * (if (0 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 0 * lorentzMatrix 5) s t *
    (if (supportNamed (s,c)).2 = (supportNamed (t,d)).2 then 1 else 0) = _
  rw [lapse_scale,row_78_original]
  simp only [support_explicit,lorentzTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_78,lorentzTable,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_79 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 57
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 57
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 57
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 57
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 57
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 57
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 57
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 57
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 57
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 57
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 57
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 57
  else 0

private theorem row_79_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 79 s t c d = row_79 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_79 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 79 (s,c) (t,d) = primalLiteral 79 s t c d := by
  rw [primitive_lorentz 79 (by decide)]
  change (lapse : ℂ) * (if (1 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 1 * lorentzMatrix 0) s t *
    (if (supportNamed (s,c)).2 = (supportNamed (t,d)).2 then 1 else 0) = _
  rw [lapse_scale,row_79_original]
  simp only [support_explicit,lorentzTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_79,lorentzTable,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_80 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 58
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 58
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 58
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 59
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 59
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 59
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 58
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 58
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 58
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 59
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 59
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 59
  else 0

private theorem row_80_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 80 s t c d = row_80 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_80 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 80 (s,c) (t,d) = primalLiteral 80 s t c d := by
  rw [primitive_lorentz 80 (by decide)]
  change (lapse : ℂ) * (if (1 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 1 * lorentzMatrix 1) s t *
    (if (supportNamed (s,c)).2 = (supportNamed (t,d)).2 then 1 else 0) = _
  rw [lapse_scale,row_80_original]
  simp only [support_explicit,lorentzTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_80,lorentzTable,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_81 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 60
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 60
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 60
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 57
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 57
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 57
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 60
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 60
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 60
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 57
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 57
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 57
  else 0

private theorem row_81_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 81 s t c d = row_81 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_81 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 81 (s,c) (t,d) = primalLiteral 81 s t c d := by
  rw [primitive_lorentz 81 (by decide)]
  change (lapse : ℂ) * (if (1 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 1 * lorentzMatrix 2) s t *
    (if (supportNamed (s,c)).2 = (supportNamed (t,d)).2 then 1 else 0) = _
  rw [lapse_scale,row_81_original]
  simp only [support_explicit,lorentzTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_81,lorentzTable,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_82 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 58
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 58
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 58
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 58
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 58
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 58
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 59
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 59
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 59
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 59
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 59
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 59
  else 0

private theorem row_82_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 82 s t c d = row_82 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_82 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 82 (s,c) (t,d) = primalLiteral 82 s t c d := by
  rw [primitive_lorentz 82 (by decide)]
  change (lapse : ℂ) * (if (1 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 1 * lorentzMatrix 3) s t *
    (if (supportNamed (s,c)).2 = (supportNamed (t,d)).2 then 1 else 0) = _
  rw [lapse_scale,row_82_original]
  simp only [support_explicit,lorentzTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_82,lorentzTable,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_83 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 60
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 60
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 60
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 57
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 57
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 57
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 57
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 57
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 57
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 60
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 60
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 60
  else 0

private theorem row_83_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 83 s t c d = row_83 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_83 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 83 (s,c) (t,d) = primalLiteral 83 s t c d := by
  rw [primitive_lorentz 83 (by decide)]
  change (lapse : ℂ) * (if (1 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 1 * lorentzMatrix 4) s t *
    (if (supportNamed (s,c)).2 = (supportNamed (t,d)).2 then 1 else 0) = _
  rw [lapse_scale,row_83_original]
  simp only [support_explicit,lorentzTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_83,lorentzTable,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_84 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 59
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 59
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 59
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 58
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 58
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 58
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 58
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 58
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 58
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 59
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 59
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 59
  else 0

private theorem row_84_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 84 s t c d = row_84 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_84 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 84 (s,c) (t,d) = primalLiteral 84 s t c d := by
  rw [primitive_lorentz 84 (by decide)]
  change (lapse : ℂ) * (if (1 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 1 * lorentzMatrix 5) s t *
    (if (supportNamed (s,c)).2 = (supportNamed (t,d)).2 then 1 else 0) = _
  rw [lapse_scale,row_84_original]
  simp only [support_explicit,lorentzTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_84,lorentzTable,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_85 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 59
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 59
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 59
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 58
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 58
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 58
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 59
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 59
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 59
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 58
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 58
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 58
  else 0

private theorem row_85_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 85 s t c d = row_85 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_85 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 85 (s,c) (t,d) = primalLiteral 85 s t c d := by
  rw [primitive_lorentz 85 (by decide)]
  change (lapse : ℂ) * (if (2 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 2 * lorentzMatrix 0) s t *
    (if (supportNamed (s,c)).2 = (supportNamed (t,d)).2 then 1 else 0) = _
  rw [lapse_scale,row_85_original]
  simp only [support_explicit,lorentzTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_85,lorentzTable,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_86 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 57
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 57
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 57
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 57
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 57
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 57
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 57
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 57
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 57
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 57
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 57
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 57
  else 0

private theorem row_86_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 86 s t c d = row_86 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_86 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 86 (s,c) (t,d) = primalLiteral 86 s t c d := by
  rw [primitive_lorentz 86 (by decide)]
  change (lapse : ℂ) * (if (2 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 2 * lorentzMatrix 1) s t *
    (if (supportNamed (s,c)).2 = (supportNamed (t,d)).2 then 1 else 0) = _
  rw [lapse_scale,row_86_original]
  simp only [support_explicit,lorentzTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_86,lorentzTable,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_87 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 58
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 58
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 58
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 58
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 58
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 58
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 58
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 58
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 58
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 58
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 58
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 58
  else 0

private theorem row_87_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 87 s t c d = row_87 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_87 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 87 (s,c) (t,d) = primalLiteral 87 s t c d := by
  rw [primitive_lorentz 87 (by decide)]
  change (lapse : ℂ) * (if (2 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 2 * lorentzMatrix 2) s t *
    (if (supportNamed (s,c)).2 = (supportNamed (t,d)).2 then 1 else 0) = _
  rw [lapse_scale,row_87_original]
  simp only [support_explicit,lorentzTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_87,lorentzTable,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_88 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 57
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 57
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 57
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 60
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 60
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 60
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 60
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 60
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 60
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 57
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 57
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 57
  else 0

private theorem row_88_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 88 s t c d = row_88 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_88 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 88 (s,c) (t,d) = primalLiteral 88 s t c d := by
  rw [primitive_lorentz 88 (by decide)]
  change (lapse : ℂ) * (if (2 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 2 * lorentzMatrix 3) s t *
    (if (supportNamed (s,c)).2 = (supportNamed (t,d)).2 then 1 else 0) = _
  rw [lapse_scale,row_88_original]
  simp only [support_explicit,lorentzTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_88,lorentzTable,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_89 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 58
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 58
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 58
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 58
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 58
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 58
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 59
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 59
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 59
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 59
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 59
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 59
  else 0

private theorem row_89_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 89 s t c d = row_89 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_89 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 89 (s,c) (t,d) = primalLiteral 89 s t c d := by
  rw [primitive_lorentz 89 (by decide)]
  change (lapse : ℂ) * (if (2 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 2 * lorentzMatrix 4) s t *
    (if (supportNamed (s,c)).2 = (supportNamed (t,d)).2 then 1 else 0) = _
  rw [lapse_scale,row_89_original]
  simp only [support_explicit,lorentzTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_89,lorentzTable,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_90 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 60
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 60
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 60
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 60
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 60
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 60
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 57
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 57
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 57
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 57
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 57
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 57
  else 0

private theorem row_90_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 90 s t c d = row_90 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_90 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 90 (s,c) (t,d) = primalLiteral 90 s t c d := by
  rw [primitive_lorentz 90 (by decide)]
  change (lapse : ℂ) * (if (2 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 2 * lorentzMatrix 5) s t *
    (if (supportNamed (s,c)).2 = (supportNamed (t,d)).2 then 1 else 0) = _
  rw [lapse_scale,row_90_original]
  simp only [support_explicit,lorentzTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_90,lorentzTable,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_91 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 57
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 57
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 57
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 60
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 60
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 60
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 57
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 57
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 57
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 60
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 60
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 60
  else 0

private theorem row_91_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 91 s t c d = row_91 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_91 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 91 (s,c) (t,d) = primalLiteral 91 s t c d := by
  rw [primitive_lorentz 91 (by decide)]
  change (lapse : ℂ) * (if (3 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 3 * lorentzMatrix 0) s t *
    (if (supportNamed (s,c)).2 = (supportNamed (t,d)).2 then 1 else 0) = _
  rw [lapse_scale,row_91_original]
  simp only [support_explicit,lorentzTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_91,lorentzTable,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_92 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 59
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 59
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 59
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 59
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 59
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 59
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 59
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 59
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 59
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 59
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 59
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 59
  else 0

private theorem row_92_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 92 s t c d = row_92 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_92 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 92 (s,c) (t,d) = primalLiteral 92 s t c d := by
  rw [primitive_lorentz 92 (by decide)]
  change (lapse : ℂ) * (if (3 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 3 * lorentzMatrix 1) s t *
    (if (supportNamed (s,c)).2 = (supportNamed (t,d)).2 then 1 else 0) = _
  rw [lapse_scale,row_92_original]
  simp only [support_explicit,lorentzTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_92,lorentzTable,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_93 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 57
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 57
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 57
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 57
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 57
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 57
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 57
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 57
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 57
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 57
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 57
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 57
  else 0

private theorem row_93_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 93 s t c d = row_93 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_93 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 93 (s,c) (t,d) = primalLiteral 93 s t c d := by
  rw [primitive_lorentz 93 (by decide)]
  change (lapse : ℂ) * (if (3 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 3 * lorentzMatrix 2) s t *
    (if (supportNamed (s,c)).2 = (supportNamed (t,d)).2 then 1 else 0) = _
  rw [lapse_scale,row_93_original]
  simp only [support_explicit,lorentzTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_93,lorentzTable,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_94 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 58
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 58
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 58
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 59
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 59
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 59
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 59
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 59
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 59
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 58
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 58
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 58
  else 0

private theorem row_94_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 94 s t c d = row_94 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_94 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 94 (s,c) (t,d) = primalLiteral 94 s t c d := by
  rw [primitive_lorentz 94 (by decide)]
  change (lapse : ℂ) * (if (3 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 3 * lorentzMatrix 3) s t *
    (if (supportNamed (s,c)).2 = (supportNamed (t,d)).2 then 1 else 0) = _
  rw [lapse_scale,row_94_original]
  simp only [support_explicit,lorentzTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_94,lorentzTable,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_95 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 57
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 57
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 57
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 57
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 57
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 57
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 60
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 60
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 60
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 60
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 60
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 60
  else 0

private theorem row_95_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 95 s t c d = row_95 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_95 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 95 (s,c) (t,d) = primalLiteral 95 s t c d := by
  rw [primitive_lorentz 95 (by decide)]
  change (lapse : ℂ) * (if (3 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 3 * lorentzMatrix 4) s t *
    (if (supportNamed (s,c)).2 = (supportNamed (t,d)).2 then 1 else 0) = _
  rw [lapse_scale,row_95_original]
  simp only [support_explicit,lorentzTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_95,lorentzTable,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_96 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 58
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 58
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 58
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 58
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 58
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 58
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 59
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 59
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 59
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 59
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 59
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 59
  else 0

private theorem row_96_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 96 s t c d = row_96 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_96 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 96 (s,c) (t,d) = primalLiteral 96 s t c d := by
  rw [primitive_lorentz 96 (by decide)]
  change (lapse : ℂ) * (if (3 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 3 * lorentzMatrix 5) s t *
    (if (supportNamed (s,c)).2 = (supportNamed (t,d)).2 then 1 else 0) = _
  rw [lapse_scale,row_96_original]
  simp only [support_explicit,lorentzTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_96,lorentzTable,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

theorem actual_lorentz_values (a : Fin 24) (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false ⟨a.val+73,by omega⟩ (s,c) (t,d) =
      primalLiteral ⟨a.val+73,by omega⟩ s t c d := by
  fin_cases a
  · exact primal_73 s t c d
  · exact primal_74 s t c d
  · exact primal_75 s t c d
  · exact primal_76 s t c d
  · exact primal_77 s t c d
  · exact primal_78 s t c d
  · exact primal_79 s t c d
  · exact primal_80 s t c d
  · exact primal_81 s t c d
  · exact primal_82 s t c d
  · exact primal_83 s t c d
  · exact primal_84 s t c d
  · exact primal_85 s t c d
  · exact primal_86 s t c d
  · exact primal_87 s t c d
  · exact primal_88 s t c d
  · exact primal_89 s t c d
  · exact primal_90 s t c d
  · exact primal_91 s t c d
  · exact primal_92 s t c d
  · exact primal_93 s t c d
  · exact primal_94 s t c d
  · exact primal_95 s t c d
  · exact primal_96 s t c d

end LowEnergy.ActualCandidateVertexValues
