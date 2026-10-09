import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateVertexValueKernel
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualCandidateVertexLiterals

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option linter.unusedTactic false
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

private theorem support_explicit (i : Support) :
    supportNamed i = (i.1,i.2,(![0,0,1,1] : Fin 4 → Fin 2) i.1) := by
  rcases i with ⟨s,c⟩
  fin_cases s <;> rfl

private def row_9 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 1 then coefficient 0
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 0 then coefficient 1
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 1 then coefficient 0
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 0 then coefficient 1
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 1 then coefficient 0
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 0 then coefficient 1
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 1 then coefficient 0
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 0 then coefficient 1
  else 0

private theorem row_9_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 9 s t c d = row_9 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_9 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 9 (s,c) (t,d) = primalLiteral 9 s t c d := by
  rw [primitive_gauge 9 (by decide) (by decide)]
  change (lapse : ℂ) * (if (0 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 0) s t *
    gaugeEntry (nativeMother 0) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_9_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_9,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_10 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 1 then coefficient 2
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 0 then coefficient 2
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 1 then coefficient 2
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 0 then coefficient 2
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 1 then coefficient 2
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 0 then coefficient 2
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 1 then coefficient 2
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 0 then coefficient 2
  else 0

private theorem row_10_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 10 s t c d = row_10 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_10 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 10 (s,c) (t,d) = primalLiteral 10 s t c d := by
  rw [primitive_gauge 10 (by decide) (by decide)]
  change (lapse : ℂ) * (if (0 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 0) s t *
    gaugeEntry (nativeMother 1) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_10_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_10,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_11 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 2 then coefficient 0
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 0 then coefficient 1
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 2 then coefficient 0
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 0 then coefficient 1
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 2 then coefficient 0
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 0 then coefficient 1
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 2 then coefficient 0
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 0 then coefficient 1
  else 0

private theorem row_11_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 11 s t c d = row_11 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_11 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 11 (s,c) (t,d) = primalLiteral 11 s t c d := by
  rw [primitive_gauge 11 (by decide) (by decide)]
  change (lapse : ℂ) * (if (0 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 0) s t *
    gaugeEntry (nativeMother 2) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_11_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_11,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_12 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 2 then coefficient 2
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 0 then coefficient 2
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 2 then coefficient 2
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 0 then coefficient 2
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 2 then coefficient 2
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 0 then coefficient 2
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 2 then coefficient 2
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 0 then coefficient 2
  else 0

private theorem row_12_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 12 s t c d = row_12 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_12 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 12 (s,c) (t,d) = primalLiteral 12 s t c d := by
  rw [primitive_gauge 12 (by decide) (by decide)]
  change (lapse : ℂ) * (if (0 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 0) s t *
    gaugeEntry (nativeMother 3) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_12_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_12,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_13 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 2 then coefficient 0
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 1 then coefficient 1
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 2 then coefficient 0
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 1 then coefficient 1
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 2 then coefficient 0
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 1 then coefficient 1
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 2 then coefficient 0
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 1 then coefficient 1
  else 0

private theorem row_13_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 13 s t c d = row_13 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_13 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 13 (s,c) (t,d) = primalLiteral 13 s t c d := by
  rw [primitive_gauge 13 (by decide) (by decide)]
  change (lapse : ℂ) * (if (0 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 0) s t *
    gaugeEntry (nativeMother 4) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_13_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_13,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_14 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 2 then coefficient 2
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 1 then coefficient 2
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 2 then coefficient 2
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 1 then coefficient 2
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 2 then coefficient 2
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 1 then coefficient 2
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 2 then coefficient 2
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 1 then coefficient 2
  else 0

private theorem row_14_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 14 s t c d = row_14 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_14 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 14 (s,c) (t,d) = primalLiteral 14 s t c d := by
  rw [primitive_gauge 14 (by decide) (by decide)]
  change (lapse : ℂ) * (if (0 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 0) s t *
    gaugeEntry (nativeMother 5) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_14_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_14,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_15 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 2
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 3
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 2
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 3
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 2
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 3
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 2
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 3
  else 0

private theorem row_15_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 15 s t c d = row_15 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_15 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 15 (s,c) (t,d) = primalLiteral 15 s t c d := by
  rw [primitive_gauge 15 (by decide) (by decide)]
  change (lapse : ℂ) * (if (0 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 0) s t *
    gaugeEntry (nativeMother 6) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_15_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_15,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_16 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 2
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 3
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 2
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 3
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 2
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 3
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 2
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 3
  else 0

private theorem row_16_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 16 s t c d = row_16 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_16 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 16 (s,c) (t,d) = primalLiteral 16 s t c d := by
  rw [primitive_gauge 16 (by decide) (by decide)]
  change (lapse : ℂ) * (if (0 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 0) s t *
    gaugeEntry (nativeMother 7) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_16_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_16,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_17 (_s _t : Fin 4) (_c _d : Fin 3) : ℂ :=
  0

private theorem row_17_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 17 s t c d = row_17 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_17 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 17 (s,c) (t,d) = primalLiteral 17 s t c d := by
  rw [primitive_gauge 17 (by decide) (by decide)]
  change (lapse : ℂ) * (if (0 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 0) s t *
    gaugeEntry (nativeMother 8) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_17_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_17,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_18 (_s _t : Fin 4) (_c _d : Fin 3) : ℂ :=
  0

private theorem row_18_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 18 s t c d = row_18 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_18 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 18 (s,c) (t,d) = primalLiteral 18 s t c d := by
  rw [primitive_gauge 18 (by decide) (by decide)]
  change (lapse : ℂ) * (if (0 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 0) s t *
    gaugeEntry (nativeMother 9) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_18_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_18,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_19 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 2
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 2
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 2
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 2
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 2
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 2
  else 0

private theorem row_19_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 19 s t c d = row_19 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_19 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 19 (s,c) (t,d) = primalLiteral 19 s t c d := by
  rw [primitive_gauge 19 (by decide) (by decide)]
  change (lapse : ℂ) * (if (0 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 0) s t *
    gaugeEntry (nativeMother 10) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_19_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_19,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_20 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 2
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 2
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 2
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 2
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 2
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 2
  else 0

private theorem row_20_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 20 s t c d = row_20 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_20 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 20 (s,c) (t,d) = primalLiteral 20 s t c d := by
  rw [primitive_gauge 20 (by decide) (by decide)]
  change (lapse : ℂ) * (if (0 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 0) s t *
    gaugeEntry (nativeMother 11) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_20_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_20,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_21 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 1 then coefficient 4
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 0 then coefficient 5
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 1 then coefficient 4
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 0 then coefficient 5
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 1 then coefficient 5
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 0 then coefficient 4
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 1 then coefficient 5
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 0 then coefficient 4
  else 0

private theorem row_21_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 21 s t c d = row_21 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_21 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 21 (s,c) (t,d) = primalLiteral 21 s t c d := by
  rw [primitive_gauge 21 (by decide) (by decide)]
  change (lapse : ℂ) * (if (1 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 1) s t *
    gaugeEntry (nativeMother 0) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_21_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_21,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_22 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 1 then coefficient 6
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 0 then coefficient 6
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 1 then coefficient 6
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 0 then coefficient 6
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 1 then coefficient 7
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 0 then coefficient 7
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 1 then coefficient 7
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 0 then coefficient 7
  else 0

private theorem row_22_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 22 s t c d = row_22 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_22 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 22 (s,c) (t,d) = primalLiteral 22 s t c d := by
  rw [primitive_gauge 22 (by decide) (by decide)]
  change (lapse : ℂ) * (if (1 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 1) s t *
    gaugeEntry (nativeMother 1) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_22_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_22,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_23 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 2 then coefficient 4
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 0 then coefficient 5
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 2 then coefficient 4
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 0 then coefficient 5
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 2 then coefficient 5
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 0 then coefficient 4
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 2 then coefficient 5
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 0 then coefficient 4
  else 0

private theorem row_23_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 23 s t c d = row_23 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_23 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 23 (s,c) (t,d) = primalLiteral 23 s t c d := by
  rw [primitive_gauge 23 (by decide) (by decide)]
  change (lapse : ℂ) * (if (1 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 1) s t *
    gaugeEntry (nativeMother 2) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_23_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_23,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_24 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 2 then coefficient 6
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 0 then coefficient 6
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 2 then coefficient 6
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 0 then coefficient 6
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 2 then coefficient 7
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 0 then coefficient 7
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 2 then coefficient 7
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 0 then coefficient 7
  else 0

private theorem row_24_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 24 s t c d = row_24 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_24 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 24 (s,c) (t,d) = primalLiteral 24 s t c d := by
  rw [primitive_gauge 24 (by decide) (by decide)]
  change (lapse : ℂ) * (if (1 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 1) s t *
    gaugeEntry (nativeMother 3) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_24_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_24,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_25 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 2 then coefficient 4
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 1 then coefficient 5
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 2 then coefficient 4
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 1 then coefficient 5
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 2 then coefficient 5
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 1 then coefficient 4
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 2 then coefficient 5
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 1 then coefficient 4
  else 0

private theorem row_25_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 25 s t c d = row_25 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_25 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 25 (s,c) (t,d) = primalLiteral 25 s t c d := by
  rw [primitive_gauge 25 (by decide) (by decide)]
  change (lapse : ℂ) * (if (1 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 1) s t *
    gaugeEntry (nativeMother 4) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_25_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_25,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_26 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 2 then coefficient 6
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 1 then coefficient 6
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 2 then coefficient 6
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 1 then coefficient 6
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 2 then coefficient 7
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 1 then coefficient 7
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 2 then coefficient 7
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 1 then coefficient 7
  else 0

private theorem row_26_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 26 s t c d = row_26 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_26 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 26 (s,c) (t,d) = primalLiteral 26 s t c d := by
  rw [primitive_gauge 26 (by decide) (by decide)]
  change (lapse : ℂ) * (if (1 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 1) s t *
    gaugeEntry (nativeMother 5) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_26_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_26,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_27 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 6
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 7
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 6
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 7
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 7
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 6
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 7
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 6
  else 0

private theorem row_27_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 27 s t c d = row_27 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_27 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 27 (s,c) (t,d) = primalLiteral 27 s t c d := by
  rw [primitive_gauge 27 (by decide) (by decide)]
  change (lapse : ℂ) * (if (1 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 1) s t *
    gaugeEntry (nativeMother 6) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_27_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_27,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_28 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 6
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 7
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 6
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 7
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 7
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 6
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 7
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 6
  else 0

private theorem row_28_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 28 s t c d = row_28 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_28 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 28 (s,c) (t,d) = primalLiteral 28 s t c d := by
  rw [primitive_gauge 28 (by decide) (by decide)]
  change (lapse : ℂ) * (if (1 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 1) s t *
    gaugeEntry (nativeMother 7) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_28_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_28,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_29 (_s _t : Fin 4) (_c _d : Fin 3) : ℂ :=
  0

private theorem row_29_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 29 s t c d = row_29 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_29 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 29 (s,c) (t,d) = primalLiteral 29 s t c d := by
  rw [primitive_gauge 29 (by decide) (by decide)]
  change (lapse : ℂ) * (if (1 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 1) s t *
    gaugeEntry (nativeMother 8) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_29_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_29,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_30 (_s _t : Fin 4) (_c _d : Fin 3) : ℂ :=
  0

private theorem row_30_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 30 s t c d = row_30 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_30 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 30 (s,c) (t,d) = primalLiteral 30 s t c d := by
  rw [primitive_gauge 30 (by decide) (by decide)]
  change (lapse : ℂ) * (if (1 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 1) s t *
    gaugeEntry (nativeMother 9) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_30_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_30,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_31 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 7
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 7
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 7
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 7
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 7
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 7
  else 0

private theorem row_31_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 31 s t c d = row_31 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_31 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 31 (s,c) (t,d) = primalLiteral 31 s t c d := by
  rw [primitive_gauge 31 (by decide) (by decide)]
  change (lapse : ℂ) * (if (1 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 1) s t *
    gaugeEntry (nativeMother 10) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_31_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_31,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_32 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 6
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 6
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 6
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 6
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 6
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 6
  else 0

private theorem row_32_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 32 s t c d = row_32 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_32 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 32 (s,c) (t,d) = primalLiteral 32 s t c d := by
  rw [primitive_gauge 32 (by decide) (by decide)]
  change (lapse : ℂ) * (if (1 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 1) s t *
    gaugeEntry (nativeMother 11) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_32_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_32,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_33 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 1 then coefficient 7
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 0 then coefficient 6
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 1 then coefficient 6
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 0 then coefficient 7
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 1 then coefficient 6
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 0 then coefficient 7
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 1 then coefficient 7
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 0 then coefficient 6
  else 0

private theorem row_33_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 33 s t c d = row_33 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_33 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 33 (s,c) (t,d) = primalLiteral 33 s t c d := by
  rw [primitive_gauge 33 (by decide) (by decide)]
  change (lapse : ℂ) * (if (2 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 2) s t *
    gaugeEntry (nativeMother 0) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_33_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_33,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_34 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 1 then coefficient 4
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 0 then coefficient 4
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 1 then coefficient 5
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 0 then coefficient 5
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 1 then coefficient 5
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 0 then coefficient 5
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 1 then coefficient 4
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 0 then coefficient 4
  else 0

private theorem row_34_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 34 s t c d = row_34 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_34 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 34 (s,c) (t,d) = primalLiteral 34 s t c d := by
  rw [primitive_gauge 34 (by decide) (by decide)]
  change (lapse : ℂ) * (if (2 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 2) s t *
    gaugeEntry (nativeMother 1) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_34_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_34,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_35 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 2 then coefficient 7
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 0 then coefficient 6
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 2 then coefficient 6
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 0 then coefficient 7
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 2 then coefficient 6
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 0 then coefficient 7
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 2 then coefficient 7
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 0 then coefficient 6
  else 0

private theorem row_35_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 35 s t c d = row_35 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_35 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 35 (s,c) (t,d) = primalLiteral 35 s t c d := by
  rw [primitive_gauge 35 (by decide) (by decide)]
  change (lapse : ℂ) * (if (2 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 2) s t *
    gaugeEntry (nativeMother 2) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_35_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_35,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_36 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 2 then coefficient 4
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 0 then coefficient 4
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 2 then coefficient 5
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 0 then coefficient 5
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 2 then coefficient 5
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 0 then coefficient 5
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 2 then coefficient 4
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 0 then coefficient 4
  else 0

private theorem row_36_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 36 s t c d = row_36 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_36 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 36 (s,c) (t,d) = primalLiteral 36 s t c d := by
  rw [primitive_gauge 36 (by decide) (by decide)]
  change (lapse : ℂ) * (if (2 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 2) s t *
    gaugeEntry (nativeMother 3) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_36_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_36,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_37 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 2 then coefficient 7
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 1 then coefficient 6
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 2 then coefficient 6
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 1 then coefficient 7
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 2 then coefficient 6
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 1 then coefficient 7
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 2 then coefficient 7
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 1 then coefficient 6
  else 0

private theorem row_37_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 37 s t c d = row_37 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_37 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 37 (s,c) (t,d) = primalLiteral 37 s t c d := by
  rw [primitive_gauge 37 (by decide) (by decide)]
  change (lapse : ℂ) * (if (2 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 2) s t *
    gaugeEntry (nativeMother 4) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_37_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_37,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_38 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 2 then coefficient 4
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 1 then coefficient 4
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 2 then coefficient 5
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 1 then coefficient 5
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 2 then coefficient 5
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 1 then coefficient 5
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 2 then coefficient 4
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 1 then coefficient 4
  else 0

private theorem row_38_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 38 s t c d = row_38 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_38 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 38 (s,c) (t,d) = primalLiteral 38 s t c d := by
  rw [primitive_gauge 38 (by decide) (by decide)]
  change (lapse : ℂ) * (if (2 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 2) s t *
    gaugeEntry (nativeMother 5) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_38_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_38,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_39 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 4
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 5
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 5
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 4
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 5
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 4
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 4
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 5
  else 0

private theorem row_39_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 39 s t c d = row_39 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_39 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 39 (s,c) (t,d) = primalLiteral 39 s t c d := by
  rw [primitive_gauge 39 (by decide) (by decide)]
  change (lapse : ℂ) * (if (2 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 2) s t *
    gaugeEntry (nativeMother 6) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_39_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_39,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_40 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 4
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 5
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 5
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 4
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 5
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 4
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 4
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 5
  else 0

private theorem row_40_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 40 s t c d = row_40 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_40 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 40 (s,c) (t,d) = primalLiteral 40 s t c d := by
  rw [primitive_gauge 40 (by decide) (by decide)]
  change (lapse : ℂ) * (if (2 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 2) s t *
    gaugeEntry (nativeMother 7) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_40_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_40,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_41 (_s _t : Fin 4) (_c _d : Fin 3) : ℂ :=
  0

private theorem row_41_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 41 s t c d = row_41 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_41 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 41 (s,c) (t,d) = primalLiteral 41 s t c d := by
  rw [primitive_gauge 41 (by decide) (by decide)]
  change (lapse : ℂ) * (if (2 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 2) s t *
    gaugeEntry (nativeMother 8) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_41_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_41,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_42 (_s _t : Fin 4) (_c _d : Fin 3) : ℂ :=
  0

private theorem row_42_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 42 s t c d = row_42 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_42 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 42 (s,c) (t,d) = primalLiteral 42 s t c d := by
  rw [primitive_gauge 42 (by decide) (by decide)]
  change (lapse : ℂ) * (if (2 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 2) s t *
    gaugeEntry (nativeMother 9) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_42_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_42,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_43 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 2 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 5
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 5
  else if s.val = 2 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 5
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 4
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 4
  else if s.val = 3 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 4
  else 0

private theorem row_43_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 43 s t c d = row_43 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_43 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 43 (s,c) (t,d) = primalLiteral 43 s t c d := by
  rw [primitive_gauge 43 (by decide) (by decide)]
  change (lapse : ℂ) * (if (2 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 2) s t *
    gaugeEntry (nativeMother 10) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_43_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_43,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_44 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 4
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 4
  else if s.val = 0 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 4
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 5
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 5
  else if s.val = 1 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 5
  else 0

private theorem row_44_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 44 s t c d = row_44 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_44 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 44 (s,c) (t,d) = primalLiteral 44 s t c d := by
  rw [primitive_gauge 44 (by decide) (by decide)]
  change (lapse : ℂ) * (if (2 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 2) s t *
    gaugeEntry (nativeMother 11) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_44_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_44,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_45 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 1 then coefficient 4
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 0 then coefficient 5
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 1 then coefficient 5
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 0 then coefficient 4
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 1 then coefficient 5
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 0 then coefficient 4
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 1 then coefficient 4
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 0 then coefficient 5
  else 0

private theorem row_45_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 45 s t c d = row_45 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_45 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 45 (s,c) (t,d) = primalLiteral 45 s t c d := by
  rw [primitive_gauge 45 (by decide) (by decide)]
  change (lapse : ℂ) * (if (3 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 3) s t *
    gaugeEntry (nativeMother 0) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_45_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_45,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_46 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 1 then coefficient 6
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 0 then coefficient 6
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 1 then coefficient 7
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 0 then coefficient 7
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 1 then coefficient 7
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 0 then coefficient 7
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 1 then coefficient 6
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 0 then coefficient 6
  else 0

private theorem row_46_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 46 s t c d = row_46 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_46 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 46 (s,c) (t,d) = primalLiteral 46 s t c d := by
  rw [primitive_gauge 46 (by decide) (by decide)]
  change (lapse : ℂ) * (if (3 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 3) s t *
    gaugeEntry (nativeMother 1) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_46_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_46,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_47 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 2 then coefficient 4
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 0 then coefficient 5
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 2 then coefficient 5
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 0 then coefficient 4
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 2 then coefficient 5
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 0 then coefficient 4
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 2 then coefficient 4
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 0 then coefficient 5
  else 0

private theorem row_47_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 47 s t c d = row_47 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_47 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 47 (s,c) (t,d) = primalLiteral 47 s t c d := by
  rw [primitive_gauge 47 (by decide) (by decide)]
  change (lapse : ℂ) * (if (3 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 3) s t *
    gaugeEntry (nativeMother 2) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_47_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_47,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_48 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 2 then coefficient 6
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 0 then coefficient 6
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 2 then coefficient 7
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 0 then coefficient 7
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 2 then coefficient 7
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 0 then coefficient 7
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 2 then coefficient 6
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 0 then coefficient 6
  else 0

private theorem row_48_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 48 s t c d = row_48 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_48 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 48 (s,c) (t,d) = primalLiteral 48 s t c d := by
  rw [primitive_gauge 48 (by decide) (by decide)]
  change (lapse : ℂ) * (if (3 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 3) s t *
    gaugeEntry (nativeMother 3) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_48_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_48,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_49 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 2 then coefficient 4
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 1 then coefficient 5
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 2 then coefficient 5
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 1 then coefficient 4
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 2 then coefficient 5
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 1 then coefficient 4
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 2 then coefficient 4
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 1 then coefficient 5
  else 0

private theorem row_49_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 49 s t c d = row_49 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_49 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 49 (s,c) (t,d) = primalLiteral 49 s t c d := by
  rw [primitive_gauge 49 (by decide) (by decide)]
  change (lapse : ℂ) * (if (3 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 3) s t *
    gaugeEntry (nativeMother 4) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_49_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_49,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_50 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 2 then coefficient 6
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 1 then coefficient 6
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 2 then coefficient 7
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 1 then coefficient 7
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 2 then coefficient 7
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 1 then coefficient 7
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 2 then coefficient 6
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 1 then coefficient 6
  else 0

private theorem row_50_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 50 s t c d = row_50 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_50 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 50 (s,c) (t,d) = primalLiteral 50 s t c d := by
  rw [primitive_gauge 50 (by decide) (by decide)]
  change (lapse : ℂ) * (if (3 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 3) s t *
    gaugeEntry (nativeMother 5) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_50_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_50,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_51 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 6
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 7
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 7
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 6
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 7
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 6
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 6
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 7
  else 0

private theorem row_51_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 51 s t c d = row_51 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_51 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 51 (s,c) (t,d) = primalLiteral 51 s t c d := by
  rw [primitive_gauge 51 (by decide) (by decide)]
  change (lapse : ℂ) * (if (3 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 3) s t *
    gaugeEntry (nativeMother 6) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_51_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_51,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_52 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 6
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 7
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 7
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 6
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 7
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 6
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 6
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 7
  else 0

private theorem row_52_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 52 s t c d = row_52 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_52 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 52 (s,c) (t,d) = primalLiteral 52 s t c d := by
  rw [primitive_gauge 52 (by decide) (by decide)]
  change (lapse : ℂ) * (if (3 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 3) s t *
    gaugeEntry (nativeMother 7) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_52_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_52,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_53 (_s _t : Fin 4) (_c _d : Fin 3) : ℂ :=
  0

private theorem row_53_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 53 s t c d = row_53 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_53 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 53 (s,c) (t,d) = primalLiteral 53 s t c d := by
  rw [primitive_gauge 53 (by decide) (by decide)]
  change (lapse : ℂ) * (if (3 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 3) s t *
    gaugeEntry (nativeMother 8) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_53_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_53,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_54 (_s _t : Fin 4) (_c _d : Fin 3) : ℂ :=
  0

private theorem row_54_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 54 s t c d = row_54 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_54 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 54 (s,c) (t,d) = primalLiteral 54 s t c d := by
  rw [primitive_gauge 54 (by decide) (by decide)]
  change (lapse : ℂ) * (if (3 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 3) s t *
    gaugeEntry (nativeMother 9) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_54_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_54,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_55 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 2 ∧ t.val = 2 ∧ c.val = 0 ∧ d.val = 0 then coefficient 7
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 1 ∧ d.val = 1 then coefficient 7
  else if s.val = 2 ∧ t.val = 2 ∧ c.val = 2 ∧ d.val = 2 then coefficient 7
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 0 ∧ d.val = 0 then coefficient 6
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 1 ∧ d.val = 1 then coefficient 6
  else if s.val = 3 ∧ t.val = 3 ∧ c.val = 2 ∧ d.val = 2 then coefficient 6
  else 0

private theorem row_55_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 55 s t c d = row_55 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_55 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 55 (s,c) (t,d) = primalLiteral 55 s t c d := by
  rw [primitive_gauge 55 (by decide) (by decide)]
  change (lapse : ℂ) * (if (3 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 3) s t *
    gaugeEntry (nativeMother 10) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_55_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_55,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

private def row_56 (s t : Fin 4) (c d : Fin 3) : ℂ :=
  if s.val = 0 ∧ t.val = 0 ∧ c.val = 0 ∧ d.val = 0 then coefficient 6
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 1 ∧ d.val = 1 then coefficient 6
  else if s.val = 0 ∧ t.val = 0 ∧ c.val = 2 ∧ d.val = 2 then coefficient 6
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 0 ∧ d.val = 0 then coefficient 7
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 1 ∧ d.val = 1 then coefficient 7
  else if s.val = 1 ∧ t.val = 1 ∧ c.val = 2 ∧ d.val = 2 then coefficient 7
  else 0

private theorem row_56_original (s t : Fin 4) (c d : Fin 3) :
    primalLiteral 56 s t c d = row_56 s t c d := by
  fin_cases s <;> fin_cases t <;> fin_cases c <;> fin_cases d <;> rfl

private theorem primal_56 (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false 56 (s,c) (t,d) = primalLiteral 56 s t c d := by
  rw [primitive_gauge 56 (by decide) (by decide)]
  change (lapse : ℂ) * (if (3 : Fin 4) = 0 then Complex.I / (lapse : ℂ) else Complex.I) *
    (diracGammaZero * diracGamma 3) s t *
    gaugeEntry (nativeMother 11) c (supportNamed (s,c)).2.2 d (supportNamed (t,d)).2.2 = _
  rw [lapse_scale,row_56_original]
  simp only [nativeMother,p286_entry,native_color,native_weak,native_hyper,support_explicit,sourceColorTable_original]
  fin_cases s <;> fin_cases t <;>
    norm_num [row_56,diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,supportNamed]
  all_goals fin_cases c <;> fin_cases d <;> norm_num [sourceColorTable,weakRaw,coefficient]
  all_goals try ring_nf
  all_goals norm_num [Complex.I_sq,Fin.lt_def,Fin.le_def,Fin.ext_iff]

theorem actual_gauge_values (a : Fin 48) (s t : Fin 4) (c d : Fin 3) :
    primitiveEntry 0 false ⟨a.val+9,by omega⟩ (s,c) (t,d) =
      primalLiteral ⟨a.val+9,by omega⟩ s t c d := by
  fin_cases a
  · exact primal_9 s t c d
  · exact primal_10 s t c d
  · exact primal_11 s t c d
  · exact primal_12 s t c d
  · exact primal_13 s t c d
  · exact primal_14 s t c d
  · exact primal_15 s t c d
  · exact primal_16 s t c d
  · exact primal_17 s t c d
  · exact primal_18 s t c d
  · exact primal_19 s t c d
  · exact primal_20 s t c d
  · exact primal_21 s t c d
  · exact primal_22 s t c d
  · exact primal_23 s t c d
  · exact primal_24 s t c d
  · exact primal_25 s t c d
  · exact primal_26 s t c d
  · exact primal_27 s t c d
  · exact primal_28 s t c d
  · exact primal_29 s t c d
  · exact primal_30 s t c d
  · exact primal_31 s t c d
  · exact primal_32 s t c d
  · exact primal_33 s t c d
  · exact primal_34 s t c d
  · exact primal_35 s t c d
  · exact primal_36 s t c d
  · exact primal_37 s t c d
  · exact primal_38 s t c d
  · exact primal_39 s t c d
  · exact primal_40 s t c d
  · exact primal_41 s t c d
  · exact primal_42 s t c d
  · exact primal_43 s t c d
  · exact primal_44 s t c d
  · exact primal_45 s t c d
  · exact primal_46 s t c d
  · exact primal_47 s t c d
  · exact primal_48 s t c d
  · exact primal_49 s t c d
  · exact primal_50 s t c d
  · exact primal_51 s t c d
  · exact primal_52 s t c d
  · exact primal_53 s t c d
  · exact primal_54 s t c d
  · exact primal_55 s t c d
  · exact primal_56 s t c d

end LowEnergy.ActualCandidateVertexValues
