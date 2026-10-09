import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualThreeParticleCutoffGram

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace LowEnergy.ActualThreeParticleCutoffGram
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory
open GaussDiagonalHistory GaussYukawaGrade GaussYukawaInteraction GaussCoreLabel
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent FullYSourceResolventGraphSplice
open FullYSourceCutoffVolterra SourceCutoffDilationWard NamedColorQtNext NativeHistoryGrade
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open scoped BigOperators InnerProductSpace
attribute [local irreducible] embed GaussCoreLabel.project NativeHistoryGrade.projection
  GaussGradedCompression.compression GaussYukawaGrade.grade

/-- The independent branch is the original conjugate-frequency adjoint, including its reversed word order. -/
def sharpInverse (F : Index) (n : ℕ) (z : ℂ) : H →L[ℂ] H := (inverse F n (star z)).adjoint
def sharpShift (F : Index) (n : ℕ) (z : ℂ) : H →L[ℂ] H :=
  GaussGradedCompression.compression F+(cutoff n).adjoint-z • 1

private theorem nonreal_star (z : ℂ) (hz : z.im≠0) : (star z).im≠0 := by
  simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz

private theorem star_shift {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
    (C Y : R) (hC : star C=C) (z : ℂ) :
    star (C+Y-(star z) • 1)=C+star Y-z • 1 := by
  simp only [star_sub,star_add,star_smul,star_star,star_one,hC]

private theorem star_inverse {R : Type*} [Ring R] [StarRing R] (D U : R) (h : D*U=1) :
    star U*star D=1 := by rw [←star_mul,h,star_one]

private theorem shift_adjoint (F : Index) (n : ℕ) (z : ℂ) :
    (shift F n (star z)).adjoint=sharpShift F n z :=
  star_shift _ _ (GaussGradedCompression.compression_selfAdjoint F).star_eq z

theorem actual_cutoff_sharp_left_inverse (F : Index) (n : ℕ) (z : ℂ) (hz : z.im≠0) :
    sharpInverse F n z*sharpShift F n z=1 := by
  have h := star_inverse _ _ (actual_cutoff_right_inverse F n (star z) (nonreal_star z hz))
  change (inverse F n (star z)).adjoint*(shift F n (star z)).adjoint=1 at h
  rw [shift_adjoint] at h
  exact h

theorem actual_cutoff_sharp_right_inverse (F : Index) (n : ℕ) (z : ℂ) (hz : z.im≠0) :
    sharpShift F n z*sharpInverse F n z=1 := by
  have h := star_inverse _ _ (actual_cutoff_left_inverse F n (star z) (nonreal_star z hz))
  change (shift F n (star z)).adjoint*(inverse F n (star z)).adjoint=1 at h
  rw [shift_adjoint] at h
  exact h

private theorem bottom_grade (q : QuantumTest) (hq : project (3,0) q=q) : gradeCore q=0 := by
  apply embed_injective
  rw [←grade_core,map_zero]
  have hp : projection (3,0) (embed q)=embed q :=
    (embed_project (3,0) q).symm.trans (congrArg embed hq)
  have h := congrArg (fun A : H →L[ℂ] H => A (embed q)) (source_grade_right (3,0))
  simpa [mul_apply_eq_comp,hp] using h

private theorem inverse_bottom (q : QuantumTest) (hq : project (3,0) q=q) :
    project (3,0) (GaussRadialDomain.inverseAction q)=GaussRadialDomain.inverseAction q := by
  apply DFunLike.ext
  intro x
  have h := congrArg (fun f : QuantumTest => f x) hq
  simp only [project_apply] at h
  rw [project_apply]
  change fiberPiece (3,0) ((GaussRadialDomain.reciprocal x : ℂ) • q x)=
    (GaussRadialDomain.reciprocal x : ℂ) • q x
  rw [map_smul,h]

private theorem sharp_vertex_bottom (q : QuantumTest) (hq : project (3,0) q=q) :
    sharpVertexAction q=0 :=
  actual_bottom_sharp_action _ (bottom_grade _ (inverse_bottom q hq))

private theorem sharp_cutoff_bottom (n : ℕ) (q : QuantumTest) (hq : project (3,0) q=q) :
    sharpCutoffAction n q=0 := by
  induction n generalizing q with
  | zero => exact sharp_vertex_bottom q hq
  | succ n ih =>
    change sharpVertexAction q+sharpCutoffAction n (q-GaussRadialDomain.inverseAction q)=0
    rw [sharp_vertex_bottom q hq,ih]
    · simp only [add_zero]
    · simp only [map_sub,hq,inverse_bottom q hq]

private theorem base_embed (F : Index) (z : ℂ) (hz : z.im≠0) (q : QuantumTest) :
    embed (resolventCore F z hz q)=finiteResolvent F z (embed q) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)

/-- On the actual bottom grade, the independent sharp inverse is the original base inverse at every cutoff. -/
theorem actual_sharp_response (F : Index) (n : ℕ) (z : ℂ) (hz : z.im≠0)
    (q : QuantumTest) (hq : project (3,0) q=q) :
    sharpInverse F n z (embed q)=finiteResolvent F z (embed q) := by
  have hy : (cutoff n).adjoint (finiteResolvent F z (embed q))=0 := by
    have hb := sharp_cutoff_bottom n (resolventCore F z hz q)
      (actual_resolvent_sector F (3,0) z hz q hq)
    have hc := sharp_cutoff_core n (resolventCore F z hz q)
    rw [hb,map_zero] at hc
    simpa only [base_embed F z hz q] using hc
  have he : sharpShift F n z (finiteResolvent F z (embed q))=embed q := by
    have hb := congrArg (fun A : H →L[ℂ] H => A (embed q))
      (resolvent_right (GaussGradedCompression.compression F)
        (GaussGradedCompression.compression_selfAdjoint F) z hz)
    change (GaussGradedCompression.compression F (finiteResolvent F z (embed q))-
      z • finiteResolvent F z (embed q))=embed q at hb
    simpa only [sharpShift,sub_apply,add_apply,smul_apply,one_apply_eq_self,hy,add_zero] using hb
  calc
    _ = sharpInverse F n z (sharpShift F n z (finiteResolvent F z (embed q))) := by rw [he]
    _ = _ := congrArg (fun A : H →L[ℂ] H => A (finiteResolvent F z (embed q)))
      (actual_cutoff_sharp_left_inverse F n z hz)

theorem actual_sharp_response_difference_zero (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im≠0)
    (q : QuantumTest) (hq : project (3,0) q=q) :
    sharpInverse F ell z (embed q)-sharpInverse F m z (embed q)=0 := by
  rw [actual_sharp_response F ell z hz q hq,actual_sharp_response F m z hz q hq,sub_self]

end LowEnergy.ActualThreeParticleCutoffGram
