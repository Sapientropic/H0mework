import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeFirstCurrentDefectDescent
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeProjectionCurrentRemainder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.SourceInverseDefectCurrentPair
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarDoubleCurrent SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceScalarVirialBulk
open SourceInverseFirstCurrentDefectDescent FullYSourceResolventGraphSplice Filter
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] diagonalAction compressionCore defectAction state sourcePair
  GaussAdjointHistory.coreStep GaussAdjointHistory.iterate

private theorem compression_embed (F : Index) (f : QuantumTest) :
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem defect_pair (F : Index) (f g : QuantumTest) :
    sourcePair f (defectAction F g)=sourcePair (defectAction F f) g := by
  have hc : sourcePair f (compressionCore F g)=sourcePair (compressionCore F f) g := by
    simp only [sourcePair,compression_embed]
    exact ((GaussGradedCompression.compression_selfAdjoint F).isSymmetric _ _).symm
  unfold defectAction
  simp only [LinearMap.sub_apply,sourcePair,map_sub,inner_sub_left,inner_sub_right]
  simpa only [sourcePair] using!
    congrArg₂ (fun a b : ℂ => a-b) (diagonalAction_pair f g) hc

private theorem pair_sub_left (a b c : QuantumTest) : sourcePair (a-b) c=sourcePair a c-sourcePair b c := by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_right (a b c : QuantumTest) : sourcePair a (b-c)=sourcePair a b-sourcePair a c := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_left (c : ℂ) (a b : QuantumTest) : sourcePair (c • a) b=star c*sourcePair a b := by
  simp only [sourcePair,map_smul,inner_smul_left,Complex.star_def]
private theorem pair_smul_right (c : ℂ) (a b : QuantumTest) : sourcePair a (c • b)=c*sourcePair a b := by
  simp only [sourcePair,map_smul,inner_smul_right]

/-- A skew-adjoint source pair generates a positive-sign dual pair for the complete defect current. -/
theorem original_defect_pair (A B : End)
    (hAB : ∀ f g,sourcePair f (A g)= -sourcePair (B f) g)
    (F : Index) (f g : QuantumTest) :
    sourcePair f (bracket (defectAction F) A g)=sourcePair (bracket (defectAction F) B f) g := by
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,pair_sub_right,pair_sub_left]
  rw [defect_pair,hAB,hAB,defect_pair]
  ring

/-- Both actual frequencies descend on one cofinal set; neither retarded state is made fixed. -/
theorem actual_two_frequency_descent (A B : End)
    (hAB : ∀ f g,sourcePair f (A g)= -sourcePair (B f) g)
    (r s : ℕ) (g k : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0),
      (star zl)^s*zr^r*sourcePair (state F zl hl k)
        (bracket (defectAction F) A (state F zr hr g))=
      sourcePair (state F zl hl (GaussAdjointHistory.iterate s k))
        (bracket (defectAction F) A (state F zr hr (GaussAdjointHistory.iterate r g))) := by
  filter_upwards [actual_retarded_defect_descent A r g,
    actual_retarded_defect_descent B s k] with F hR hL zl zr hl hr
  have hright := congrArg (fun q => sourcePair (state F zl hl k) q) (hR zr hr)
  rw [pair_smul_right] at hright
  have hleft := congrArg
    (fun p => sourcePair p (state F zr hr (GaussAdjointHistory.iterate r g))) (hL zl hl)
  rw [pair_smul_left,star_pow] at hleft
  calc
    _ = (star zl)^s*sourcePair (state F zl hl k)
        (bracket (defectAction F) A (state F zr hr (GaussAdjointHistory.iterate r g))) := by
      rw [mul_assoc,hright]
    _ = _ := by
      rw [original_defect_pair A B hAB,hleft,original_defect_pair A B hAB]

/-- On the physical conjugate/nonconjugate legs the exact factor is z^(r+s), not a modulus square. -/
theorem actual_retarded_pair_descent (A B : End)
    (hAB : ∀ f g,sourcePair f (A g)= -sourcePair (B f) g)
    (r s : ℕ) (g k : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ (z : ℂ) (hz : z.im≠0),
      z^(r+s)*sourcePair (state F (star z)
        (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
        (bracket (defectAction F) A (state F z hz g))=
      sourcePair (state F (star z)
        (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz)
        (GaussAdjointHistory.iterate s k))
        (bracket (defectAction F) A (state F z hz (GaussAdjointHistory.iterate r g))) := by
  filter_upwards [actual_two_frequency_descent A B hAB r s g k] with F hF z hz
  have h := hF (star z) z (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) hz
  simpa only [star_star,pow_add,mul_comm (z^s) (z^r)] using h

end LowEnergy.SourceInverseDefectCurrentPair
