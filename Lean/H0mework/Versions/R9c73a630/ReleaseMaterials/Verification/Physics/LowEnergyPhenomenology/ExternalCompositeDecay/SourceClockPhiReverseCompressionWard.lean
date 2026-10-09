import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiFullReverseScale
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseNativeFrequencyWard
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory GaussUnitaryHistory
open SourceClockYukawaCubicCurrent SourceScalarPairedTransport SourceScalarPositiveBulkWard
open FullYSourceResolventGraphSplice SourceScalarDoubleCurrent ReverseNativeClock
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev Z:End:=reverseNativeClock
attribute [local irreducible] embed diagonalAction compressionCore resolventCore reverseNativeClock reverseScaleForce

def reverseCompressionForce(F:Index):End:=
  reverseScaleForce+(18:ℂ) • defectAction F-bracket Z (defectAction F)
private theorem resolvent_embed(F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest):
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f):=by
  unfold resolventCore state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem compression_embed(F:Index)(f:QuantumTest):
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f):=by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
theorem actual_original_cf_inverses(F:Index)(z:ℂ)(hz:z.im≠0):
    (compressionCore F-z • (1:End))*resolventCore F z hz=1 ∧
    resolventCore F z hz*(compressionCore F-z • (1:End))=1:=by
  constructor
  · apply LinearMap.ext
    intro f
    apply embed_injective
    simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
      map_sub,map_smul,compression_embed,resolvent_embed]
    have h:=congrArg (fun A:H→L[ℂ]H=>A (embed f))
      (resolvent_right (GaussGradedCompression.compression F)
        (GaussGradedCompression.compression_selfAdjoint F) z hz)
    simpa only [finiteResolvent,mul_apply_eq_comp,sub_apply,smul_apply,one_apply_eq_self,map_sub,map_smul] using h
  · apply LinearMap.ext
    intro f
    apply embed_injective
    simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
      map_sub,map_smul,resolvent_embed,compression_embed]
    have h:=congrArg (fun A:H→L[ℂ]H=>A (embed f))
      (resolvent_left (GaussGradedCompression.compression F)
        (GaussGradedCompression.compression_selfAdjoint F) z hz)
    simpa only [finiteResolvent,mul_apply_eq_comp,sub_apply,smul_apply,one_apply_eq_self,map_sub,map_smul] using h

/-- The literal compression defect and its Z commutator stay inside the generated force. -/
theorem actual_reverse_compression_scale(F:Index):
    bracket Z (compressionCore F)=(18:ℂ) • compressionCore F+reverseCompressionForce F:=by
  have h:=actual_reverse_full_hamiltonian_scale
  unfold reverseCompressionForce defectAction
  unfold bracket at h ⊢
  simp only [mul_sub,sub_mul]
  linear_combination (norm:=module) h

private theorem inverse_commutator(A C R:End)(hL:R*C=1)(hR:C*R=1):
    bracket A R= -R*bracket A C*R:=by
  symm
  calc
    -R*bracket A C*R= -(R*A*(C*R))+(R*C)*A*R:=by unfold bracket;noncomm_ring
    _=bracket A R:=by rw [hR,hL];unfold bracket;noncomm_ring

/-- The scale coefficient multiplies the actual resolvent frequency derivative; it is not a physical-time growth exponent. -/
theorem actual_reverse_resolvent_ward(F:Index)(z:ℂ)(hz:z.im≠0):
    let R:End:=resolventCore F z hz
    bracket Z R+(18:ℂ) • (R+z • (R*R))= -R*reverseCompressionForce F*R:=by
  dsimp only
  let R:End:=resolventCore F z hz
  let C:End:=compressionCore F-z • (1:End)
  have hi:=actual_original_cf_inverses F z hz
  have hL:R*C=1:=hi.2
  have hR:C*R=1:=hi.1
  have hb:bracket Z R= -R*bracket Z (compressionCore F)*R:=by
    have he:bracket Z C=bracket Z (compressionCore F):=by
      dsimp only [C]
      simp only [bracket,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_one,one_mul]
      module
    exact (inverse_commutator Z C R hL hR).trans (by rw [he])
  have hCR:compressionCore F*R=1+z • R:=by
    change (compressionCore F-z • (1:End))*R=1 at hR
    simp only [sub_mul,smul_mul_assoc,one_mul] at hR
    linear_combination (norm:=module) hR
  have hRCR:R*compressionCore F*R=R+z • (R*R):=by
    calc
      R*compressionCore F*R=R*(compressionCore F*R):=rfl
      _=R*(1+z • R):=congrArg (fun T:End=>R*T) hCR
      _=R+z • (R*R):=by simp only [mul_add,mul_one,mul_smul_comm]
  rw [hb,actual_reverse_compression_scale]
  simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,neg_mul]
  rw [hRCR]
  module

/-- A fixed original source word may sit outside the resolvent, but its complete Z commutator must then be returned explicitly. -/
theorem actual_reverse_source_word_ward(F:Index)(z:ℂ)(hz:z.im≠0)(L:End)(f:QuantumTest):
    let R:End:=resolventCore F z hz
    Z (L (R f))+(18:ℂ) • L (R f+z • R (R f))=
      bracket Z L (R f)+L (R (Z f))-L (R (reverseCompressionForce F (R f))):=by
  dsimp only
  have h:=congrArg L (LinearMap.congr_fun (actual_reverse_resolvent_ward F z hz) f)
  simp only [bracket,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.neg_apply,
    Module.End.mul_apply,map_add,map_sub,map_smul,map_neg] at h ⊢
  linear_combination (norm:=module) h
end LowEnergy.ReverseNativeFrequencyWard
