import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.Born.CofinalQuery.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.BornInstalledJoint.WrittenCofinal
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open SourceGeneratedScalarDifferentialResidual
namespace Paid
export ActualNativeRelationTransport (paid)
end Paid
attribute [local irreducible] AS.localNativeReceipt

section NativeProjection
variable {W X : Unit→Type} [∀ target,AddCommGroup (W target)]
local instance nativeProjectionGroups (grade : Nat) : ∀ target,AddCommGroup (F.Value W grade target) := F.groups W grade

private def native_decoded_old
 (packet : AS.AdmissionPacket (W:=W) (X:=X) (s:=())) :
 Env (F.Value W (AS.bornAfterNative packet).1) X :=
 (Paid.paid (S.Complete.atReceipt (AS.stockCfg packet.2.2.1) packet.2.1.1 0)).environment

private def native_decoded_increment
 (packet : AS.AdmissionPacket (W:=W) (X:=X) (s:=())) :=
 (AS.bornAfterNative packet).2.1.1.activeEnvironment-native_decoded_old packet

private theorem native_decoded_residual
 (packet : AS.AdmissionPacket (W:=W) (X:=X) (s:=()))
 (word : Formal ℤ (F.Value W (AS.bornAfterNative packet).1) X ()) :
 (residualEquivRange (evaluation (R:=ℤ) (AS.bornAfterNative packet).2.1.1.activeEnvironment)
  (canonicalResidual (evaluation (R:=ℤ) (AS.bornAfterNative packet).2.1.1.activeEnvironment) word)).val=
 evaluation (R:=ℤ) (native_decoded_old packet) word+
  effectEvaluator (R:=ℤ) (native_decoded_old packet) (native_decoded_increment packet) word := by
 have actual : native_decoded_old packet+native_decoded_increment packet=
  (AS.bornAfterNative packet).2.1.1.activeEnvironment := by
  unfold native_decoded_increment
  abel
 rw [←actual]
 exact updated_residual_readout _ _ _

private theorem list_relation_sum
 {V : Type} [AddCommGroup V] [Module ℤ V] (closed : Submodule ℤ V) (words : List V)
 (present : ∀ word∈words,word∈closed) : words.sum∈closed := by
 induction words with
 | nil => exact closed.zero_mem
 | cons first rest previous =>
  exact closed.add_mem (present first List.mem_cons_self)
   (previous (fun word belongs=>present word (List.mem_cons_of_mem first belongs)))

private theorem complete_update_fibre
 (old increment : Env W X) (word candidate : Formal ℤ W X ()) :
 canonicalResidual (updateInventory (R:=ℤ) old increment) candidate=
  canonicalResidual (updateInventory (R:=ℤ) old increment) word ↔
 evaluation (R:=ℤ) old candidate=evaluation (R:=ℤ) old word ∧
 effectEvaluator (R:=ℤ) old increment candidate=effectEvaluator (R:=ℤ) old increment word := by
 have fibre:=canonicalResidual_eq_zero_iff (updateInventory (R:=ℤ) old increment) (candidate-word)
 simp only [map_sub,sub_eq_zero] at fibre
 exact fibre.trans (by
  change (evaluation (R:=ℤ) old candidate,effectEvaluator (R:=ℤ) old increment candidate)=
   (evaluation (R:=ℤ) old word,effectEvaluator (R:=ℤ) old increment word) ↔ _
  simp only [Prod.mk.injEq])
end NativeProjection

local instance decoderGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

/-- The complete boundary belongs to the actual next stock's generated relation span. -/
theorem actual_boundary_stock_closure :
 ∃ stock,(CA.site (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
  (D.firstCfg observation nontrivial half depth) rfl (ordinal+2)).2.1.1.inventory=some stock ∧
 queryBoundary observation nontrivial half depth ordinal∈Submodule.span ℤ
  {word | PresentedRelationEventAt.relation word∈stock.trace} := by
 obtain ⟨stock,present,relations⟩:=actual_query_stock observation nontrivial half depth ordinal
 refine ⟨stock,present,?_⟩
 rw [boundary_paid_sum]
 apply list_relation_sum
 intro word belongs
 obtain ⟨source,sourceMember,same⟩:=List.mem_map.mp belongs
 exact Submodule.subset_span (same ▸ relations source sourceMember)

def decodedOld := native_decoded_old (originalNative observation nontrivial half depth (ordinal+2))
def decodedIncrement := native_decoded_increment (originalNative observation nontrivial half depth (ordinal+2))

def decodedEffectCode := Coefficients.terms
 ((Coefficients.expression (decodedQueryWord observation nontrivial half depth ordinal)).mixedTerms.map
  (fun term=>(term,(1:ℤ))))
abbrev decodedEffectEnvironment := mixedEnvironment (decodedOld observation nontrivial half depth ordinal)
 (decodedIncrement observation nontrivial half depth ordinal)
abbrev decodedEffectValue := (decodedEffectCode observation nontrivial half depth ordinal).eval
 (decodedEffectEnvironment observation nontrivial half depth ordinal)
abbrev decodedEffectTrace := execution (decodedEffectEnvironment observation nontrivial half depth ordinal)
 (decodedEffectCode observation nontrivial half depth ordinal)

theorem actual_decoder_effect : decodedEffectValue observation nontrivial half depth ordinal=
 effectEvaluator (R:=ℤ) (decodedOld observation nontrivial half depth ordinal)
  (decodedIncrement observation nontrivial half depth ordinal) (decodedQueryWord observation nontrivial half depth ordinal) := by
 unfold decodedEffectValue decodedEffectCode
 rw [Coefficients.terms_eval]
 simp only [List.map_map,Function.comp_def,one_zsmul]
 exact ((Coefficients.expression (decodedQueryWord observation nontrivial half depth ordinal)).mixedTerms_sum _ _).trans
  (Coefficients.expression_effect _ _ _)

/-- Both decoder old/effect coordinates survive the existing coimage. -/
theorem actual_decoder_inventory_inverse :
 (residualEquivRange
  (updateInventory (R:=ℤ) (decodedOld observation nontrivial half depth ordinal)
   (decodedIncrement observation nontrivial half depth ordinal))
  (canonicalResidual
   (updateInventory (R:=ℤ) (decodedOld observation nontrivial half depth ordinal)
    (decodedIncrement observation nontrivial half depth ordinal))
   (decodedQueryWord observation nontrivial half depth ordinal))).val=
 (evaluation (R:=ℤ) (decodedOld observation nontrivial half depth ordinal)
   (decodedQueryWord observation nontrivial half depth ordinal),decodedEffectValue observation nontrivial half depth ordinal) := by
 rw [actual_decoder_effect]
 rfl

/-- Every representative of the complete acted decoder fibre is retained. -/
theorem actual_decoder_inventory_fibre
 (candidate : type_of% (decodedQueryWord observation nontrivial half depth ordinal)) :
 canonicalResidual (updateInventory (R:=ℤ) (decodedOld observation nontrivial half depth ordinal)
  (decodedIncrement observation nontrivial half depth ordinal)) candidate=
 canonicalResidual (updateInventory (R:=ℤ) (decodedOld observation nontrivial half depth ordinal)
  (decodedIncrement observation nontrivial half depth ordinal))
  (decodedQueryWord observation nontrivial half depth ordinal) ↔
 evaluation (R:=ℤ) (decodedOld observation nontrivial half depth ordinal) candidate=
  evaluation (R:=ℤ) (decodedOld observation nontrivial half depth ordinal)
   (decodedQueryWord observation nontrivial half depth ordinal) ∧
 effectEvaluator (R:=ℤ) (decodedOld observation nontrivial half depth ordinal)
  (decodedIncrement observation nontrivial half depth ordinal) candidate=decodedEffectValue observation nontrivial half depth ordinal := by
 rw [actual_decoder_effect]
 exact complete_update_fibre _ _ _ _

/-- The same post-decoder residual is computed by its actual complete old value and mixed effect AST. -/
theorem actual_decoder_updated_residual :
 (residualEquivRange
  (evaluation (R:=ℤ) (writerBorn observation nontrivial half depth (ordinal+2)).activeEnvironment)
  (canonicalResidual
   (evaluation (R:=ℤ) (writerBorn observation nontrivial half depth (ordinal+2)).activeEnvironment)
   (decodedQueryWord observation nontrivial half depth ordinal))).val=
 evaluation (R:=ℤ) (decodedOld observation nontrivial half depth ordinal)
  (decodedQueryWord observation nontrivial half depth ordinal)+decodedEffectValue observation nontrivial half depth ordinal := by
 rw [actual_decoder_effect]
 exact native_decoded_residual (originalNative observation nontrivial half depth (ordinal+2))
  (decodedQueryWord observation nontrivial half depth ordinal)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.BornInstalledJoint.WrittenCofinal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
