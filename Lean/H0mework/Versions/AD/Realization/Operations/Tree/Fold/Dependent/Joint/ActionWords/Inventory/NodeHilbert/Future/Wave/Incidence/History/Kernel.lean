import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Response.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedLineageInventory
abbrev Word := Nat →₀ ℤ
abbrev shift : Word →ₗ[ℤ] Word := Finsupp.lmapDomain ℤ ℤ (fun stage => stage+1)
abbrev previous : Word →ₗ[ℤ] Word := Finsupp.lcomapDomain (fun stage => stage+1) (add_left_injective 1)
abbrev birth : Word →ₗ[ℤ] ℤ := Finsupp.lapply 0
theorem previous_shift (word : Word) : previous (shift word)=word :=
 Finsupp.leftInverse_lcomapDomain_mapDomain (fun stage => stage+1) (add_left_injective 1) word
theorem shift_previous (word : Word) : shift (previous word)=word.erase 0 := by
 exact Finsupp.mapDomain_comapDomain_nat_add_one word
theorem full_recovery (word : Word) : shift (previous word)+Finsupp.single 0 (birth word)=word := by
 rw [shift_previous]
 exact Finsupp.erase_add_single 0 word
def birthWord : ℤ →ₗ[ℤ] Word := Finsupp.lsingle 0
def split : Word →ₗ[ℤ] Word × ℤ := previous.prod birth
def join : Word × ℤ →ₗ[ℤ] Word := shift.comp (LinearMap.fst ℤ Word ℤ)+birthWord.comp (LinearMap.snd ℤ Word ℤ)
theorem join_split (word : Word) : join (split word)=word := full_recovery word
theorem split_join (value : Word × ℤ) : split (join value)=value := by
 simp only [split,join,LinearMap.prod_apply,LinearMap.add_apply,LinearMap.comp_apply,LinearMap.fst_apply,LinearMap.snd_apply]
 apply Prod.ext
 · change previous (shift value.1+Finsupp.single 0 value.2)=value.1
   rw [map_add,previous_shift]
   have fresh : previous (Finsupp.single 0 value.2)=0 := by
     ext stage
     simp [previous]
   rw [fresh,add_zero]
 · change ((shift value.1+Finsupp.single 0 value.2 : Word) 0)=value.2
   simp [shift,Finsupp.mapDomain_of_notMem_range]
def equivalence : Word ≃ₗ[ℤ] Word × ℤ := LinearEquiv.ofLinearMap split join
 (LinearMap.ext split_join) (LinearMap.ext join_split)
def history : Nat → Word
 | 0 => Finsupp.single 0 1
 | count+1 => Finsupp.single 0 1+shift (history count)
theorem history_inventory (count : Nat) : history count=∑ stage ∈ Finset.range (count+1),Finsupp.single stage (1:ℤ) := by
 induction count with
 | zero => simp [history]
 | succ count previous =>
   rw [history,previous,map_sum]
   simp only [shift,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
   conv_rhs => rw [Finset.sum_range_succ']
   exact add_comm _ _
theorem history_previous (count : Nat) : previous (history (count+1))=history count := by
 rw [history,map_add,previous_shift]
 have first : previous (Finsupp.single 0 1)=0 := by ext stage; simp [previous]
 rw [first,zero_add]
section Actual
open RootInquiryCompletion SourceOperationEffects
variable {S : Type u} {A X : S → Type u} [∀ s,AddCommGroup (A s)] {s : S}
variable (initial : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=A) (Var:=X) (sort:=s))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue:=A) (PhysicalVar:=X) (sort:=s))
theorem history_source (stage : Nat) : SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation.Lineage.embed initial configuration (history stage)=
 ∑ index ∈ Finset.range (stage+1),SourceOperationInquiry.point
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.runtime initial configuration)
   ((SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.runtime initial configuration).stateAt index) := by
 rw [history_inventory,map_sum]
 apply Finset.sum_congr rfl
 intro index _
 exact SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation.Lineage.embed_point initial configuration index
end Actual
end SourceGeneratedLineageInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
