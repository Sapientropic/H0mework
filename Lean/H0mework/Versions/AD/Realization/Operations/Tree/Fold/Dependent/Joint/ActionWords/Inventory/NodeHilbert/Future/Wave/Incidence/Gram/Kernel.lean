import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Lineage.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedHilbertGramProgramme
open SourceOperationEffects SourceOperationExecution
variable {W H : Type u} [AddCommGroup W] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (read : W →ₗ[ℤ] H)
def gram : H →+ H →+ ULift.{u} ℂ where
 toFun := fun left => {
   toFun := fun right => ULift.up (inner ℂ left right)
   map_zero' := congrArg ULift.up (inner_zero_right left)
   map_add' := by intro first second; exact congrArg ULift.up (inner_add_right left first second) }
 map_zero' := by ext right; exact inner_zero_left right
 map_add' := by intro left right; ext test; exact inner_add_left left right test
inductive Slot : Type u | word | hilbert | scalar
abbrev Value : Slot → Type u | .word => W | .hilbert => H | .scalar => ULift.{u} ℂ
abbrev Var : Slot.{u} → Type u := fun _ => PUnit.{u+1}
instance : (slot : Slot) → AddCommGroup (Value.{u,u} (W:=W) (H:=H) slot)
 | .word => inferInstance
 | .hilbert => inferInstance
 | .scalar => inferInstance
def environment (word : W) : Env (Value.{u,u} (W:=W) (H:=H)) Var.{u}
 | .word,_ => word | .hilbert,_ => read word | .scalar,_ => 0
def programme : Expr (Value.{u,u} (W:=W) (H:=H)) Var.{u} Slot.scalar.{u} :=
 .bilinear (s:=Slot.hilbert) (t:=Slot.hilbert) (gram (H:=H))
   (.linear (s:=Slot.word) read.toAddMonoidHom (.var PUnit.unit))
   (.linear (s:=Slot.word) read.toAddMonoidHom (.var PUnit.unit))
def increment (before after : W) := environment read after-environment read before
theorem value (word : W) : ((programme read).eval (environment read word)).down=inner ℂ (read word) (read word) := rfl
theorem effect (before after : W) :
 ((programme read).effect (environment read before) (increment read before after)).down=
 inner ℂ (read before) (read after-read before)+
 inner ℂ (read after-read before) (read before)+
 inner ℂ (read after-read before) (read after-read before) := by
 change inner ℂ (read before) (read (after-before))+
   inner ℂ (read (after-before)) (read before)+inner ℂ (read (after-before)) (read (after-before))=_
 rw [map_sub]
theorem update (before after : W) :
 (programme read).eval (environment read after)=(programme read).eval (environment read before)+
   (programme read).effect (environment read before) (increment read before after) := by
 have actual := Expr.eval_update (programme read) (environment read before) (increment read before after)
 rw [increment,add_sub_cancel] at actual
 exact actual
theorem budget : remaining (programme read)=5 := rfl
theorem energy (before after : W) : ‖read after‖^2=
    ‖read before‖^2+2*(inner ℂ (read before) (read after-read before)).re+‖read after-read before‖^2 := by
 have full : read after=read before+(read after-read before) := (add_sub_cancel _ _).symm
 exact (congrArg (fun value : H => ‖value‖^2) full).trans (norm_add_sq (𝕜:=ℂ) (read before) (read after-read before))
end SourceGeneratedHilbertGramProgramme
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
