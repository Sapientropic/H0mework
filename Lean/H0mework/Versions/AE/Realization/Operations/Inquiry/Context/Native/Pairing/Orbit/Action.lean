import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Pairing.Orbit.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Pairing.Orbit
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual
variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)
variable {S : Type u} {Value Var : S → Type u} [∀ sort,AddCommGroup (Value sort)] {slot : S}
variable (source : RawSource (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=slot) runtime)
theorem covariance : (paired runtime source).comp (wordAction (Value:=Value) (Var:=Var) (slot:=slot))=
 (statePullback (Value:=Value) (slot:=slot) runtime).comp (paired runtime source) := by
 apply LinearMap.ext
 intro word
 apply Finsupp.lhom_ext
 intro state coefficient
 have h := congrArg (fun value => coefficient • value) (point_covariance runtime source word state)
 change coefficient • paired runtime source (wordAction (Value:=Value) (Var:=Var) word) (Finsupp.single state 1)=
 coefficient • paired runtime source word (SourceOperationInquiry.sourceAction runtime (Finsupp.single state 1)) at h
 have single : Finsupp.single state coefficient=coefficient • Finsupp.single state (1:ℤ) := by
  rw [Finsupp.smul_single,smul_eq_mul,mul_one]
 change paired runtime source (wordAction (Value:=Value) (Var:=Var) word) (Finsupp.single state coefficient)=
  paired runtime source word (SourceOperationInquiry.sourceAction runtime (Finsupp.single state coefficient))
 rw [single,map_smul,map_smul,map_smul]
 exact h

def morphism : Morphism (paired runtime source) (paired runtime source) where
 sourceMap := wordAction
 targetMap := statePullback runtime
 commutes := (covariance runtime source).symm
abbrev Carrier := ResidualCarrier (paired runtime source)
def canonical := canonicalResidual (paired runtime source)
def action := inducedResidualMap (morphism runtime source)
theorem action_source (word : Words (Value:=Value) (Var:=Var) (slot:=slot)) :
 action runtime source (canonical runtime source word)=canonical runtime source (wordAction (Value:=Value) (Var:=Var) word) :=
 LinearMap.congr_fun (inducedResidualMap_comp_canonical (morphism runtime source)) word

def read (state : runtime.State) : Carrier runtime source →ₗ[ℤ] PairValue Value slot :=
 (LinearMap.applyₗ (R:=ℤ) (SourceOperationInquiry.point runtime state)).comp
 ((LinearMap.range (paired runtime source)).subtype.comp (residualEquivRange (paired runtime source)).toLinearMap)
theorem read_source (state : runtime.State) (word : Words (Value:=Value) (Var:=Var) (slot:=slot)) :
 read runtime source state (canonical runtime source word)=updateInventory (R:=ℤ) (old runtime source state)
 (increment runtime source state) word := point runtime source word state
theorem read_action_single (state : runtime.State) (expression : Expr Value (O.Var Var) slot) :
 read runtime source state (action runtime source (canonical runtime source (Finsupp.single expression (1:ℤ))))=
 ((expression.subst O.binding).eval (old runtime source state),
  (expression.subst O.binding).effect (old runtime source state) (increment runtime source state)) := by
 rw [action_source,read_source]
 apply Prod.ext
 · change evaluation (R:=ℤ) (old runtime source state) (wordAction (Finsupp.single expression (1:ℤ)))=_
   simp only [wordAction,substitution,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,
    evaluation,Finsupp.linearCombination_single,one_smul]
 · change effectEvaluator (R:=ℤ) (old runtime source state) (increment runtime source state)
    (wordAction (Finsupp.single expression (1:ℤ)))=_
   simp only [wordAction,substitution,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,
    effectEvaluator,Finsupp.linearCombination_single,one_smul]
end SourceOperationInquiry.Context.Native.Pairing.Orbit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
