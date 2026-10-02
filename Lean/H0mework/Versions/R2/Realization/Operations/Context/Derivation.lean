import H0mework.Versions.R2.Realization.Operations.Context.Expression
import H0mework.Realization.Operations.DerivationReduction

/-! Original derivation constructors enter the complete native context without replacing their proof trees. -/

set_option autoImplicit false

universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Context

open SourceOperationEffects SourceOperationDerivations

noncomputable section

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ sort, AddCommGroup (PhysicalValue sort)]

def embedDerivation (readEnv : process.State → Env PhysicalValue PhysicalVar)
    (runtime : LivingRuntimeState process) {s : Sorts} {left right : Expr PhysicalValue PhysicalVar s}
    (proof : Derivation (readEnv runtime.state) left right) :
    Derivation (environment (point runtime)) (embed readEnv left) (embed readEnv right) := by
  induction proof with
  | refl expression => exact .refl (embed readEnv expression)
  | symm proof ih => exact .symm ih
  | trans first second ihFirst ihSecond => exact .trans ihFirst ihSecond
  | @bind source name =>
      have generated := Derivation.normalize (environment (point runtime)) (embed readEnv (.var name))
      have actualRead : (embed readEnv (.var name)).eval (environment (point runtime)) =
          readEnv runtime.state source name :=
        observer_point (fun state => readEnv state source name) runtime
      rw [actualRead] at generated
      exact generated
  | @addConst source left right =>
      simpa only [embed] using Derivation.addConst (ρ := environment (point runtime))
        (s := Sum.inl source) left right
  | @linearConst source target operation value =>
      simpa only [embed] using Derivation.linearConst (ρ := environment (point runtime))
        (s := Sum.inl source) (t := Sum.inl target) operation value
  | @bilinearConst source target result operation left right =>
      simpa only [embed] using Derivation.bilinearConst (ρ := environment (point runtime))
        (s := Sum.inl source) (t := Sum.inl target) (r := Sum.inl result) operation left right
  | addCongr first second ihFirst ihSecond => exact .addCongr ihFirst ihSecond
  | @linearCongr source target operation left right proof ih =>
      simpa only [embed] using Derivation.linearCongr (s := Sum.inl source) (t := Sum.inl target) operation ih
  | @bilinearCongr source target result operation left left' right right' first second ihFirst ihSecond =>
      simpa only [embed] using Derivation.bilinearCongr
        (s := Sum.inl source) (t := Sum.inl target) (r := Sum.inl result) operation ihFirst ihSecond

end
end SourceOperationNative.Context
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
