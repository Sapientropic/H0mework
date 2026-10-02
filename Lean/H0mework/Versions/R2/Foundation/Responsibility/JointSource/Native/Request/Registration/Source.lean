import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Consumer
import H0mework.Versions.R2.Realization.Faces.ProjectionCoface

/-! Uniform raw data are a restriction of the existing complete registration.
The added before-emitter coface retains every original projection and the
actual general restructuring compiler. It does not identify arbitrary roots. -/

set_option autoImplicit false
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Request.Registration

open SourceOperationEffects

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}

structure UniformRaw where
  environment : Env Value Var
  expression : Expr Value Var sort

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V)
variable (program : Native.Program old.toLedgerRoot) {origin : V.Current}
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort) old.toLedgerRoot origin)

def uniform : UniformRaw (Value := Value) (Var := Var) (sort := sort) :=
  ⟨registered.input.environment, registered.input.expression⟩

def base := Native.Restructuring.authoritySource old program registered

def completeLaw : SourceNativeProjectionLaw (base old program registered).restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} _ _ => RawInputAt (Value := Value) (Var := Var) (sort := sort)
    old.toLedgerRoot origin (old.emitted origin)
  project := fun _ {_current} _ _ => registered.input

def completeSource := (base old program registered).withProjectionCoface (completeLaw old program registered)

def law : SourceNativeProjectionLaw (base old program registered).restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} _ _ => UniformRaw (Value := Value) (Var := Var) (sort := sort)
  project := fun _ {_current} _ _ => uniform old registered

def authoritySource : SourceNativeAuthoritySource (Native.World registered) (Native.JointV program registered) :=
  { (completeSource old program registered).withProjectionCoface (law old program registered) with
    observationAt := fun {_current} occurrence =>
      ⟨UniformRaw (Value := Value) (Var := Var) (sort := sort),
        (law old program registered).project PUnit.unit occurrence PUnit.unit⟩ }

theorem observation_generated {current : (Native.JointV program registered).Current}
    (occurrence : (base old program registered).restructuringSource.source.toRootSource.actual.OccurrenceAt current) :
    (authoritySource old program registered).observationAt occurrence =
      ⟨UniformRaw (Value := Value) (Var := Var) (sort := sort), uniform old registered⟩ := rfl

def rawInstallation : SourceNativeProjectionLaw.InstallationAt (law old program registered)
    (authoritySource old program registered).projectionLaw :=
  .componentCoface (completeSource old program registered) (law old program registered)

def completeInstallation : SourceNativeProjectionLaw.InstallationAt (completeLaw old program registered)
    (authoritySource old program registered).projectionLaw :=
  (SourceNativeProjectionLaw.InstallationAt.componentCoface
    (base old program registered) (completeLaw old program registered)).trans
    (.inheritedCoface (completeSource old program registered) (law old program registered))

def oldInstallation : SourceNativeProjectionLaw.InstallationAt
    (base old program registered).projectionLaw (authoritySource old program registered).projectionLaw :=
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (base old program registered) (completeLaw old program registered)).trans
    (.inheritedCoface (completeSource old program registered) (law old program registered))

theorem compiler_preserved : (authoritySource old program registered).restructuringSource.compiler =
    (base old program registered).restructuringSource.compiler := rfl

theorem raw_generated {current : (Native.JointV program registered).Current}
    (occurrence : (base old program registered).restructuringSource.source.toRootSource.actual.OccurrenceAt current) :
    (law old program registered).project PUnit.unit occurrence PUnit.unit = uniform old registered := rfl

theorem original_generated {current : (Native.JointV program registered).Current}
    (occurrence : (base old program registered).restructuringSource.source.toRootSource.actual.OccurrenceAt current)
    (projection : (base old program registered).projectionLaw.Projection) :
    HEq ((authoritySource old program registered).projectionLaw.outcomeAt
      ((oldInstallation old program registered).embed projection) occurrence)
      ((base old program registered).projectionLaw.outcomeAt projection occurrence) :=
  (oldInstallation old program registered).outcome_heq occurrence projection

end RootGeneratedDebtActivationJointSource.Native.Request.Registration
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
