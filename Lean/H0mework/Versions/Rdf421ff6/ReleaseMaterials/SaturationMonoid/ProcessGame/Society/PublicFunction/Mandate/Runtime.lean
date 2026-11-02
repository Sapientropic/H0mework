import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.NativeRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Source.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Institutions.Capitalism.Universal.Root

def bound : BoundSource base scope := ⟨source, rfl⟩

abbrev previousRoot := NativeRuntime.previousRoot bound
abbrev previousFacade := NativeRuntime.previousFacade bound
abbrev projectionLaw := NativeRuntime.projectionLaw bound
abbrev root := NativeRuntime.root bound
abbrev stateAt := NativeRuntime.stateAt bound
abbrev process := NativeRuntime.process bound
abbrev Face := NativeRuntime.Face bound
abbrev facade := NativeRuntime.facade bound
abbrev activated := NativeRuntime.activated bound

theorem original_root_is_preserved :
    root.toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot source.input).toAuthoritativeRoot.toRoot := rfl

theorem activated_state (ordinal : Nat) : (activated ordinal).state = ordinal :=
  NativeRuntime.activated_state bound ordinal

theorem mandate_payload_is_actual (depth : Nat) :
    projectionLaw.project ()
      (ProgrammeSource.emitted source.input (ProgrammeHistory.visitAt source.input (depth + 1)).current)
      () depth rfl = (actualGrants depth).map (admitGrant base scope _ _) := rfl

theorem actual_grant_in_payload : admitGrant base scope _ _ grant ∈ projectionLaw.project ()
    (ProgrammeSource.emitted source.input (ProgrammeHistory.visitAt source.input 2).current) () 1 rfl := by
  exact List.mem_map.mpr ⟨grant, List.get_mem _ _, rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Source.Runtime
