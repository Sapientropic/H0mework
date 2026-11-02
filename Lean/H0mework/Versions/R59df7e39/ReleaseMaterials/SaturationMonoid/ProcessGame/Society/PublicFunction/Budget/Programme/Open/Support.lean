import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Support

open Successor
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (fallback : Rule model.source.code)

def requests (domain : List (Cursor model.source.code)) (program : Program model.source.code) :=
  (List.range (Whole.Complete.horizon domain)).flatMap fun ordinal =>
    match (stage model.source.code fallback program ordinal).work with
    | none => []
    | some policy => model.source.code.keys.attach.flatMap fun key => policy key.val key.property

def SourceSupported (domain : List (Cursor model.source.code)) (program : Program model.source.code) : Prop :=
  ∀ request ∈ requests model fallback domain program, request ∈ model.source.code.actions

instance (domain : List (Cursor model.source.code)) (program : Program model.source.code) :
    Decidable (SourceSupported model fallback domain program) := by unfold SourceSupported;infer_instance

theorem support_exact (domain : List (Cursor model.source.code)) (program : Program model.source.code) :
    SourceSupported model fallback domain program ↔ Open.Supported model domain fallback program := by
  constructor
  · intro supported ordinal bounded policy chosen key inside request present
    apply supported request
    apply List.mem_flatMap.mpr
    refine ⟨ordinal,List.mem_range.mpr bounded,?_⟩
    rw [chosen]
    exact List.mem_flatMap.mpr ⟨⟨key,inside⟩,List.mem_attach _ _,present⟩
  · intro supported request present
    obtain ⟨ordinal,bounded,present⟩ := List.mem_flatMap.mp present
    cases chosen : (stage model.source.code fallback program ordinal).work with
    | none => simp only [chosen,List.not_mem_nil] at present
    | some policy =>
      rw [chosen] at present
      obtain ⟨key,_,present⟩ := List.mem_flatMap.mp present
      exact supported ordinal (List.mem_range.mp bounded) policy chosen key.val key.property request present

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Support
