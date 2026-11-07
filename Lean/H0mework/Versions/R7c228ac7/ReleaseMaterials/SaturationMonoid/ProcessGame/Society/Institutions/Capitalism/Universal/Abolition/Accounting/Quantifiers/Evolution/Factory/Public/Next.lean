import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public.Target

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument : Type} {N : WorldRelationNetwork}
  (current : Context (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) N)

def nextBasic : Context (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) N where
  V := V current
  root := targetRoot current
  visit := (generated current).target.targetVisit
  row := (generated current).target.targetEntry
  authority := (generated current).target.targetAuthority
  basis := current.basis
  raw := current.raw
  rawFace := {
    projection := oldProjection current current.rawFace.projection
    active := current.rawFace.active,classifier_eq := current.rawFace.classifier_eq }
  raw_heq := current.raw_heq
  actualLaw := law current
  members := Context.readMembers current
  contextFace := activeFace current (generated current).target.targetVisit
  context_heq := by
    change HEq (effectiveAt current (Sparse.Compiler.successor (code current) false).targetCurrent)
      (law current,Context.readMembers current)
    have phase : (Sparse.Compiler.successor (code current) false).targetCurrent = true :=
      Sparse.Compiler.successor_current (code current) false
    have effective := congrArg (effectiveAt current) phase
    exact heq_of_eq effective

theorem nextBasic_reads_the_enacted_public_law :
    Context.readLaw (nextBasic current) = law current := Context.readLaw_eq _

theorem nextBasic_retains_the_original_actual_raw :
    Context.readRaw (nextBasic current) = Context.readRaw current :=
  (Context.readRaw_eq _).trans (Context.readRaw_eq _).symm

theorem nextBasic_retains_the_entire_original_world_support :
    Context.support (nextBasic current) = Context.support current := rfl

theorem nextBasic_is_the_actual_canonical_root_next :
    (⟨N,(generated current).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) =
      Context.erase (nextBasic current) :=
  congrArg (fun next => (⟨N,next⟩ : AnyAuthoritativeRootCurrent))
    (generated current).target.targetAnswerAndNext_next_eq

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public
