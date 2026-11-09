import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Law
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Root.Adjoin
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Root.Sequential
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Frame

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Quantities.Execution (query next)
open Transport (NativeWork native_step_has_no_material_items sourceSupport)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Proposal" => Input Party Good Port Technology Instrument

theorem material_ready {cut : C} {input : Proposal} {community : Party → Community}
    (damage : Boundary.Actual.DamageAt cut input community) : ¬ NativeWork (query cut input) := by
  intro work
  have present := damage.source_item
  change damage.item ∈ Quantities.Execution.inventory cut [input] at present
  rw [native_step_has_no_material_items input work] at present
  exact List.not_mem_nil present

def nativeResident (cut : C) : Resident cut.native.frame.N where
  V := cut.native.full.V
  root := cut.native.full.root
  visit := cut.native.visit
  entry := cut.native.full.entry cut.native.visit.current
  authority := cut.native.authority
  unique := cut.native.full.occurrence_eq_emitted

theorem reindex_finite {N M : WorldRelationNetwork} (same : M = N) (s : M.Support)
    (finite : Finite (OpenResponsibilityAt M s)) :
    Finite (OpenResponsibilityAt N (same ▸ s)) := by cases same; exact finite

theorem reindex_support {N M : WorldRelationNetwork} (same : M = N) (s : M.Support) :
    HEq (same ▸ s : N.Support) s := by cases same; rfl

def materialFirst (cut : C) (input : Proposal) (ready : ¬ NativeWork (query cut input)) :
    First cut.native.frame.N :=
  let edge := History.originalEdge cut input (.inl ready)
  { before := sourceSupport cut.native
    after := edge.sameNetwork ▸ sourceSupport (next cut input).native
    whole := ⟨edge.whole, edge.keys⟩
    beforeFinite := cut.native.frame.entries_finite cut.native.visit.current
    afterFinite := reindex_finite edge.sameNetwork _ ((next cut input).native.frame.entries_finite
      (next cut input).native.visit.current)
    openFibres := cut.native.frame.family.open_fibres
    writes := edge.writes }

/-- Reuse the material first write selected by the original dispatcher. -/
def materialDraft (cut : C) (input : Proposal) (ready : ¬ NativeWork (query cut input)) :
    Draft cut.native.frame.N :=
  (materialFirst cut input ready).prepare (nativeResident cut) rfl

theorem material_draft_reaches_the_original_visit (cut : C) (input : Proposal)
    (ready : ¬ NativeWork (query cut input)) :
    HEq (materialDraft cut input ready).afterSupport (sourceSupport (next cut input).native) :=
  (heq_of_eq (materialFirst cut input ready).first_support).trans
    (reindex_support (History.originalEdge cut input (.inl ready)).sameNetwork _)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual
