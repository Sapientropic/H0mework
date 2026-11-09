import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Occurrence
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Root.First
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public.Result

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

/-- The literal material emission on the original root after an interpreter
change. The physical compiler supplies its items and the next stock. -/
structure PostedMaterial (Party Good Port Technology Instrument : Type) where
  ordinal : Nat
  programme : ProgrammeSource.Input Party Good Port Technology Instrument
  before : Capitalism.Universal.Abolition.Root.Actual.Current (Party := Party) (Good := Good)
    (Port := Port) (Technology := Technology) (Instrument := Instrument)
  command : Compile.RawInput Party Good Port Technology Instrument
  deliveryReplies : Party → Bool

namespace PostedMaterial

noncomputable def effect (read : PostedMaterial Party Good Port Technology Instrument) :=
  Physical.Public.compile read.programme read.before read.command

def IsWritten (read : PostedMaterial Party Good Port Technology Instrument) : Prop :=
  ∃ (world : WorldRelationNetwork) (resident : Resident world)
    (face : SourceNativeRootSemanticFaceAt resident.root resident.visit)
    (typed : face.Restriction = PostedMaterial Party Good Port Technology Instrument),
    cast typed face.rootRead = read

end PostedMaterial

/-- A position after the native prefix still belongs to that prefix's
original occurrence. Its stock and interpreter are read from the real write. -/
structure PostedPosition (seed : Root.Cut Party Good Port Technology Instrument) where
  private mk ::
  anchor : Script Party Good Port Technology Instrument
  material : PostedMaterial Party Good Port Technology Instrument
  ordered : anchor.length ≤ material.ordinal
  written : material.IsWritten
  accepted : material.effect.isAccepted = true
  position : Fin material.effect.execution.items.length

namespace PostedPosition

variable {seed : Root.Cut Party Good Port Technology Instrument}
    (site : PostedPosition seed)

noncomputable abbrev item :=
  site.material.effect.execution.items[site.position]

def address : Nat × Nat := (site.material.ordinal, site.position.val)

end PostedPosition

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual
