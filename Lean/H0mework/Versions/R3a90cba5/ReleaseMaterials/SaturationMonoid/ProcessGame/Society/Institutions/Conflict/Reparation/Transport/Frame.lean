import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Write

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Accounting.Root
open Capitalism.Universal.Root.Financial.Installation
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "Native" => Evolving.NativeCurrent (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

abbrev sourceSupport (native : Native) := native.frame.sourceSupport native.visit.current

abbrev structuralTarget (native : Native) :=
  native.frame.sourceSupport (native.frame.successor native.visit.current).targetCurrent

variable {law : DebtActivationLaw} {joint : WorldRelationNetwork}
  (native : Evolving.NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (shape : Shape law native.frame.N joint) (phase : law.DebtState)

def heldWrite (wait : law.TransportAt phase phase) (current : native.frame.V.Current) :
    Whole joint (shape.support (native.frame.sourceSupport current) phase)
      (shape.support (native.frame.sourceSupport (native.frame.successor current).targetCurrent) phase) :=
  let original := History.nativeWrite (input := native.input) native.frame current
  let owner := native.frame.entry current
  ⟨shape.lift (.inr wait) original.val owner, shape.lift_keeps_keys _ _ _ original.property⟩

/-- An initial whole write followed by the literal structural successors
of its original native target. The initial support belongs to that write. -/
structure Frame where
  initialSupport : joint.Support
  initialFinite : Finite (OpenResponsibilityAt joint initialSupport)
  initialWrite : Whole joint initialSupport (shape.support (native.frame.sourceSupport native.visit.current) phase)
  writes : Bool

namespace Frame

variable {native shape phase} (frame : Frame (native := native) shape phase)

abbrev Cursor (_frame : Frame native shape phase) := Option native.frame.V.Current

def support : Cursor frame → joint.Support
  | none => frame.initialSupport
  | some current => shape.support (native.frame.sourceSupport current) phase

def next : Cursor frame → Cursor frame
  | none => some native.visit.current
  | some current => some (native.frame.successor current).targetCurrent

def whole (wait : law.TransportAt phase phase) :
    (current : Cursor frame) → Whole joint (frame.support current) (frame.support (frame.next current))
  | none => frame.initialWrite
  | some current => heldWrite native shape phase wait current

def flow (wait : law.TransportAt phase phase) : Compiler.Flow joint where
  Current := Cursor frame
  initial := none
  support := frame.support
  next := frame.next
  writes := fun current => match current with
    | none => frame.writes
    | some original => History.hasWrite (input := native.input) native.frame original
  evolution := fun current => (frame.whole wait current).val
  finite := fun current => match current with
    | none => frame.initialFinite
    | some original => shape.finiteRows _ _ (native.frame.entries_finite original)
  injective := fun current =>
    let keys := (frame.whole wait current).property
    let fibres := shape.openFibres native.frame.family.open_fibres
    ⟨keys_imply_origin_injective _ keys fibres, keys_imply_destination_injective _ keys fibres⟩
  open_fibres := shape.openFibres native.frame.family.open_fibres

end Frame

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport
