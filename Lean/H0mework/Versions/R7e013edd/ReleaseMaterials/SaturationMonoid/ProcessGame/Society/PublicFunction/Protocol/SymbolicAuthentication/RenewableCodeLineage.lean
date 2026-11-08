import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableArchiveConsumer
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AncestralReceptionSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableCodeLineage
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
abbrev Emitter := Code Party Good Port (Mandate.State Party Technology) Instrument

structure Lineage (root current : Emitter (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) where
 private mk ::
 catalogue : CatalogueHandoffSource.Catalogue root
 same : current=CatalogueHandoffSource.code root catalogue

variable {root current : Emitter (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)}

def empty (root : Emitter (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) : CatalogueHandoffSource.Catalogue root := ⟨[],0,[],0,[]⟩
omit [DecidableEq Port] [DecidableEq Technology] in
theorem empty_code : CatalogueHandoffSource.code root (empty root)=root := by
 simp only [empty,CatalogueHandoffSource.code,Extension.code,
  List.append_nil,Nat.max_zero]

-- Only actual catalogue extensions enter the lineage. No signature/body is transported.
private def extendFlat
 (earlier : {catalogue : CatalogueHandoffSource.Catalogue root // current=CatalogueHandoffSource.code root catalogue})
 (addition : CatalogueHandoffSource.Catalogue current) :
 {catalogue : CatalogueHandoffSource.Catalogue root //
  CatalogueHandoffSource.code current addition=CatalogueHandoffSource.code root catalogue} := by
 obtain ⟨catalogue,same⟩ := earlier
 subst current
 exact ⟨AncestralReceptionSource.join root catalogue addition,
  AncestralReceptionSource.joined_code_is_the_same_actual_extension root catalogue addition⟩

def Lineage.original : Lineage root root := ⟨empty root,empty_code.symm⟩

def Lineage.extended (prior : Lineage root current) (addition : CatalogueHandoffSource.Catalogue current) :
 Lineage root (CatalogueHandoffSource.code current addition) :=
 let joined := extendFlat ⟨prior.catalogue,prior.same⟩ addition
 ⟨joined.val,joined.property⟩

def flatten (lineage : Lineage root current) :
 {catalogue : CatalogueHandoffSource.Catalogue root // current=CatalogueHandoffSource.code root catalogue} :=
 ⟨lineage.catalogue,lineage.same⟩

def recodeRow {other : Emitter (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)}
 (same : current=other) (row : StageTrace.Record (code := current)) : StageTrace.Record (code := other) := same ▸ row

theorem recodeRow_keeps_the_entire_actual_payload
 {other : Emitter (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)}
 (same : current=other) (row : StageTrace.Record (code := current)) :
 (recodeRow same row).cursor.source.input=row.cursor.source.input ∧
 (recodeRow same row).cursor.cut=row.cursor.cut ∧
 (recodeRow same row).submitted=row.submitted ∧
 HEq (recodeRow same row).before row.before ∧ HEq (recodeRow same row).after row.after := by
 cases same
 exact ⟨rfl,rfl,rfl,HEq.rfl,HEq.rfl⟩

omit [DecidableEq Port] [DecidableEq Technology] in
theorem recodeRow_items {other : Emitter (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)}
 (same : current=other) (row : StageTrace.Record (code := current)) :
 StageTrace.items (recodeRow same row)=StageTrace.items row := by cases same;rfl

structure Row (root : Emitter (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) where
 private mk ::
 code : Emitter (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
 lineage : Lineage root code
 actual : StageTrace.Record (code := code)

def pack (lineage : Lineage root current) (row : StageTrace.Record (code := current)) : Row root :=
 ⟨current,lineage,row⟩
def Row.catalogue (row : Row root) := (flatten row.lineage).val
def Row.material (row : Row root) := recodeRow (flatten row.lineage).property row.actual

variable (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (begin : RenewableArchiveSource.State (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (control : RenewableArchiveSource.State (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument) → RenewableArchiveSource.Command)

abbrev currentAt (count : Nat) := RenewableArchiveSource.run contract begin control count

def lineageAt : (count : Nat) → Lineage begin.model.source.code (currentAt contract begin control count).model.source.code :=
 Nat.rec Lineage.original fun count prior =>
  match chosen : control (currentAt contract begin control count) with
  | .execute inputs => by
    change Lineage _ (RenewableArchiveSource.next contract (currentAt contract begin control count)
     (control (currentAt contract begin control count))).model.source.code
    rw [chosen]
    exact prior
  | .renew enabled accept => by
    change Lineage _ (RenewableArchiveSource.next contract (currentAt contract begin control count)
     (control (currentAt contract begin control count))).model.source.code
    rw [chosen]
    exact .extended prior
     (PaidInvocationSource.catalogue (currentAt contract begin control count).model.source.code contract)

def commandRows (count : Nat) : List (Row begin.model.source.code) :=
 let state := currentAt contract begin control count
 match control state with
 | .execute inputs =>
   ((RenewableArchiveSource.fresh state inputs).rows state.model).map (pack (lineageAt contract begin control count))
 | .renew enabled accept =>
   (StageTrace.records (PaidInvocationSource.start state.model.source.code contract state.point)
    (PaidInvocationSource.stages state.model.source.code contract enabled accept)).map
    (pack (.extended (lineageAt contract begin control count)
     (PaidInvocationSource.catalogue state.model.source.code contract)))

def history : Nat → List (Row begin.model.source.code) :=
 Nat.rec [] fun count prior => prior++commandRows contract begin control count

theorem every_control_step_keeps_the_complete_actual_row_prefix (count : Nat) :
 history contract begin control count <+: history contract begin control (count+1) := List.prefix_append _ _

theorem every_actual_payment_attempt_is_two_original_rows
 (count : Nat) (enabled accept : Bool)
 (chosen : control (currentAt contract begin control count)=.renew enabled accept) :
 commandRows contract begin control count=
  (StageTrace.records (PaidInvocationSource.start (currentAt contract begin control count).model.source.code contract
    (currentAt contract begin control count).point)
   (PaidInvocationSource.stages (currentAt contract begin control count).model.source.code contract enabled accept)).map
   (pack (.extended (lineageAt contract begin control count)
    (PaidInvocationSource.catalogue (currentAt contract begin control count).model.source.code contract))) := by
 simp only [commandRows,chosen]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableCodeLineage
