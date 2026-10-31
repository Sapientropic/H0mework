import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Schedule
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.Archives

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Deployment

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument} {depth count : Nat}
  {oldReader : Macro.Raw.Reader input depth count}
  (source : Position input depth count oldReader)

def before := source.actual.actual.account
def history := source.past
def plan := Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.word input depth count (before source)
def reader := Clearing.reader (history source).length (plan source) oldReader

/-- Extend the original current's installed frame. Old query cofaces, the
source occurrence, account, paid rows and authority are inherited literally. -/
def position : Position input depth count (reader source) where
  start := source.start
  frame := source.native.full
  visit := source.visit
  actual := source.native.sourceActual
  paid := source.paid
  authority := source.authority.withProjectionCoface (Public.Inquiry.component source.native.full (reader source))
  rows := source.rows
  ready := source.ready

theorem the_source_installer_extends_the_same_current_root :
    (position source).frame.root = source.native.full.root := rfl

theorem the_source_installer_keeps_the_same_original_native_account :
    (position source).actual.actual.account = (before source) := rfl

theorem the_source_installer_keeps_the_same_actual_past : (position source).past = (history source) := rfl

def schedule (resources : Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ArchiveNative.Conditions
    input depth count (history source) (before source)) :
    Schedule input depth count (history source).length (plan source) oldReader (plan source) where
  position := (position source)
  front := []
  split := rfl
  location := rfl
  noConsents := Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ArchiveNative.every_actual_request_uses_its_original_debtor_without_extra_consent
    input depth count (before source)
  index := 0
  valid := Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ArchiveNative.primitive_source_resources_generate_all_actual_items
    input depth count (history source) (before source) resources

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Deployment
