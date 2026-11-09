import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Pricing.Payment
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Consumers.OriginalReview

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Pricing.Original

open Capitalism.Universal.Source.Program

noncomputable section

private abbrev base := OriginalReview.initial
private abbrev RequestAt := Request Bool Bool Bool Unit Unit

private def filing : RequestAt := reviewRequest true false [(true, 1/4)]
private def examination : RequestAt := reviewRequest true false [(true, 1/2)]

private def measured (request : RequestAt)
    (own : workAdmissible base.programme.law true ⟨0, base.physical.raw, request⟩) :
    MeteredWork base.programme.law base.physical.raw true :=
  ⟨[request], fun _ listed => (List.mem_singleton.mp listed).symm ▸ own⟩

private theorem filing_paid : workAdmissible base.programme.law true ⟨0, base.physical.raw, filing⟩ := by
  change workAdmissible OriginalRecipe.programme.law true ⟨0, Settlement.settledCut.raw, filing⟩
  rw [Settlement.settled_raw]
  decide +kernel

private theorem examination_paid :
    workAdmissible base.programme.law true ⟨0, base.physical.raw, examination⟩ := by
  change workAdmissible OriginalRecipe.programme.law true ⟨0, Settlement.settledCut.raw, examination⟩
  rw [Settlement.settled_raw]
  decide +kernel

def desk : Desk base.programme.law base.physical.raw true :=
  ⟨false, measured filing filing_paid, fun _ => measured examination examination_paid⟩

private theorem filingDraw : base.programme.law.actualDebit base.physical.raw filing = locate true [(true,1/4)] := by
  change OriginalRecipe.programme.law.actualDebit Settlement.settledCut.raw filing = _
  rw [Settlement.settled_raw]
  decide +kernel

private theorem examinationDraw :
    base.programme.law.actualDebit base.physical.raw examination = locate true [(true,1/2)] := by
  change OriginalRecipe.programme.law.actualDebit Settlement.settledCut.raw examination = _
  rw [Settlement.settled_raw]
  decide +kernel

theorem filing_bundle : desk.filing.bundle = [(true,1/4)] := by
  unfold MeteredWork.bundle
  change (([⟨0, base.physical.raw, filing⟩] : List (ExecutionItem Bool Bool Bool Unit Unit)).flatMap
    fun item => (base.programme.law.actualDebit item.before item.request).map (fun lot => (lot.1.2, lot.2))) = _
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [show base.programme.law.actualDebit base.physical.raw filing = _ from filingDraw]
  rfl

theorem examination_bundle (request : RequestAt) : (desk.review request).bundle = [(true,1/2)] := by
  unfold MeteredWork.bundle
  change (([⟨0, base.physical.raw, examination⟩] : List (ExecutionItem Bool Bool Bool Unit Unit)).flatMap
    fun item => (base.programme.law.actualDebit item.before item.request).map (fun lot => (lot.1.2, lot.2))) = _
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [show base.programme.law.actualDebit base.physical.raw examination = _ from examinationDraw]
  rfl

theorem the_original_filing_has_real_cost : desk.filingCheck = true := by
  apply desk.filingCheck_iff.mpr
  exact ⟨true, by rw [filing_bundle]; decide +kernel⟩

def quote := desk.tariff the_original_filing_has_real_cost

theorem one_original_request_costs_three_quarters (request : RequestAt) :
    (quote.parts [request]).bundle = [(true,1/4), (true,1/2)] := by
  simp only [quote, Tariff.parts, Desk.tariff, ChargeParts.bundle, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, filing_bundle, examination_bundle]
  rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Pricing.Original
