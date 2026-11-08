import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Aggression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Conservation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Source
open Capacity Space

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "Law" => RawLaw Party Good Port Technology Instrument
local notation "Origin" => ProgrammeFace.Origin Party Good Port Technology Instrument
local notation "Debit" => Row Party Good Port Technology Instrument

omit [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Community] in
theorem positive_loss_requires_the_original_debit (law : Law) (row : Debit)
    (valid : law.Valid row.1.before row.1.request) (positive : 0 < loss law row) :
    row.2 ∈ (law.actualDebit row.1.before row.1.request).map Prod.fst := by
  by_contra absent
  have zero : flowAt (law.actualDebit row.1.before row.1.request) row.2.1 row.2.2 = 0 := by
    apply amount_zero_of_absent
    intro entry present same
    exact absent (List.mem_map.mpr ⟨entry, present, same⟩)
  have credit : 0 ≤ flowAt (law.actualCredit row.1.before row.1.request) row.2.1 row.2.2 := by
    rw [RawLaw.actualCredit, if_pos valid]
    exact amount_nonnegative _ valid.2.2.2.2.1 _
  change 0 < flowAt (law.actualDebit row.1.before row.1.request) row.2.1 row.2.2 -
    flowAt (law.actualCredit row.1.before row.1.request) row.2.1 row.2.2 at positive
  linarith

/-- Every original positive foreign loss is in the generated M11 inventory. -/
theorem boundary_from_original_row (law : Law) (origin : Origin) (community : Party → Community)
    (row : Debit) (original : row.1 ∈ law.rawItems origin.1 origin.2)
    (valid : law.Valid row.1.before row.1.request)
    (debited : row.2 ∈ (law.actualDebit row.1.before row.1.request).map Prod.fst)
    (positive : 0 < loss law row)
    (foreign : community row.1.request.signer ≠ community row.2.1) :
    ∃ boundary ∈ (sourceCrossings law origin community).boundaryCertificates,
      debitAt law origin boundary.crossing = row := by
  let action : ProgrammeFace.ActionSeed Party := ⟨row.1.index, .execution, row.1.request.signer⟩
  let point : ProgrammeFace.Point Party Good Port Technology Instrument := .action action
  have actionMember : action ∈ ProgrammeFace.actions law origin := by
    apply List.mem_flatMap.mpr
    exact ⟨row.1, original, by simp [ProgrammeFace.itemActions, valid, action]⟩
  have pointMember : point ∈ (originalGame law origin).occurrence.trace := by
    change point ∈ (ProgrammeFace.trace law origin).trace
    rw [ProgrammeFace.trace_exact]
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨action, actionMember, rfl⟩
  have rowMember : row ∈ rowsAt law origin point := by
    apply List.mem_flatMap.mpr
    refine ⟨row.1, ?_, ?_⟩
    · change row.1 ∈ (law.rawItems origin.1 origin.2).filter (fun item => decide
        (item.index = row.1.index ∧ item.request.signer = row.1.request.signer ∧ law.Valid item.before item.request))
      exact List.mem_filter.mpr ⟨original, decide_eq_true ⟨rfl, rfl, valid⟩⟩
    · exact List.mem_map.mpr ⟨row.2, List.mem_filter.mpr ⟨List.mem_dedup.mpr debited, decide_eq_true positive⟩, rfl⟩
  obtain ⟨position, exactPoint⟩ := List.mem_iff_get.mp pointMember
  have positioned : row ∈ rowsAt law origin (stateAt (originalGame law origin) position) := by
    change (originalGame law origin).occurrence.trace.get position = point at exactPoint
    rw [stateAt, exactPoint]
    exact rowMember
  obtain ⟨unit, exactRow⟩ := List.mem_iff_get.mp positioned
  let crossing := (debitRate law origin).exactQueueUnitOf position unit
  have rowEq : debitAt law origin crossing = row := exactRow
  have other : community (debitAt law origin crossing).1.request.signer ≠
      community (debitAt law origin crossing).2.1 := by rw [rowEq]; exact foreign
  let compiler := crossingCompiler law origin community
  have classified : compiler.classifyBoundary crossing = .inl (⟨other⟩ : compiler.BoundaryActiveAt crossing) := by
    simp [compiler, crossingCompiler, other]
  cases certified : compiler.boundaryCertificate? crossing with
  | none =>
      unfold SourceOwnedCrossingCompiler.boundaryCertificate? at certified
      split at certified
      · contradiction
      · rename_i inactive picked
        rw [classified] at picked
        cases picked
  | some boundary =>
      refine ⟨⟨crossing, boundary⟩, ?_, rowEq⟩
      change (⟨crossing, boundary⟩ : compiler.AnyBoundaryCertificate) ∈
        compiler.crossingTrace.filterMap compiler.boundaryCertificateEntry?
      apply List.mem_filterMap.mpr
      exact ⟨crossing, compiler.exactCrossing_mem crossing,
        by simp [SourceOwnedCrossingCompiler.boundaryCertificateEntry?, certified]⟩

theorem boundary_from_original_positive_loss (law : Law) (origin : Origin) (community : Party → Community)
    (row : Debit) (original : row.1 ∈ law.rawItems origin.1 origin.2)
    (valid : law.Valid row.1.before row.1.request) (positive : 0 < loss law row)
    (foreign : community row.1.request.signer ≠ community row.2.1) :
    ∃ boundary ∈ (sourceCrossings law origin community).boundaryCertificates,
      debitAt law origin boundary.crossing = row :=
  boundary_from_original_row law origin community row original valid
    (positive_loss_requires_the_original_debit law row valid positive) positive foreign

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary
