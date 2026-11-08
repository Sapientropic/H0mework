import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity.FirstFailure

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity.Profile

open scoped BigOperators

variable {Address Row Item : Type*}
variable [Fintype Row] [Fintype Item] [DecidableEq Address]

/-- Old due rows stay funded while the next instruction debits its own
input. Rows maturing at the same commit are checked together at that cut. -/
def pastDue (view : Profile Address Row Item) (time : ℚ) (address : Address) : ℚ :=
  ∑ row, if view.address row = address ∧ view.deadline row < time then
    view.required row - view.paidThrough time row else 0

def beforeDebitGap (view : Profile Address Row Item) (before : Item → Address → ℚ)
    (item : Item) (address : Address) : ℚ :=
  view.pastDue (view.commit item) address + view.debit item address - before item address

theorem beforeDebitGap_fits_iff (view : Profile Address Row Item) (before : Item → Address → ℚ)
    (item : Item) (address : Address) (reserve : ℚ) :
    view.beforeDebitGap before item address ≤ reserve ↔
      view.pastDue (view.commit item) address + view.debit item address ≤ before item address + reserve := by
  rw [beforeDebitGap, sub_le_iff_le_add, add_comm reserve]

def beforeDebitReserve (view : Profile Address Row Item) (before : Item → Address → ℚ)
    (time : ℚ) (address : Address) : ℚ :=
  (insert 0 ((Finset.univ.filter (fun item => view.commit item ≤ time)).image
    (fun item => view.beforeDebitGap before item address))).max' ⟨0, Finset.mem_insert_self _ _⟩

theorem beforeDebitReserve_fits_iff (view : Profile Address Row Item) (before : Item → Address → ℚ)
    (time : ℚ) (address : Address) (reserve : ℚ) :
    view.beforeDebitReserve before time address ≤ reserve ↔
      0 ≤ reserve ∧ ∀ item, view.commit item ≤ time → view.beforeDebitGap before item address ≤ reserve := by
  let values := insert 0 ((Finset.univ.filter (fun item => view.commit item ≤ time)).image
    (fun item => view.beforeDebitGap before item address))
  have nonempty : values.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  change values.max' nonempty ≤ reserve ↔ _
  refine (Finset.max'_le_iff values nonempty).trans ?_
  constructor
  · intro bound
    exact ⟨bound 0 (Finset.mem_insert_self _ _), fun item inside =>
      bound _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, inside⟩)))⟩
  · rintro ⟨zero, fits⟩ amount listed
    rcases Finset.mem_insert.mp listed with rfl | listed
    · exact zero
    · obtain ⟨item, original, rfl⟩ := Finset.mem_image.mp listed
      exact fits item (Finset.mem_filter.mp original).2

theorem beforeDebitReserve_attained (view : Profile Address Row Item) (before : Item → Address → ℚ)
    (time : ℚ) (address : Address) (positive : 0 < view.beforeDebitReserve before time address) :
    ∃ item, view.commit item ≤ time ∧
      view.beforeDebitReserve before time address = view.beforeDebitGap before item address := by
  let values := insert 0 ((Finset.univ.filter (fun item => view.commit item ≤ time)).image
    (fun item => view.beforeDebitGap before item address))
  have nonempty : values.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  have listed : view.beforeDebitReserve before time address ∈ values := Finset.max'_mem values nonempty
  rcases Finset.mem_insert.mp listed with zero | listed
  · exact ((ne_of_gt positive) zero).elim
  obtain ⟨item, original, exactGap⟩ := Finset.mem_image.mp listed
  exact ⟨item, (Finset.mem_filter.mp original).2, exactGap.symm⟩

def protectedGap (view : Profile Address Row Item) (before : Item → Address → ℚ)
    (time : ℚ) (address : Address) : ℚ :=
  max (view.gap time address) (view.beforeDebitReserve before time address)

theorem protectedGap_at_lastCut (view : Profile Address Row Item) (before : Item → Address → ℚ)
    (time : ℚ) (started : view.start ≤ time) (address : Address) :
    view.protectedGap before (view.lastCut time started) address = view.protectedGap before time address := by
  have sameItems : Finset.univ.filter (fun item => view.commit item ≤ view.lastCut time started) =
      Finset.univ.filter (fun item => view.commit item ≤ time) := by
    ext item
    simp only [Finset.mem_filter, view.commit_le_lastCut_iff time started]
  unfold protectedGap beforeDebitReserve
  rw [view.gap_at_lastCut time started address]
  exact congrArg (fun items : Finset Item => max (view.gap time address)
    ((insert 0 (items.image (fun item => view.beforeDebitGap before item address))).max'
      ⟨0, Finset.mem_insert_self _ _⟩)) sameItems

def rollingReserveThrough (view : Profile Address Row Item) (before : Item → Address → ℚ)
    (time : ℚ) (address : Address) : ℚ :=
  max (view.reserveThrough time address) (view.beforeDebitReserve before time address)

theorem rollingReserveThrough_fits_iff (view : Profile Address Row Item) (before : Item → Address → ℚ)
    (horizon : ℚ) (address : Address) (reserve : ℚ) :
    view.rollingReserveThrough before horizon address ≤ reserve ↔
      0 ≤ reserve ∧
      (∀ time, view.start ≤ time → time ≤ horizon → view.gap time address ≤ reserve) ∧
      (∀ item, view.commit item ≤ horizon →
        view.pastDue (view.commit item) address + view.debit item address ≤ before item address + reserve) := by
  rw [rollingReserveThrough, max_le_iff, view.reserveThrough_fits_iff, view.beforeDebitReserve_fits_iff]
  simp_rw [view.beforeDebitGap_fits_iff]
  tauto

theorem protected_safe_iff_tight_rolling_reserve (view : Profile Address Row Item) (before : Item → Address → ℚ)
    (addresses : List Address) (reserve : Address → ℚ) (horizon : ℚ) (started : view.start ≤ horizon) :
    view.SafeThroughAt (view.protectedGap before) addresses reserve horizon ↔
      ∀ address ∈ addresses, view.rollingReserveThrough before horizon address ≤ reserve address := by
  constructor
  · intro safe address listed
    apply max_le
    · have horizonFits := max_le_iff.mp (safe horizon started le_rfl address listed)
      have nonnegative := ((view.beforeDebitReserve_fits_iff before horizon address _).mp horizonFits.2).1
      exact (view.reserveThrough_fits_iff horizon address _).mpr
        ⟨nonnegative, fun time reached within => (max_le_iff.mp (safe time reached within address listed)).1⟩
    · exact (max_le_iff.mp (safe horizon started le_rfl address listed)).2
  · intro fits time reached within address listed
    have bound := max_le_iff.mp (fits address listed)
    have after := (view.reserveThrough_fits_iff horizon address _).mp bound.1
    have beforeFits := (view.beforeDebitReserve_fits_iff before horizon address _).mp bound.2
    exact max_le (after.2 time reached within) ((view.beforeDebitReserve_fits_iff before time address _).mpr
      ⟨beforeFits.1, fun item inside => beforeFits.2 item (inside.trans within)⟩)

def inspectProtected (view : Profile Address Row Item) (before : Item → Address → ℚ)
    (addresses : List Address) (reserve : Address → ℚ) :
    view.DecisionAt (view.protectedGap before) addresses reserve :=
  view.inspectAt (view.protectedGap before) (view.protectedGap_at_lastCut before) addresses reserve

/-- The first failed protected cut is a short due balance or an original
debit at that same time. An earlier original debit could not have caused it. -/
theorem protected_shortage_cause {view : Profile Address Row Item} {before : Item → Address → ℚ}
    {addresses : List Address} {reserve : Address → ℚ}
    (allOriginal : ∀ item, view.start ≤ view.commit item)
    (fundedReserve : ∀ address ∈ addresses, 0 ≤ reserve address)
    (failure : view.FirstShortageAt (view.protectedGap before) addresses reserve) :
    reserve failure.address < view.gap failure.time failure.address ∨
      ∃ item, view.commit item = failure.time ∧
        reserve failure.address < view.beforeDebitGap before item failure.address := by
  rcases lt_max_iff.mp failure.short with after | during
  · exact .inl after
  · have positive := (fundedReserve failure.address failure.watched).trans_lt during
    obtain ⟨item, within, same⟩ := view.beforeDebitReserve_attained before failure.time failure.address positive
    rw [same] at during
    refine .inr ⟨item, le_antisymm within (le_of_not_gt fun earlier => ?_), during⟩
    have old := max_le_iff.mp (failure.earlier (view.commit item) (allOriginal item) earlier
      failure.address failure.watched)
    exact (not_le_of_gt during) (((view.beforeDebitReserve_fits_iff before (view.commit item)
      failure.address _).mp old.2).2 item le_rfl)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity.Profile
