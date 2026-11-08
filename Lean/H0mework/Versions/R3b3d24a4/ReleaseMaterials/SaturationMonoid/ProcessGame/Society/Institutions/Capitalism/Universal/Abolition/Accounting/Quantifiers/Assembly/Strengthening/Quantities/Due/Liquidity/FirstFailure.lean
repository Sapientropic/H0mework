import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity.Reserve

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity.Profile

variable {Address Row Item : Type*}
variable [Fintype Row] [Fintype Item]

def SafeThroughAt (view : Profile Address Row Item) (score : ℚ → Address → ℚ)
    (addresses : List Address) (reserve : Address → ℚ) (horizon : ℚ) : Prop :=
  ∀ time, view.start ≤ time → time ≤ horizon → ∀ address ∈ addresses, score time address ≤ reserve address

def failedCutsAt (view : Profile Address Row Item) (score : ℚ → Address → ℚ)
    (addresses : List Address) (reserve : Address → ℚ) : Finset ℚ :=
  view.cuts.filter (fun time => ∃ address ∈ addresses, reserve address < score time address)

structure FirstShortageAt (view : Profile Address Row Item) (score : ℚ → Address → ℚ)
    (addresses : List Address) (reserve : Address → ℚ) where
  time : ℚ
  address : Address
  watched : address ∈ addresses
  actualCut : time ∈ view.cuts
  short : reserve address < score time address
  earlier : ∀ earlier, view.start ≤ earlier → earlier < time →
    ∀ old ∈ addresses, score earlier old ≤ reserve old

theorem FirstShortageAt.safeThrough_iff {view : Profile Address Row Item} {score : ℚ → Address → ℚ}
    {addresses : List Address} {reserve : Address → ℚ}
    (failure : view.FirstShortageAt score addresses reserve) (horizon : ℚ) :
    view.SafeThroughAt score addresses reserve horizon ↔ horizon < failure.time := by
  refine ⟨fun safe => lt_of_not_ge (fun late => ?_), fun early time started within => ?_⟩
  · exact (not_le_of_gt failure.short) (safe failure.time
      (view.start_le_of_mem_cuts failure.actualCut) late failure.address failure.watched)
  · exact failure.earlier time started (within.trans_lt early)

inductive DecisionAt (view : Profile Address Row Item) (score : ℚ → Address → ℚ)
    (addresses : List Address) (reserve : Address → ℚ)
  | noFailure (safe : ∀ horizon, view.SafeThroughAt score addresses reserve horizon)
  | blocked (failure : view.FirstShortageAt score addresses reserve)

private theorem failure_recognized_at_lastCut (view : Profile Address Row Item)
    (score : ℚ → Address → ℚ) (addresses : List Address) (reserve : Address → ℚ)
    (time : ℚ) (started : view.start ≤ time) (address : Address) (listed : address ∈ addresses)
    (stable : score (view.lastCut time started) address = score time address)
    (short : reserve address < score time address) :
    view.lastCut time started ∈ view.failedCutsAt score addresses reserve :=
  Finset.mem_filter.mpr ⟨view.lastCut_mem time started, address, listed, stable ▸ short⟩

/-- Scan the finite original cuts. The blocked result identifies an
actual address, and the first blocked time itself is already unsafe. -/
def inspectAt (view : Profile Address Row Item) (score : ℚ → Address → ℚ)
    (stable : ∀ time (started : view.start ≤ time) address,
      score (view.lastCut time started) address = score time address)
    (addresses : List Address) (reserve : Address → ℚ) :
    view.DecisionAt score addresses reserve := by
  let candidates := view.failedCutsAt score addresses reserve
  if found : candidates.Nonempty then
    let time := candidates.min' found
    have observed := Finset.mem_filter.mp (Finset.min'_mem candidates found)
    let probe := fun address => decide (reserve address < score time address)
    match named : addresses.find? probe with
    | none =>
      have impossible : False := by
        obtain ⟨address, original, short⟩ := observed.2
        exact (List.find?_eq_none.mp named) address original (decide_eq_true short)
      exact impossible.elim
    | some address =>
      have positive : probe address = true := List.find?_some named
      refine .blocked ⟨time, address, List.mem_of_find?_eq_some named, observed.1,
        of_decide_eq_true positive, ?_⟩
      intro earlier started before old original
      exact le_of_not_gt fun short => by
        have bad := view.failure_recognized_at_lastCut score addresses reserve earlier started old original
          (stable earlier started old) short
        have first : time ≤ view.lastCut earlier started := Finset.min'_le candidates _ bad
        exact (not_le_of_gt before) (first.trans (view.lastCut_le earlier started))
  else
    refine .noFailure fun _ time started _ address original => le_of_not_gt fun short => ?_
    exact found ⟨view.lastCut time started,
      view.failure_recognized_at_lastCut score addresses reserve time started address original
        (stable time started address) short⟩

variable [DecidableEq Address]

abbrev SafeThrough (view : Profile Address Row Item) := view.SafeThroughAt view.gap

abbrev FirstShortage (view : Profile Address Row Item) := view.FirstShortageAt view.gap

abbrev Decision (view : Profile Address Row Item) := view.DecisionAt view.gap

theorem FirstShortage.safeThrough_iff {view : Profile Address Row Item} {addresses : List Address}
    {reserve : Address → ℚ} (failure : view.FirstShortage addresses reserve) (horizon : ℚ) :
    view.SafeThrough addresses reserve horizon ↔ horizon < failure.time :=
  FirstShortageAt.safeThrough_iff failure horizon

def inspect (view : Profile Address Row Item) (addresses : List Address) (reserve : Address → ℚ) :
    view.Decision addresses reserve :=
  view.inspectAt view.gap view.gap_at_lastCut addresses reserve

theorem safeThrough_iff_every_address_has_its_tight_reserve (view : Profile Address Row Item)
    (addresses : List Address) (reserve : Address → ℚ) (horizon : ℚ)
    (nonnegative : ∀ address ∈ addresses, 0 ≤ reserve address) :
    view.SafeThrough addresses reserve horizon ↔
      ∀ address ∈ addresses, view.reserveThrough horizon address ≤ reserve address := by
  constructor
  · intro safe address listed
    exact (view.reserveThrough_fits_iff horizon address _).mpr
      ⟨nonnegative address listed, fun time started within => safe time started within address listed⟩
  · intro bound time started within address listed
    exact ((view.reserveThrough_fits_iff horizon address _).mp (bound address listed)).2 time started within

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity.Profile
