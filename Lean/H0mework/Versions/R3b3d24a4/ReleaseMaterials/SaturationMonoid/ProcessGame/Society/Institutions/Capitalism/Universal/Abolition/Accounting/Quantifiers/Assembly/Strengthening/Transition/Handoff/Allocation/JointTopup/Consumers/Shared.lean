import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.JointTopup.Optimize
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics.Stock
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics.Slack
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Reserve.Original

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.JointTopup.Consumers

open Source.Program Diagnostics
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear

private abbrev Address := Bool × Unit
private abbrev Material := ℕ × ExecutionItem Bool Unit Unit Unit Unit
private abbrev Label := StockSite Address Material ⊕ LimitSite Bool Unit

private def keys : List Address := [(false, ()), (true, ())]
private theorem distinct : keys.Nodup := by decide

private def law : RawLaw Bool Unit Unit Unit Unit where
  technique := fun _ _ => ⟨[], [], [], []⟩
  controller := fun _ _ => false
  allowed := fun _ _ _ => true
  stockPort := fun _ _ _ => ()
  revisionPort := fun _ => ()
  revisionCost := fun _ _ => []
  settlementUnit := fun _ => ()
  settlementRate := fun _ => 1
  issuerPort := fun _ => ()
  necessities := fun _ _ => [((), 1)]
  mandatoryMaintenance := fun _ _ => []
  duration := fun _ => 1

private def raw : RawCurrent Bool Unit Unit Unit := ⟨fun _ _ => 1, fun _ _ _ => 0, (), 8, 0⟩
private def use (person : Bool) : Request Bool Unit Unit Unit Unit :=
  ⟨person, [], (), [], .use person [((), 1)] .external⟩

private def original := Reserve.readSteps law (fun (_ : Bool) _ => 0)
  ((law.rawItems raw [use false, use true]).map fun item => (item, raw.clock)) 0

private abbrev Width := 0 + List.length keys

private def stockTags (key : Address) : List (Tagged Label Width) :=
  let stock := (Affine.literal (raw.stock key.1 key.2)).add (extraForm keys distinct 0 key)
  (attach (stockLabels key 2 raw.clock original)
    (stockConstraintsFor [false, true] (fun person => (person, ())) key (fun _ _ => Affine.literal 0)
      original (fun _ => Affine.literal 1) stock)).map (Tagged.mapLabel Sum.inl)

private def supply (capacity : ℚ) : Limits Bool Unit :=
  { atAddress := fun _ => some 1, shared := fun _ => some capacity }

private def system (checked : List Address) (capacity : ℚ) : List (Tagged Label Width) :=
  checked.flatMap stockTags ++ (limitTags (supply capacity) keys distinct 0).map (Tagged.mapLabel Sum.inr)

def individuallyFits (person : Bool) : Bool :=
  match diagnose (system [(person, ())] 1) with
  | .feasible _ _ => true
  | .blocked _ => false

def sharedFailure : Option (ℚ × ℚ × ℚ × ℚ) :=
  match diagnose (system keys 1) with
  | .feasible _ _ => none
  | .blocked failure =>
    match failure.label with
    | .inr (.sharedCap () amount) =>
        some (amount, failure.minimumSlack.amount,
          extraAt keys distinct failure.witness (false, ()), extraAt keys distinct failure.witness (true, ()))
    | _ => none

/-- Both material paths can protect their original held needs separately
within one unit. The shared ceiling sees both addresses on the same word. -/
theorem two_individually_payable_additions_share_the_one_original_pool :
    individuallyFits false = true ∧ individuallyFits true = true ∧
    sharedFailure = some (1, 1, 1, 1) := by
  decide +kernel

private def weights (key : Address) : ℚ := if key.1 then 3 else 2
private def score : Affine Width := weightedForm keys distinct 0 weights

private theorem score_nonnegative (values : Fin Width → ℚ)
    (admitted : Feasible (numeric (system keys 2)) values) : 0 ≤ score.eval values := by
  have checks : Feasible (numeric (keys.flatMap stockTags)) values ∧
      Feasible (numeric (limitTags (supply 2) keys distinct 0)) values := by
    simpa only [system, numeric_append, feasible_append, numeric_mapLabel] using admitted
  have enough := (limitTags_exact _ _ _ _).mp checks.2
  unfold score
  rw [weightedForm_exact]
  exact weightedTotal_nonnegative _ _ _ (fun key _ => by unfold weights; split <;> norm_num)
    (fun key listed => (enough.1 key listed).1)

def sharedMinimum : Option (ℚ × ℚ × ℚ) :=
  match minimize (system keys 2) score score_nonnegative with
  | .attained values _ _ => some (score.eval values,
      extraAt keys distinct values (false, ()), extraAt keys distinct values (true, ()))
  | .blocked _ => none

theorem two_units_attain_the_weighted_joint_minimum :
    sharedMinimum = some (5, 1, 1) := by
  decide +kernel

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.JointTopup.Consumers
