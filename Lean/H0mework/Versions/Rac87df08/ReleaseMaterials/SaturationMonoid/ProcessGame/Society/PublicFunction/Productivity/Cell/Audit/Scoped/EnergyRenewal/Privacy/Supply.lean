import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Governance
import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Windows

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

/-- These are the decoder's public inputs. Each snapshot is rebuilt from its own actual governance prefix. -/
abbrev ReplyInput := Nat × Nat × Party × Option Record

def rebuildReplies (queries : Nat → Query) (larger : Bool) (births : Governance.Births)
    (inputs : List ReplyInput) : Governance.Replies :=
  inputs.foldl (fun past (atCut,observed,challenger,alleged) =>
    past ++ [(atCut,⟨challenger,observed,(Governance.current queries larger births past atCut).technology,alleged⟩)]) []

theorem rebuilt_replies_equal (queries : Nat → Query) (births : Governance.Births) (inputs : List ReplyInput) :
    rebuildReplies queries false births inputs = rebuildReplies queries true births inputs := by
  have stepEqual : (fun (past : Governance.Replies) (input : ReplyInput) =>
      past ++ [(input.1,⟨input.2.2.1,input.2.1,(Governance.current queries false births past input.1).technology,input.2.2.2⟩)]) =
    (fun (past : Governance.Replies) (input : ReplyInput) =>
      past ++ [(input.1,⟨input.2.2.1,input.2.1,(Governance.current queries true births past input.1).technology,input.2.2.2⟩)]) := by
    funext past input
    rw [(GovernancePrivacy.current queries births past input.1).technology]
  unfold rebuildReplies
  exact congrArg (fun step => inputs.foldl step []) stepEqual

def sourcePlan (queries : Nat → Query) (larger : Bool) (births : Governance.Births)
    (replies : List ReplyInput) (cut : Nat) (candidate : Party) : Plan :=
  ⟨queries,larger,births,rebuildReplies queries larger births replies,cut,candidate⟩

structure PlanTwin (left right : Plan) : Prop where
  cut : left.cut = right.cut
  candidate : left.candidate = right.candidate
  before : Twin (EnergyRenewal.before left) (EnergyRenewal.before right)

theorem source_plans (queries : Nat → Query) (births : Governance.Births)
    (replies : List ReplyInput) (cut : Nat) (candidate : Party) :
    PlanTwin (sourcePlan queries false births replies cut candidate) (sourcePlan queries true births replies cut candidate) := by
  refine ⟨rfl,rfl,?_⟩
  unfold EnergyRenewal.before
  rw [original_prefix _ _ (Nat.le_refl _),original_prefix _ _ (Nat.le_refl _)]
  change Twin (Governance.current queries false births (rebuildReplies queries false births replies) cut)
    (Governance.current queries true births (rebuildReplies queries true births replies) cut)
  rw [rebuilt_replies_equal]
  exact GovernancePrivacy.current _ _ _ _

theorem PlanTwin.eligible {left right : Plan} (same : PlanTwin left right) : Eligible left ↔ Eligible right := by
  simp only [Eligible,same.cut,same.candidate]
theorem PlanTwin.quiet {left right : Plan} (same : PlanTwin left right) : Quiet (EnergyRenewal.before left) ↔ Quiet (EnergyRenewal.before right) := by
  simp only [Quiet,same.before.technology]

theorem supply_stable (plan : Plan) : ∀ stage ∈ supplyStages plan,AuditLaw.Stable stage := by
  simp only [supplyStages,List.mem_cons,List.not_mem_nil,or_false]
  intro stage member
  rcases member with rfl | rfl | rfl <;> exact ⟨fun _ _ _ => rfl,fun _ => by simp [AuditLaw.Safe,transfer,applicationFee]⟩
theorem supply_safe (plan : Plan) (current : AuditCurrent) : ∀ action ∈ supplyWord plan current,AuditLaw.Safe action := by
  unfold supplyWord
  split
  · exact AuditLaw.attempt_safe _ _ (supply_stable plan)
  · simp

theorem PlanTwin.actions {left right : Plan} (same : PlanTwin left right) : actions left = actions right := by
  unfold EnergyRenewal.actions supplyWord
  simp only [← propext same.eligible,← propext same.quiet]
  split
  · have stages : supplyStages left = supplyStages right := by simp only [supplyStages,same.candidate]
    rw [← stages]
    exact AuditLaw.attempt same.before _ (supply_stable left)
  · rfl

theorem PlanTwin.paid {left right : Plan} (same : PlanTwin left right) : Paid left ↔ Paid right := by
  unfold Paid RawLaw.rawItems
  rw [← same.actions]
  exact and_congr Iff.rfl (AuditLaw.all_valid same.before _ (supply_safe left _) 0)

theorem PlanTwin.after {left right : Plan} (same : PlanTwin left right) : Twin (after left) (after right) := by
  by_cases positive : 0 < left.cut
  · rw [actual_supply_next left positive,actual_supply_next right (same.cut ▸ positive),← same.actions]
    exact AuditLaw.next same.before _ (supply_safe left _)
  · have zero : left.cut = 0 := by omega
    have zeroRight : right.cut = 0 := same.cut ▸ zero
    unfold EnergyRenewal.after
    rw [zero,zeroRight,current_succ,current_succ]
    unfold EnergyRenewal.current
    change Twin (auditLaw.next initial []) (auditLaw.next initial [])
    exact Twin.refl _

theorem PlanTwin.scope {left right : Plan} (same : PlanTwin left right) (lr : Ready left) (rr : Ready right) :
    lr.scope = rr.scope := by
  simp only [Ready.scope,Ready.task,same.after.clock]

set_option backward.isDefEq.respectTransparency false in
theorem nextEpoch_available (plan : Plan) : (Runtime.nextEpoch plan).isSome = true ↔
    Eligible plan ∧ Quiet (before plan) ∧ Paid plan := by
  unfold Runtime.nextEpoch
  split
  · rename_i ready generated
    simp only [Option.isSome_some,eq_self,true_iff]
    exact ⟨ready.eligible,ready.quiet,ready.paid⟩
  · rename_i reason generated
    simp only [Option.isSome_none,Bool.false_eq_true,false_iff]
    intro all
    have actual : generate plan = .blocked reason := by
      simpa only [Runtime.consume,SourceNativeLivingRuntimeFacade.readoutAt,Runtime.facade,
        Runtime.projectionLaw,SourceNativeProjectionLaw.outcomeAt,Runtime.result,Runtime.Output] using generated
    unfold generate at actual
    split at actual
    · cases actual
    · rename_i selected
      have present : choose plan ≠ none := by simp [choose,all.1,all.2.1,all.2.2]
      exact present selected

theorem PlanTwin.available {left right : Plan} (same : PlanTwin left right) :
    (Runtime.nextEpoch left).isSome = (Runtime.nextEpoch right).isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [nextEpoch_available,nextEpoch_available,same.eligible,same.quiet,same.paid]

theorem epoch_word_energy {plan : Plan} (ready : Ready plan) (queries : Nat → Query) (current : AuditCurrent) :
    ∀ action ∈ ready.epochWord queries current,EnergyAction action := by
  unfold Ready.epochWord
  dsimp only
  split
  · apply attempt_energy
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    intro stage member
    rcases member with rfl | rfl | rfl | rfl
    · exact stable_command _ _ _
    · exact stable_command _ _ _
    · exact stable_access _ _
    · exact stable_fee
  · exact attempt_energy _ _ _ (by
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      intro stage member
      rcases member with rfl | rfl
      · exact stable_access _ _
      · exact stable_fee)

theorem PlanTwin.epoch_word {left right : Plan} (same : PlanTwin left right) (lr : Ready left) (rr : Ready right)
    {lc rc : AuditCurrent} (current : Twin lc rc) (queries : Nat → Query) :
    lr.epochWord queries lc = rr.epochWord queries rc := by
  have scope := same.scope lr rr
  unfold Ready.epochWord Ready.readWord Ready.law
  rw [← same.candidate,← same.after.round,← current.round,← scope]
  dsimp only
  split
  · apply current.attempt lr.scope rfl
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    intro stage member
    rcases member with rfl | rfl | rfl | rfl
    · exact stable_command _ _ _
    · exact stable_command _ _ _
    · exact stable_access _ _
    · exact stable_fee
  · apply current.attempt lr.scope rfl
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    intro stage member
    rcases member with rfl | rfl
    · exact stable_access _ _
    · exact stable_fee

theorem PlanTwin.epoch {left right : Plan} (same : PlanTwin left right) (lr : Ready left) (rr : Ready right)
    (queries : Nat → Query) (n : Nat) : Twin (lr.epochCurrent queries n) (rr.epochCurrent queries n) := by
  induction n with
  | zero => unfold Ready.epochCurrent; exact same.after
  | succ n ih =>
    rw [lr.epoch_succ,rr.epoch_succ]
    have lawEqual : lr.law = rr.law := congrArg (Mandate.law energyBase) (same.scope lr rr)
    rw [← lawEqual]
    split
    · exact ih.next lr.scope rfl [] (by simp)
    · rw [← same.epoch_word lr rr ih queries]
      exact ih.next lr.scope rfl _ (epoch_word_energy _ _ _)

theorem PlanTwin.first {left right : Plan} (same : PlanTwin left right)
    (ls : Runtime.EpochSeed left) (rs : Runtime.EpochSeed right) (queries : Nat → Query) (ordinal : Nat) :
    WindowTwin (Continuation.first ls queries ordinal) (Continuation.first rs queries ordinal) :=
  ⟨same.scope ls.ready rs.ready,same.candidate,same.epoch ls.ready rs.ready queries (ordinal+1)⟩

/-- No initial relation is supplied by a caller: original governance and first paid supply generate it, or both refuse. -/
theorem original_source_generates_initial_windows (queries epochQueries : Nat → Query) (births : Governance.Births)
    (replies : List ReplyInput) (cut : Nat) (candidate : Party) (ordinal : Nat) :
    Option.Rel WindowTwin
      ((Runtime.nextEpoch (sourcePlan queries false births replies cut candidate)).map (fun seed => Continuation.first seed epochQueries ordinal))
      ((Runtime.nextEpoch (sourcePlan queries true births replies cut candidate)).map (fun seed => Continuation.first seed epochQueries ordinal)) := by
  have same := source_plans queries births replies cut candidate
  have available := same.available
  cases left : Runtime.nextEpoch (sourcePlan queries false births replies cut candidate) with
  | none =>
    cases right : Runtime.nextEpoch (sourcePlan queries true births replies cut candidate) with
    | none => exact .none
    | some seed => simp [left,right] at available
  | some seed =>
    cases right : Runtime.nextEpoch (sourcePlan queries true births replies cut candidate) with
    | none => simp [left,right] at available
    | some other => exact .some (same.first seed other epochQueries ordinal)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy
