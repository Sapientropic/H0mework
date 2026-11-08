import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PartyCode

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PartyFrame
open Institutions.Capitalism.Universal.Source.Program
open Distributed Reaction
open Repayment.Recovery (Good)
open WholePartyLift PartyCode
variable (old : OldCode) (outside : Good → ℚ)

def packet (p : old.Packet) : (code old outside).Packet := ⟨p.sender,p.recipient,p.signal,p.sentAfter⟩
def unpacket (p : (code old outside).Packet) : old.Packet := ⟨p.sender,p.recipient,p.signal,p.sentAfter⟩
def frame (f : old.Frame) : (code old outside).Frame := ⟨f.word.map request,f.sent.map (packet old outside),f.inbox,f.localLegal⟩
def unframe (f : (code old outside).Frame) : old.Frame := ⟨unword f.word,f.sent.map (unpacket old outside),f.inbox,f.localLegal⟩

theorem unframe_frame (f : old.Frame) : unframe old outside (frame old outside f) = f := by
  cases f
  simp only [unframe,frame,unword_word,List.map_map]
  have identity : unpacket old outside ∘ packet old outside = id := by funext p;cases p;rfl
  simp only [identity,List.map_id]

theorem action (p : old.Policy) (site : Fin old.sites) (signal : Fin old.signals) :
    (code old outside).action (policy old outside p) site signal = (old.action p site signal).map request := by
  unfold Code.action
  change (if old.memoryReady signal then (p (site,signal) _).map request else []) = _
  split <;> rfl

theorem rawAt (same : old.law = oldLaw) (here : OldCurrent) (f : old.Frame) :
    (code old outside).rawAt (current here outside) (frame old outside f) = current (old.rawAt here f) outside := by
  change (newLaw.execute (current here outside) 0 (f.word.map request)).final = _
  rw [WholePartyExecution.execute]
  rw [← same]
  rfl

theorem snapshot (here : OldCurrent) (site : Fin old.sites) :
    PartyCode.snapshot ((code old outside).snapshot site (current here outside)) = old.snapshot site here := rfl

theorem step (same : old.law = oldLaw) (p : old.Policy) (here : OldCurrent) (f : old.Frame)
    (ev : Event OldParty Good OldPort OldState Unit old.sites) :
    (code old outside).step (policy old outside p) (current here outside) (frame old outside f) (event ev) =
      frame old outside (old.step p here f ev) := by
  have paid : ∀ word : List OldAction,
      decide (∀ item ∈ (code old outside).law.rawItems
        ((code old outside).rawAt (current here outside) (frame old outside f)) (word.map request),
        (code old outside).law.Valid item.before item.request) =
      decide (∀ item ∈ old.law.rawItems (old.rawAt here f) word,old.law.Valid item.before item.request) := by
    intro word
    rw [rawAt old outside same]
    change decide (∀ item ∈ newLaw.rawItems (current (old.rawAt here f) outside) (word.map request), newLaw.Valid item.before item.request) = _
    exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using PartyCode.paid old outside same (old.rawAt here f) word)
  cases ev with
  | adversary a => simp [event,Code.step,frame,List.map_append]
  | activate site =>
      simp only [event,Code.step,action]
      rw [paid]
      simp [frame,code,word_word,List.map_append]
  | send sender recipient =>
      have reading : (code old outside).readLocal sender ((code old outside).snapshot sender
          ((code old outside).rawAt (current here outside) (frame old outside f))) =
        old.readLocal sender (old.snapshot sender (old.rawAt here f)) := by
        rw [rawAt old outside same]
        rfl
      simp only [event,Code.step]
      dsimp only [code] at reading ⊢
      have paidSend := paid (old.sendCost sender recipient)
      dsimp only [code] at paidSend
      erw [paidSend,reading]
      split_ifs <;> simp_all [frame,packet,code,List.map_append]
  | deliver address =>
      simp only [event,Code.step,frame,List.getElem?_map]
      cases found : f.sent[address]? with
      | none => simp only [Option.map_none]
      | some p =>
          simp only [Option.map_some]
          have paidDelivery := paid (old.deliveryCost p.recipient)
          dsimp only [code] at paidDelivery ⊢
          change decide (∀ item ∈ newLaw.rawItems
            ((code old outside).rawAt (current here outside) (frame old outside f))
            ((old.deliveryCost p.recipient).map request), newLaw.Valid item.before item.request) = _ at paidDelivery
          simp only [frame] at paidDelivery
          dsimp only [code] at paidDelivery
          erw [paidDelivery]
          split_ifs <;> simp_all [packet,List.map_append]

theorem replayFrom (same : old.law = oldLaw) (p : old.Policy) (here : OldCurrent)
    (events : Events old) (f : old.Frame) :
    (events.map event).foldl ((code old outside).step (policy old outside p) (current here outside)) (frame old outside f) =
      frame old outside (events.foldl (old.step p here) f) := by
  induction events generalizing f with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons,List.foldl_cons,step old outside same,ih]

theorem replay (same : old.law = oldLaw) (p : old.Policy) (here : OldCurrent) (events : Events old) :
    (code old outside).replay (policy old outside p) (current here outside) (events.map event) =
      frame old outside (old.replay p here events) := replayFrom old outside same p here events old.start
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PartyFrame
