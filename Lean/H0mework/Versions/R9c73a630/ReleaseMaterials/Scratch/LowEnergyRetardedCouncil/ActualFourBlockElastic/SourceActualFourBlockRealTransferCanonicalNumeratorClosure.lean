import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferCanonicalProof
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
namespace LowEnergy.ActualFourBlockRealTransfer
open LowEnergy.ActualCanonical79Imaginary

/-- Internal closure of the original return vector. The public numerator
producer supplies every group fact from its source-owned analytic theorem. -/
private theorem source_numerator_closure (z : ℂ)
    (h0 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 0) x 0 i) z)
    (h1 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 1) x 0 i) z)
    (h2 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 2) x 0 i) z)
    (h3 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 3) x 0 i) z)
    (h4 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 4) x 0 i) z)
    (h5 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 5) x 0 i) z)
    (h6 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 6) x 0 i) z)
    (h7 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 7) x 0 i) z)
    (h8 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 8) x 0 i) z)
    (h9 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 9) x 0 i) z)
    (h10 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 10) x 0 i) z)
    (h11 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 11) x 0 i) z)
    (h12 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 12) x 0 i) z)
    (h13 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 13) x 0 i) z)
    (h14 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 14) x 0 i) z)
    (h15 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 15) x 0 i) z)
    (h16 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 16) x 0 i) z)
    (h17 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 17) x 0 i) z)
    (h18 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 18) x 0 i) z)
    (h19 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 19) x 0 i) z)
    (h20 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 20) x 0 i) z)
    (h21 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 21) x 0 i) z)
    (h22 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 22) x 0 i) z)
    (h23 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 23) x 0 i) z)
    (h24 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 24) x 0 i) z)
    (h25 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 25) x 0 i) z)
    (h26 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 26) x 0 i) z)
    (h27 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 27) x 0 i) z)
    (h28 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 28) x 0 i) z)
    (h29 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 29) x 0 i) z)
    (h30 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 30) x 0 i) z)
    (h31 : ∀ i : Fin 128, AnalyticAt ℂ (fun x => (canonical_group% 31) x 0 i) z)
    (h32 : ∀ i : Fin 106, AnalyticAt ℂ (fun x => (canonical_group% 32) x 0 i) z)
    (a : Fin 526) :
    AnalyticAt ℂ (fun x => MixedSpectatorCanonical79Data.numeratorPolynomial x 0 a) z := by
  analytic_canonical_numerator_from_groups

open Lean Meta Elab Term
elab "canonical_numerator_closure%" : term =>
  mkConstWithFreshMVarLevels ``source_numerator_closure

end LowEnergy.ActualFourBlockRealTransfer
