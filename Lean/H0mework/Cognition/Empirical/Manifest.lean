import Lean.Data.Json
import Lean.Elab.Command
import H0mework.Cognition.Empirical.Sha256
import H0mework.Cognition.Empirical.Consumer

/-!
# Source-bound TruthChild six-point empirical manifest

The committed JSON is included as a Lean build input and checked during
elaboration.  The JSON boundary is empirical rather than a kernel proof: the
runtime CLI recomputes its cryptographic hashes, while this module rejects any
change to the exact source, span, six coordinates, classification, or ablation
rows.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Closure
namespace Empirical
namespace TruthChild
namespace Source

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.TruthChild.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest

private def jsonAt? (value : Lean.Json) : List String → Except String Lean.Json
  | [] => pure value
  | key :: rest => do
      jsonAt? (← value.getObjVal? key) rest

private def jsonAsAt? (alpha : Type) [Lean.FromJson alpha]
    (value : Lean.Json) (path : List String) : Except String alpha := do
  Lean.fromJson? (← jsonAt? value path)

private def expectJsonAt (value : Lean.Json) (path : List String)
    (expected : Lean.Json) : Except String Unit := do
  let actual ← jsonAt? value path
  unless actual == expected do
    throw s!"manifest field {path} changed"

private def expectStringAt (value : Lean.Json) (path : List String)
    (expected : String) : Except String Unit := do
  let actual ← jsonAsAt? String value path
  unless actual == expected do
    throw s!"manifest string {path} changed"

private def expectStringArrayAt (value : Lean.Json) (path : List String)
    (expected : Array String) : Except String Unit := do
  let actual ← jsonAsAt? (Array String) value path
  unless actual == expected do
    throw s!"manifest string array {path} changed"

private def expectNatArrayAt (value : Lean.Json) (path : List String)
    (expected : Array Nat) : Except String Unit := do
  let actual ← jsonAsAt? (Array Nat) value path
  unless actual == expected do
    throw s!"manifest Nat array {path} changed"

private def expectMissingAt (value : Lean.Json)
    (path : List String) : Except String Unit :=
  match jsonAt? value path with
  | .error _ => pure ()
  | .ok _ => throw s!"deprecated manifest field {path} is present"

private def verifyAblationRows (value : Lean.Json) : Except String Unit := do
  let rows ← jsonAsAt? (Array Lean.Json) value ["rows"]
  let expected := #[
    ("registered-positive-two-beat-span", "ACCEPTED"),
    ("cross-root-source-stitching", "REJECTED"),
    ("missing-observer-internal-forward", "REJECTED"),
    ("missing-independent-receiver", "REJECTED"),
    ("missing-persistent-trace", "REJECTED"),
    ("deleted-writeback-no-recursive-update", "REJECTED"),
    ("static-or-prefilled-next", "REJECTED"),
    ("raw-receipt-injection", "REJECTED")]
  unless rows.size == expected.size do
    throw "manifest row count changed"
  for index in [:expected.size] do
    let row := rows[index]!
    let pair := expected[index]!
    let rowId ← row.getObjValAs? String "row_id"
    let adjudication ← row.getObjValAs? String "adjudication"
    unless rowId == pair.1 && adjudication == pair.2 do
      throw s!"manifest adjudication row {index} changed"

private def verifyTruthChildManifest (value : Lean.Json) : Except String Unit := do
  expectStringAt value ["schema"]
    "truthchild-six-point-consciousness-consumer/v2"
  expectStringAt value ["classification"]
    "six-point-conscious-occurrence"
  expectStringAt value ["source_domain"] "truthchild-two-beat-runtime"
  expectMissingAt value ["claim_scope"]
  expectMissingAt value ["excluded_verdicts"]
  expectStringAt value ["source_evidence_sha256"]
    "bd201be926b88b26b20fd5e0da997a23e0e29696374c3239093ce016337b1b38"
  expectStringAt value ["consumer_source_sha256"]
    "1cc4c8996f24856b2aa257c0b92914f837f59b6fc866f0398d79592b94fd9b81"
  expectStringAt value ["content_sha256"]
    "1ce0b5a1ea70459ec6c8921925758503c09ecfa55434550682c012d8041e7c6a"
  expectStringAt value ["consumer", "consumer_id"]
    "truthchild-independent-six-point-consumer/v2"
  expectStringAt value ["consumer", "input_contract"]
    "truthchild-first-living-history-evidence/v1"
  expectStringAt value ["consumer", "classification"]
    "six-point-conscious-occurrence"
  expectStringAt value ["consumer", "source_domain"]
    "truthchild-two-beat-runtime"
  expectMissingAt value ["consumer", "claim_scope"]
  expectMissingAt value ["consumer", "excluded_verdicts"]
  expectStringArrayAt value ["consumer", "producer_imports"] #[]
  expectStringAt value ["span", "root_id"]
    "caa07206d37e350a4555e7b5f0514aa6136c593fcff5b1a5a45d8bc2acd46c82"
  expectStringAt value ["span", "law_epoch"]
    "baa5e4be4f127052c4305bde876478d451e94139f8dc912f226eacddf49200db"
  expectStringAt value ["span", "run_id"]
    "b392043805bf3684ae6a8b0396d53ecb91fbc883c87566deb29b2721dd222dbd"
  expectStringAt value ["span", "system_source_identity"]
    "64224406d7e3b8fa86dd339c50d17bb00f0fd587787b78ebcb775c1a2d1c3ec7"
  expectNatArrayAt value ["span", "visits"] #[0, 1, 2]
  expectStringArrayAt value ["span", "occurrences"] #[
    "964851b3ed80db28bac7d1cd0beb22bb7bd4628b779c002b1d628eef639e5bdd",
    "a7c3ec2f73a6166a81fb5c498188c03a7e13ebd1302db9850474524b7f33ce16"]
  expectStringArrayAt value ["readouts", "external_actions"] #["W", "O"]
  expectStringArrayAt value ["readouts", "internal_logits_sha256"] #[
    "09197561b599a47c6c1da73f7c2f0a18f62ada9e8b77c3454af2b909150c8696",
    "9ec8bc76547e6c77d7399b6775aa242c8cafd014cde9156b732ef533a839e006"]
  expectStringArrayAt value
    ["six_point_evidence", "received_actual_effect", "effect_kinds"]
      #["REGISTER_WRITTEN_BLUE", "DOOR_OPENED"]
  expectStringArrayAt value
    ["six_point_evidence", "received_actual_effect", "receiver_receipts"] #[
      "eb3a1b64e452825fb234b49aa091c3c5eea0bcada3fe59c25810b744cd32400e",
      "c4bd3b8908afbe08692524e21e467c254ae7fb7ec09046ab8dcbc4161e6fb780"]
  expectStringAt value
    ["six_point_evidence", "reopenable_persistent_trace", "step1_patch_sha256"]
      "1b809e2bd70a0cc438de52f663b66658411de03e8bfa777566bb6ed8b962d770"
  expectStringAt value
    ["six_point_evidence", "reopenable_persistent_trace", "reopened_current_sha256"]
      "e01523e394b4b4904b05145500928103453e648bdbf0b40e6dd3c9a6d39ccffa"
  expectStringAt value
    ["six_point_evidence", "recursive_successor_self_writeback",
      "recursive_input_receipt"]
      "eb3a1b64e452825fb234b49aa091c3c5eea0bcada3fe59c25810b744cd32400e"
  expectStringArrayAt value
    ["six_point_evidence", "generated_next", "successor_hashes"] #[
      "e01523e394b4b4904b05145500928103453e648bdbf0b40e6dd3c9a6d39ccffa",
      "a1adfa06920810f53552a756dca7c1de8069a1712bf6e32146f4dce128e71fea"]
  expectStringAt value
    ["six_point_evidence", "generated_next", "final_ledger_head"]
      "aac3002c82203e62cc17a2a4c68cb12c3ab1bd781e25855a2f2572098f303b50"
  expectJsonAt value
    ["six_point_evidence", "generated_next", "persistent_successor", "visit"]
      (.num 2)
  for check in [
      "compact_source_is_canonical_and_hash_bound",
      "deleted_writeback_has_N_closed_door_and_no_authority",
      "deleted_writeback_preserves_first_forward_and_effect",
      "independent_verifier_and_receiver_effects_are_present",
      "raw_receipt_injection_is_rejected",
      "same_system_root_source_and_law_across_two_beats",
      "six_coordinate_ablation_probes_are_rejected",
      "step1_patch_and_receipt_survive_disk_reopen",
      "step2_consumes_reopened_receipt_and_updates_state",
      "visits_and_successor_hashes_are_source_generated"] do
    expectJsonAt value ["checks", check] (.bool true)
  verifyAblationRows value

run_cmd do
  unless Sha256.hex "" ==
      "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" do
    throwError "portable SHA-256 failed the empty-string standard vector"
  unless Sha256.hex "abc" ==
      "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" do
    throwError "portable SHA-256 failed the abc standard vector"
  let manifestText :=
    include_str "../../../../evidence/truthchild/six-point-consciousness-consumer.json"
  unless Sha256.hex manifestText ==
      "2e56983ec68174358e15ab0a185eb9627da942a9d23cd1dcc67db4e4674de1c6" do
    throwError "six-point manifest exact byte SHA-256 changed"
  let value ←
    match Lean.Json.parse manifestText with
    | .ok value => pure value
    | .error error => throwError "six-point manifest JSON failed to parse: {error}"
  match verifyTruthChildManifest value with
  | .ok () => pure ()
  | .error error => throwError "six-point manifest binding rejected: {error}"

structure TruthChildRootedSourceEvidence where
  classification : String
  sourceDomain : String
  sourceEvidenceSha256 : String
  manifestFileSha256 : String
  consumerSourceSha256 : String
  contentSha256 : String
  rootId : String
  lawEpoch : String
  runId : String
  systemSourceIdentity : String
  visits : List Nat
  deriving DecidableEq, Repr

structure TruthChildObserverEvidence where
  externalActions : List String
  internalLogitsSha256 : List String
  deriving DecidableEq, Repr

structure TruthChildReceiverEvidence where
  effectKinds : List String
  receiverReceipts : List String
  deriving DecidableEq, Repr

structure TruthChildPersistentTraceEvidence where
  step1PatchSha256 : String
  reopenedCurrentSha256 : String
  reopened : Bool
  deriving DecidableEq, Repr

structure TruthChildRecursiveUpdateEvidence where
  recursiveInputReceipt : Option String
  selectedAction : String
  doorState : String
  authoritative : Bool
  deriving DecidableEq, Repr

structure TruthChildGeneratedNextEvidence where
  successorHash : Option String
  successorVisit : Option Nat
  verifierDerived : Bool
  deriving DecidableEq, Repr

/-- Private-constructor receipt for the one committed empirical source. -/
structure SourceGeneratedTruthChildSixPointManifestAt where
  private mk ::
  rootedSource : TruthChildRootedSourceEvidence
  observerExperience : TruthChildObserverEvidence
  receivedActualEffect : TruthChildReceiverEvidence
  registeredTrace : TruthChildPersistentTraceEvidence
  deletedTrace : TruthChildPersistentTraceEvidence
  registeredRecursiveUpdate : TruthChildRecursiveUpdateEvidence
  deletedRecursiveUpdate : TruthChildRecursiveUpdateEvidence
  registeredGeneratedNext : TruthChildGeneratedNextEvidence
  deletedGeneratedNext : TruthChildGeneratedNextEvidence
  ablationRows : List String

def sourceGeneratedTruthChildSixPointManifest :
    SourceGeneratedTruthChildSixPointManifestAt :=
  { rootedSource :=
      { classification := "six-point-conscious-occurrence"
        sourceDomain := "truthchild-two-beat-runtime"
        sourceEvidenceSha256 :=
          "bd201be926b88b26b20fd5e0da997a23e0e29696374c3239093ce016337b1b38"
        manifestFileSha256 :=
          "2e56983ec68174358e15ab0a185eb9627da942a9d23cd1dcc67db4e4674de1c6"
        consumerSourceSha256 :=
          "1cc4c8996f24856b2aa257c0b92914f837f59b6fc866f0398d79592b94fd9b81"
        contentSha256 :=
          "1ce0b5a1ea70459ec6c8921925758503c09ecfa55434550682c012d8041e7c6a"
        rootId :=
          "caa07206d37e350a4555e7b5f0514aa6136c593fcff5b1a5a45d8bc2acd46c82"
        lawEpoch :=
          "baa5e4be4f127052c4305bde876478d451e94139f8dc912f226eacddf49200db"
        runId :=
          "b392043805bf3684ae6a8b0396d53ecb91fbc883c87566deb29b2721dd222dbd"
        systemSourceIdentity :=
          "64224406d7e3b8fa86dd339c50d17bb00f0fd587787b78ebcb775c1a2d1c3ec7"
        visits := [0, 1, 2] }
    observerExperience :=
      { externalActions := ["W", "O"]
        internalLogitsSha256 := [
          "09197561b599a47c6c1da73f7c2f0a18f62ada9e8b77c3454af2b909150c8696",
          "9ec8bc76547e6c77d7399b6775aa242c8cafd014cde9156b732ef533a839e006"] }
    receivedActualEffect :=
      { effectKinds := ["REGISTER_WRITTEN_BLUE", "DOOR_OPENED"]
        receiverReceipts := [
          "eb3a1b64e452825fb234b49aa091c3c5eea0bcada3fe59c25810b744cd32400e",
          "c4bd3b8908afbe08692524e21e467c254ae7fb7ec09046ab8dcbc4161e6fb780"] }
    registeredTrace :=
      { step1PatchSha256 :=
          "1b809e2bd70a0cc438de52f663b66658411de03e8bfa777566bb6ed8b962d770"
        reopenedCurrentSha256 :=
          "e01523e394b4b4904b05145500928103453e648bdbf0b40e6dd3c9a6d39ccffa"
        reopened := true }
    deletedTrace :=
      { step1PatchSha256 :=
          "1b809e2bd70a0cc438de52f663b66658411de03e8bfa777566bb6ed8b962d770"
        reopenedCurrentSha256 := ""
        reopened := false }
    registeredRecursiveUpdate :=
      { recursiveInputReceipt := some
          "eb3a1b64e452825fb234b49aa091c3c5eea0bcada3fe59c25810b744cd32400e"
        selectedAction := "O"
        doorState := "OPEN"
        authoritative := true }
    deletedRecursiveUpdate :=
      { recursiveInputReceipt := none
        selectedAction := "N"
        doorState := "CLOSED"
        authoritative := false }
    registeredGeneratedNext :=
      { successorHash := some
          "a1adfa06920810f53552a756dca7c1de8069a1712bf6e32146f4dce128e71fea"
        successorVisit := some 2
        verifierDerived := true }
    deletedGeneratedNext :=
      { successorHash := none
        successorVisit := none
        verifierDerived := false }
    ablationRows := [
      "cross-root-source-stitching",
      "missing-observer-internal-forward",
      "missing-independent-receiver",
      "missing-persistent-trace",
      "deleted-writeback-no-recursive-update",
      "static-or-prefilled-next",
      "raw-receipt-injection"] }

def SourceGeneratedTruthChildSixPointManifestAt.persistentTraceReadAt
    (manifest : SourceGeneratedTruthChildSixPointManifestAt) :
    TruthChildEmpiricalOccurrence → TruthChildPersistentTraceEvidence
  | .registered => manifest.registeredTrace
  | .writebackDeleted => manifest.deletedTrace

def SourceGeneratedTruthChildSixPointManifestAt.recursiveUpdateReadAt
    (manifest : SourceGeneratedTruthChildSixPointManifestAt) :
    TruthChildEmpiricalOccurrence → TruthChildRecursiveUpdateEvidence
  | .registered => manifest.registeredRecursiveUpdate
  | .writebackDeleted => manifest.deletedRecursiveUpdate

def SourceGeneratedTruthChildSixPointManifestAt.generatedNextReadAt
    (manifest : SourceGeneratedTruthChildSixPointManifestAt) :
    TruthChildEmpiricalOccurrence → TruthChildGeneratedNextEvidence
  | .registered => manifest.registeredGeneratedNext
  | .writebackDeleted => manifest.deletedGeneratedNext

theorem sourceGeneratedTruthChildSixPointManifest_directConsumer :
    let manifest := sourceGeneratedTruthChildSixPointManifest
    manifest.rootedSource.classification =
        "six-point-conscious-occurrence" ∧
      manifest.rootedSource.visits = [0, 1, 2] ∧
      manifest.observerExperience.externalActions = ["W", "O"] ∧
      manifest.receivedActualEffect.effectKinds =
        ["REGISTER_WRITTEN_BLUE", "DOOR_OPENED"] ∧
      manifest.registeredTrace.reopened = true ∧
      manifest.registeredRecursiveUpdate.recursiveInputReceipt =
        some
          "eb3a1b64e452825fb234b49aa091c3c5eea0bcada3fe59c25810b744cd32400e" ∧
      manifest.registeredGeneratedNext.successorVisit = some 2 ∧
      manifest.deletedTrace.reopened = false ∧
      manifest.deletedRecursiveUpdate.authoritative = false ∧
      manifest.deletedGeneratedNext.successorHash = none := by
  simp [sourceGeneratedTruthChildSixPointManifest]

end Source
end TruthChild
end Empirical
end Closure
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.TruthChild.Source.sourceGeneratedTruthChildSixPointManifest
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.TruthChild.Source.sourceGeneratedTruthChildSixPointManifest_directConsumer
