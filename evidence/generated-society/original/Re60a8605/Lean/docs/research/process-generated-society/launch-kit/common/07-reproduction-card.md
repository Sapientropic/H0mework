# Independent Reproduction Card

> **Editorial draft - minimal cold-check protocol.** Replay the accepted mouths; do not reconstruct
> the proof or invent a parallel test ontology.

## Page 1 of 2 - Cold checkout and the production sink

### Fixed checkpoint and current release gate

```text
commit: 36a54b2c2eb67f116158af2ff920eab9d62d1c65
subject: society: close universal root law and U8 availability
Lean:    4.33.0
```

The configured authoring remote does not yet resolve this checkpoint. Public circulation is
therefore blocked until `PUBLIC_REPOSITORY_URL` and `PUBLIC_RELEASE_TAG` both contain that exact
commit. During editorial QA, the sequence below was tested in a true `--no-local` clone with no
pre-existing repository `.lake/`; that validates the build path, not public access.

### Cold checkout and dependency preparation

```bash
git clone --no-local PUBLIC_REPOSITORY_URL Homework
cd Homework
git merge-base --is-ancestor \
  36a54b2c2eb67f116158af2ff920eab9d62d1c65 PUBLIC_RELEASE_TAG
git checkout --detach 36a54b2c2eb67f116158af2ff920eab9d62d1c65
cd Lean
lake env lean --version
lake exe cache get
```

The first `lake env lean` invocation installs the pinned package revisions when `.lake/packages/`
is absent; `lake exe cache get` prepares the pinned Mathlib cache. A PDF that still contains either
public placeholder is not release-ready.

### Build the production whole sink

```bash
lake build SaturationMonoid.ProcessGame.Regression.Society.M14.M14WholeProgramRegression
```

This is the necessary cold-build step missing from the earlier card: direct `lake env lean FILE`
does not by itself promise to build every absent imported `.olean`.

<div style="page-break-after: always;"></div>

## Page 2 of 2 - Trust-zero replay without reconstruction

### Replay the two trust-zero consumers

```bash
ROOT_LAW_CONSUMER="SaturationMonoid/ProcessGame/Regression/Society/M14/"\
"Fixture/EssentialAccess/ActualUpdate/Selection/Append/CrossCompiler/"\
"Readout/Recognition/Admission/Constitution/RootLaw/Completion/Consumer/"\
"ProofCarryingCanonicalSocietyRootLawComplete.lean"
lake env lean --trust=0 -DwarningAsError=true "$ROOT_LAW_CONSUMER"

lake env lean --trust=0 -DwarningAsError=true \
  SaturationMonoid/ProcessGame/Regression/Society/M14/M14WholeProgramRegression.lean
```

Success means both exit with code `0`, warnings remain fatal, and the reported final spectrum is:

```text
[propext, Classical.choice, Quot.sound]
```

### Claim-specific optional replay

Only a reader auditing Σ adoption or the universe-polymorphic observer maximum needs these two
additional focused consumers:

```bash
lake env lean --trust=0 -DwarningAsError=true \
  SaturationMonoid/ProcessGame/Regression/Society/M13/M13WholeProgramRegression.lean

OBSERVER_CONSUMER="SaturationMonoid/ProcessGame/Regression/Society/M14/"\
"Consumer/Root/Universal/Observer/"\
"ProofCarryingUniversalObserverConsumerExhaustionRegression.lean"
lake env lean --trust=0 -DwarningAsError=true "$OBSERVER_CONSUMER"
```

Both report `[propext, Classical.choice, Quot.sound]`. They are verification routes, not requests to
rebuild the M13 or observer ontologies.

### No-rework boundary

The [Regression Reuse Manifest](08-regression-reuse-manifest.md) names the existing producers,
direct consumers, and counterexamples. Independent review should replay or attack those mouths, not
rebuild lineage, UBI, observer kernels, refusal recourse, cofinal dynamics, or four-class exhaustion.
