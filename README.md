# UFPL - Unified Formal Philosophy Language (Lean 4)

UFPL is a **typed, multi‑modal logic** embedded in Lean 4. It gives you:
- multi‑sorted **terms** and **formulas** (individuals, agents, actions, worlds, time),
- **modalities** (alethic `□/◇`, epistemic `K/B`, deontic `Obl`, temporal `G/F/H/P`),
- a standard **Kripke/relational semantics** (`sat` over `Prop`),
- and a finite, executable **Boolean semantics** (`satB`) for quick model checks.

This repository includes two illustrative examples:
1. **Necessity of Identity** (Kripke): a short proof that `a = b → □(a = b)` for rigid names.
2. **Trolley**: a small deontic model with outcome worlds and a Boolean evaluator.

## Quick start

**Requirements**
- Lean 4 toolchain (pinned): `leanprover/lean4:v4.25.0`
- Lake build tool (comes with the Lean toolchain)

```bash
# Build the library and the demo executable
lake build

# Run the demo
lake exe ufpl
```

**Expected output (shape)**

```
UFPL demo:
  Facts□@w0 (Bool):          true
  LesserEvil@w0 (Bool):      true
  ObligationToDivert (Bool): true
  Necessity of identity theorem compiled (see Examples/NecIdentity.lean).
```

> The first three lines come from the Trolley example (Boolean semantics).
> The last line indicates the Necessity‑of‑Identity proof compiled successfully.

## Repository layout

```
.
├── lakefile.toml          # Lake (TOML) project file
├── lake-manifest.json     # Lake dependency lockfile (generated)
├── lean-toolchain         # Toolchain pin (Lean 4 version)
├── Main.lean              # Executable entry point (prints example results)
├── README.md
├── UFPL.lean              # Library root (re-exports core)
└── UFPL
   ├── Core
   │  ├── Types.lean       # Sorts, symbol signatures, hetero lists (HList)
   │  ├── Syntax.lean      # Terms and Form (with modalities)
   │  ├── Semantics.lean   # Kripke/temporal/deontic semantics: `sat` / `validIn`
   │  └── EvalBool.lean    # Finite Boolean semantics: `EvalSupport`, `satB`
   └── Examples
      ├── NecIdentity.lean # a=b → □(a=b) with rigid constants
      └── Trolley.lean     # deontic example + finite Bool evaluator
```

### Lake configuration (excerpt)

`lakefile.toml`:

```toml
name = "ufpl"
version = "0.1.0"
defaultTargets = ["ufpl", "UFPL"]

[[lean_lib]]
name = "UFPL"

[[lean_exe]]
name = "ufpl"
root = "Main"
```

Toolchain pin (Lean):

```
leanprover/lean4:v4.25.0
```

## What’s in the core

### Types & symbols

* **Sorts** (`Ty`): `ind` (individuals), `agt` (agents), `act` (actions/events), `wld` (object‑language worlds if needed), `tim` (times).
* **Symbols**: `ConstSym`, `FuncSym`, `PredSym`, grouped in a `Signature`.
* **HList**: typed, heterogeneous lists for symbol arguments.

### Syntax

* **Terms**: variables, constants, function application.
* **Formulas**: propositional connectives, equality, quantifiers, and modalities:

  * `box / dia`  → `□/◇`
  * `knows / believes`  → `K_a/B_a`
  * `obl`  → `Obl`, with derived `perm`, `forb`
  * `G/F/H/P`  → temporal “always/eventually” (future/past)
* Scoped notations:

  ```lean
  scoped notation "□" φ => UFPL.Core.Form.box φ
  scoped notation "◇" φ => UFPL.Core.Form.dia φ
  ```

### Semantics

* **Prop semantics (`sat`)**: `sat M w t ρ φ : Prop` with a model `M`

  * Model fields: domains per sort, worlds `W`, times `T` with `le`, alethic `Rbox`,
    epistemic/doxastic `RK/RB`, and deontic `ideal`.
  * Interprets predicates as `W → T → args → Prop`.

* **Boolean semantics (`satB`)** (finite execution):

  * `EvalSupport` provides finite `worlds`, `times`, and per‑sort domains, plus Boolean adapters for `Rbox`, `ideal`, `RK`, `RB`, `le`, and atomic predicates.
  * `satB` mirrors `sat` but returns `Bool`, enabling quick `lake exe` runs.

> Use `sat` for proofs and meta‑theory; use `satB` for quick checks on finite frames.

## The examples

### 1) Necessity of Identity (UFPL/Examples/NecIdentity.lean)

* Constants `H` and `P` for Hesperus/Phosphorus.
* UFPL formula: `H = P → □(H = P)`.
* Lean theorem:

  ```lean
  theorem necIdentity_HP_valid {Sig : Signature} (M : Model Sig) :
    validIn M NecId_HP := by
    intro w t ρ h
    intro w' _R
    simpa [sat, NecId_HP] using h
  ```

  Because constants are interpreted rigidly in the core semantics, equality is world‑independent.

### 2) Trolley (UFPL/Examples/Trolley.lean)

* Three worlds: decision `w0`, outcomes `wD` (divert), `wN` (no divert).
* Outcome facts (e.g., `Divert → Kill1 ∧ ¬Kill5`) and a “lesser evil” obligation (avoid 5 deaths).
* Boolean support `E` enumerates the **finite** worlds/times and provides Boolean adapters.
* `Main.lean` prints:

  * `□facts @ w0` (the outcome laws as seen from the decision world),
  * `lesserEvil @ w0`,
  * and the resulting **obligation to divert**.

## How to extend

1. **Add symbols** to your `Signature` (predicates, functions, constants).
2. **Choose domains** per sort and define a **model**:

   * temporal order `le`, relations `Rbox/RK/RB/ideal`, and an interpreter for atomics.
3. **(Optional) Add `EvalSupport`** for finite `satB` runs:

   * enumerate `worlds`, `times`, and each sort’s finite domain,
   * provide Boolean versions of your relations and atomic predicate.
4. **Write formulas** using `Form` (or add macros/notation if you prefer).
5. **Evaluate** with `sat` (Prop) or `satB` (Bool), or **prove** with Lean.

## Design notes & limitations

* **Typed by construction**: UFPL’s sorts prevent category mistakes (e.g., you can’t apply a person‑predicate to an action).
* **Modalities are parametric in the frame**: pick frame conditions (T/S4/S5, D for deontic, etc.) by restricting your relations; UFPL’s core leaves this open.
* **Boolean semantics** (`satB`) is an **executable** approximation that requires finite supports; quantifiers range over the listed elements.
* This repo focuses on **semantics and examples**. A full **proof system** (ND/sequent) and macros for a surface language are natural next steps.

## Development

* Build library & examples: `lake build`
* Run demo: `lake exe ufpl`
* Toolchain pin: `leanprover/lean4:v4.25.0` (see `lean-toolchain`)
* Consider adding a `.gitignore` with:

  ```
  .lake/
  lake-packages/
  build/
  ```

## Acknowledgments / License

* Logic design inspired by standard modal/temporal/deontic/epistemic frameworks.
* License: MIT 

*Questions or ideas?* Open an issue or start a discussion in your fork.
