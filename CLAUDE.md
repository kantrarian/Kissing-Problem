# KissingNumber Lean 4 Project

## Project Overview

Formal verification of kissing number lower bounds in dimensions 3, 5, and 8 using explicit witness configurations (D3, D5, E8 root systems). All proofs are axiom-free (depending only on Lean kernel axioms).

## Structure

- `KissingNumber/Defs.lean` — `IsKissingConfiguration` definition
- `KissingNumber/Lemmas.lean` — Shared lemmas (`Finset.sum_eq_add_of_pair`, `dist_ge_two_of_norm_eq_two_and_inner_le_two`)
- `KissingNumber/D3.lean` — Dimension 3: 12 points (cuboctahedron)
- `KissingNumber/D5.lean` — Dimension 5: 40 points (D5 roots)
- `KissingNumber/Witness/E8.lean` — Dimension 8: 240 points (E8 roots)
- `KissingNumber/Summary.lean` — Top-level theorems

## Lean-LSP-MCP Integration

This project has Lean-LSP-MCP configured as an MCP server. When available, use these tools:

- **`lean_goal`** — Inspect proof state at a specific line. Use this BEFORE guessing what `simp` or `norm_num` produces. This is the single highest-value tool.
- **`lean_diagnostic_messages`** — Get all errors/warnings for a file without a full `lake build`.
- **`lean_multi_attempt`** — Try multiple tactic strategies at a proof node in parallel.
- **`lean_leansearch`** / **`lean_loogle`** — Search Mathlib for lemmas by natural language or pattern.
- **`lean_leanfinder`** — Semantic search for Mathlib theorems via Lean Finder.
- **`lean_state_search`** / **`lean_hammer_premise`** — Find applicable theorems for a given proof goal.
- **`lean_local_search`** — Search project + stdlib with ripgrep.
- **`lean_run_code`** — Run standalone Lean snippets (e.g., `#eval`, `#check`).

LeanDex (semantic search across Mathlib) is integrated via `leansearch_leandex` — no separate installation needed.

## Proof Development Workflow

Follow the Numina-Lean-Agent methodology:

### 1. Blueprint First
Before writing any Lean code for proofs >50 lines, create a blueprint document (see `BLUEPRINT_TEMPLATE.md`):
- Write the informal mathematical argument first
- Decompose into intermediate lemmas with an explicit dependency DAG
- Identify Mathlib API surface (use `lean_leansearch` / `lean_loogle`)
- Mark the computable/noncomputable boundary
- List potential issues and fallbacks

### 2. Iterative Refinement > Independent Sampling
When a tactic fails:
- Use `lean_goal` to see the exact proof state
- Try the fallback from your blueprint
- Do NOT blindly retry the same approach

### 3. Computable/Noncomputable Discipline
- Computable definitions (`parityBit`, `extBit`, `sgnMatchSum`) go BEFORE `noncomputable section`
- `native_decide` only works on `Decidable` propositions with computable terms
- Bridge lemmas connect computable results to noncomputable goals via `exact_mod_cast`, `push_cast`, `Int.cast_sum`

### 4. Common Patterns in This Project

**Inner product expansion:**
```lean
rw [PiLp.inner_apply]
simp only [RCLike.inner_apply, conj_trivial]
```

**Norm calculation:**
```lean
rw [norm_eq_sqrt_real_inner, h]  -- where h : ⟪v, v⟫ = c
```

**Sparse vector sums (only 2 nonzero coords):**
```lean
rw [Finset.sum_eq_add_of_pair i j h_ne]
-- Then prove rest are zero
```

**Bool case splitting:**
```lean
cases b <;> simp [sgn]
```

## Common Pitfalls

- **BEq vs Eq for Bool**: `extBit x k == extBit y k` (BEq) is not the same as `=`. Watch for commutativity issues.
- **`Finset.sum_div` ordering**: `∑ x, f x / c` requires `Finset.sum_div` which rewrites `(∑ x, f x) / c`.
- **Type coercions**: Going from `ℤ` to `ℝ` requires `Int.cast_sum` before `Finset.sum_div`. Order matters.
- **`congr` depth**: `congr 2` can produce unsolvable goals. Prefer `Finset.sum_congr rfl` + intro.
- **Elaboration order**: Lean elaborates top-down. Computable defs must appear before they're used in `native_decide` lemmas.

## Build Commands

```bash
lake build          # Full build
lake build KissingNumber.Summary  # Just the summary (imports everything)
```

## Toolchain

- Lean: `leanprover/lean4:v4.28.0-rc1`
- Mathlib: latest from git
