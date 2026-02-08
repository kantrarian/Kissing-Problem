# Proof Blueprint: [Theorem Name]

**Date:** YYYY-MM-DD
**Status:** Draft | In Progress | Complete
**Estimated complexity:** ~N lines of Lean

---

## 1. Mathematical Background

*Informal proof sketch. Write the mathematical argument in plain language before any Lean is written. This serves as the "Informal Prover" role from the Numina-Lean-Agent approach.*

**Goal:** [State the theorem informally]

**Key mathematical ideas:**
- [Idea 1]
- [Idea 2]

**Critical observations:**
- [Observation that simplifies the proof]

---

## 2. Dependency DAG

*List intermediate lemmas in dependency order. Each lemma should have a clear mathematical statement and its dependencies.*

```
[final_theorem]
  ├── [lemma_A]
  │     ├── [helper_1]
  │     └── [helper_2]
  ├── [lemma_B]
  │     └── [helper_3]
  └── [lemma_C] (from Mathlib: Exact.Name)
```

### Lemma Specifications

| Lemma | Statement (informal) | Dependencies | Strategy |
|-------|---------------------|--------------|----------|
| `helper_1` | ... | none | `native_decide` / `norm_num` / tactic proof |
| `helper_2` | ... | `helper_1` | ... |
| `lemma_A` | ... | `helper_1`, `helper_2` | ... |
| `lemma_B` | ... | `helper_3` | ... |
| `final_theorem` | ... | `lemma_A`, `lemma_B`, Mathlib | ... |

---

## 3. Mathlib API Surface

*List the Mathlib lemmas/definitions you expect to use. This reduces hallucination of nonexistent API names.*

| Mathlib Name | Purpose |
|-------------|---------|
| `PiLp.inner_apply` | Expand inner product on EuclideanSpace |
| `norm_eq_sqrt_real_inner` | Relate norm to inner product |
| ... | ... |

*Use `lean_leansearch`, `lean_loogle`, or `lean_local_search` via MCP to discover these.*

---

## 4. Computable vs. Noncomputable Boundary

*Identify which parts of the proof need `native_decide` / `decide` and which are in the noncomputable section.*

**Computable (before `noncomputable section`):**
- [Definition/lemma that must be computable]

**Noncomputable:**
- [Everything using Real, sqrt, etc.]

**Bridge lemmas** (connecting computable results to noncomputable goals):
- [Lemma that casts from Int/Nat to Real]

---

## 5. Potential Issues & Fallbacks

| Issue | Likelihood | Fallback |
|-------|-----------|----------|
| `simp` doesn't close goal | Medium | Try `norm_num`, explicit `rw` chain |
| Type coercion problems (Int → Real) | High | Use `push_cast`, `exact_mod_cast`, `Int.cast_sum` |
| `native_decide` timeout | Low | Break into smaller decidable subgoals |
| Elaboration order issues | Medium | Move computable defs before `noncomputable section` |
| ... | ... | ... |

---

## 6. Revision Log

| Revision | Date | What Changed | Why |
|----------|------|-------------|-----|
| v1 | ... | Initial blueprint | — |
| v2 | ... | Rewrote lemma_X | Build error: [description] |
