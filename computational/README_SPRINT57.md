# Sprint 5.7: Diagnostic Re-run Documentation

## Overview

Sprint 5.7 enhances the certification script with diagnostic logging to distinguish between **geometric obstruction (hard wall)** and **certification polishing failure**. This enables scientific interpretation of 0% certification rates seen in Sprint 5.6.

## Key Enhancements Over Sprint 5.6

### 1. Preserved `insertion_details`
- **Before:** `insertion_details` was stripped from JSON output (line 795)
- **After:** Full forensic trail preserved in saved results
- **Impact:** Can analyze where each insertion attempt failed

### 2. Enhanced Diagnostic Fields

**Per-seed fields added:**
- `best_approach_min_gap`: Best gap found during approach phase (across all insertion attempts)
- `best_approach_max_rad_err`: Maximum radial error in best approach configuration
- `best_approach_gap_violations`: Number of gap violations in best approach
- `best_postcert_min_gap`: Best gap after certification retry (if applicable)
- `failure_stage`: Where failure occurred (`no_path`, `approach_only`, `cert_retry_fail`, or `None` for success)
- `achieved_loose`: Whether configuration passes with `eps_g = 1e-3` (loose threshold)

**Per-insertion fields added:**
- `best_approach_min_gap`: Best gap for this specific insertion attempt
- `best_approach_max_rad_err`: Radial error in best approach
- `best_approach_gap_violations`: Gap violations in best approach
- `best_postcert_min_gap`: Gap after certification retry (if retry failed)
- `failure_stage`: Stage where this insertion failed

### 3. Failure Stage Tracking

The script now tracks where failures occur:
- `no_path`: No viable approach path found (all seam directions failed)
- `approach_only`: Approach succeeded but certification failed (no retry attempted or retry not applicable)
- `cert_retry_fail`: Approach succeeded, certification retry attempted but failed
- `None`: Success (either immediate certification or after retry)

### 4. Achieved Loose Check

Added `achieved_loose` counter that checks if configuration passes with `eps_g = 1e-3` (100× looser than strict `1e-5`). This helps identify near-misses that might be certifiable with continuation methods.

## Configuration

**New config parameters:**
```python
"loose_eps_g": 1e-3,         # Loose threshold for achieved_loose check
"n_seeds_diagnostic": 10,    # Reduced seeds for diagnostic run
```

**Default diagnostic run:**
- N values: [41, 42] only
- Seeds: 10 (vs 50 in full run)
- Expected runtime: 5-10 minutes

## Usage

### Diagnostic Run (Default)
```python
python sprint57_diagnostic.py
```

This runs the diagnostic suite with:
- N=41, N=42
- 10 seeds per N
- Enhanced diagnostic output

### Full Run (Original)
```python
# Modify CONFIG or call directly:
all_results, all_summaries = run_full_certification_suite(config=CONFIG)
```

## Interpretation Guide

### Distinguishing Case A vs Case B

**Case A (Geometric Obstruction - Hard Wall):**
- `best_approach_min_gap` is strongly negative: `< -1e-2` (e.g., -0.05, -0.1)
- `best_approach_gap_violations` is high (many overlapping pairs)
- `achieved_loose` is `False` (doesn't even pass loose threshold)
- **Interpretation:** Likely geometric impossibility → strong evidence for τ₅ = 40

**Case B (Polishing Failure):**
- `best_approach_min_gap` is near-miss: `> -1e-4` (e.g., -1e-5, -5e-6)
- `best_approach_gap_violations` is low (few violations)
- `achieved_loose` is `True` (passes loose threshold)
- `failure_stage` is `cert_retry_fail` or `approach_only`
- **Interpretation:** Certifier too strict → τ₅ might still be > 40, needs continuation

### Failure Stage Distribution

Analyze `failure_stage` across all seeds:
- Mostly `no_path`: Search space too constrained, need different insertion strategy
- Mostly `approach_only`: Approach finds good configs but certification fails → polishing problem
- Mostly `cert_retry_fail`: Retry helps but not enough → needs continuation schedule

### Gap Analysis

**Best approach gaps:**
- If median `best_approach_min_gap` < -1e-2 → hard wall
- If median `best_approach_min_gap` > -1e-4 → polishing failure
- If `achieved_loose` rate >> `certified` rate → tolerance too strict

## Example Analysis

After running, examine JSON results:

```python
import json
with open('sprint57_results/results_N41.json') as f:
    data = json.load(f)

# Extract diagnostic fields
for result in data['results']:
    print(f"Seed {result['seed']}:")
    print(f"  best_approach_min_gap: {result.get('best_approach_min_gap')}")
    print(f"  achieved_loose: {result.get('achieved_loose')}")
    print(f"  failure_stage: {result.get('failure_stage')}")
    print(f"  insertion_details: {len(result.get('insertion_details', []))} attempts")
```

## Next Steps Based on Results

### If Case B (Polishing Failure) Dominates:
→ **Sprint 5.8**: Implement certification continuation schedule
- Certify at `eps_g = 1e-2` → feed into `eps_g = 1e-3` → `eps_g = 1e-4` → `eps_g = 1e-5`
- Decreasing step size, increasing iterations per stage

### If Case A (Hard Wall) Dominates:
→ **Sprint 5.9**: Search-space falsification
- Try global search (random 41 points + repulsion) instead of D₅-insertion
- Or allow intruder direction to move tangentially during relaxation
- If still no near-misses → strong computational evidence for τ₅ = 40

## Output Files

- `sprint57_results/results_N41.json`: Full diagnostic results for N=41
- `sprint57_results/results_N42.json`: Full diagnostic results for N=42
- Each result includes complete `insertion_details` with full forensic trail

## Differences from Sprint 5.6

| Feature | Sprint 5.6 | Sprint 5.7 |
|---------|------------|------------|
| `insertion_details` | Stripped | Preserved |
| `best_approach_min_gap` | Not saved | Saved per-seed |
| `best_approach_max_rad_err` | Not saved | Saved per-seed |
| `best_approach_gap_violations` | Not saved | Saved per-seed |
| `best_postcert_min_gap` | Not saved | Saved per-seed |
| `failure_stage` | Not tracked | Tracked |
| `achieved_loose` | Not checked | Checked with eps_g=1e-3 |
| Certification retry diag | Discarded | Captured |

## Scientific Value

These enhancements transform "0% certified" from an uninterpretable result into a diagnostic that can distinguish:
1. **Fundamental geometric impossibility** (hard wall)
2. **Optimization/certification limitations** (polishing failure)

This is critical for determining whether τ₅ = 40 (hard wall) or τ₅ > 40 with certification challenges (polishing failure).
