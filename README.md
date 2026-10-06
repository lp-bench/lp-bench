# proofbench-statements

Private.  The test-taker side of ProofBench: everything a model may see during
an evaluation, and nothing else.  Generated from the private ProofBench
repository; do not edit by hand.

## Contents

    ProofBench/PROBLEMS/Pxxx/Pxxx.lean            challenge statement (one intended sorry)
    ProofBench/PROBLEMS/Pxxx/Pxxx_DISPROVE.lean   disprove polarity, open problems only
    ProofBench/Mathlib_Problems/                  statement-layer library (definitions)
    ProofBench/DATABASE/Database.json             id, name, difficulty, MSC, statements
    SOURCE_COMMIT                                 ProofBench commit this export comes from

Not included: bounds (`_LB`, `_UB`), solutions (`_sol`), the proctor library
`ProofBench/Mathlib`, source papers, and the rest of the database.

## Regenerate

    scripts/sync_from_proofbench.py ../ProofBench --build
    git add -A && git commit -m "Sync ProofBench $(cut -c1-10 SOURCE_COMMIT)"

The script exports the last commit of ProofBench, not uncommitted changes.
It stops if a statement imports hidden material, and skips (and reports) a
library file that does.
