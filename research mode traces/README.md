# Research Mode Traces

This directory stores the raw artifacts produced by the research-mode pipeline across three topics: convex optimization, graph theory, and sphere packing. Each topic folder contains the prompts, generated conjectures, novelty screening output, and multi-iteration proof attempts collected during the run. The files are traces, so they intentionally preserve the original language-model transcripts.

## Directory Overview

- `chosen_convex_result.json`, `chosen_graph_result.json`, `chosen_sphere_result.json` store the champion statement and rendered proof that survived filtering for each topic.
- `convex optimization traces/` holds all trace data for the convex optimization runs (folder name contains spaces, so quote it on the command line).
- `graph traces/` captures the graph theory exploration focused on neighbor-sum distinguishing edge weightings.
- `sphere traces/` contains the sphere packing research session, including lattice constructions.

## Shared artifacts inside each topic folder

| Artifact | What it captures |
| --- | --- |
| `annotations.md` | Domain conventions and shorthand prepared for the run. |
| `research_guideline.txt` | One-line theme that guided the agent (for example "graph theory"). |
| `seed_<topic>.txt` | Seed statements or proofs that anchored the exploration in that domain. |
| `literature_results.txt` | Plain-text summary of literature search snippets relevant to the topic. |
| `literature_results_with_sources.json` | Structured version of the same search results with URLs and metadata. |
| `predictions.txt` | List of all candidate conjectures generated before verification. |
| `prediction_annotations.md` | Extra definitions introduced after the initial annotations to support the predictions. |
| `novelty_details.json` | Per-prediction novelty assessment (matched statements and source URLs when found). |
| `novelty_kept.txt` / `novelty_rejected.txt` | Statements kept or discarded after the novelty filter (rejected list is present only when something was filtered out). |
| `prediction_<n>_log/statement.txt` | The exact statement that the solver attempted to prove or refute for prediction `n`. |
| `prediction_<n>_<m>_log/` | One solver run for prediction `n`, attempt `m`, containing iteration transcripts. |
| `prediction_<n>_<m>.log` | Run-level summary showing proof lengths and judge decisions per iteration. |
| `iteration_<k>.log` | Verbatim transcript for iteration `k`, including the prover output and judge feedback. |
| `final_proof.md`, `final_statement.txt` | Present only when a verifier accepted an argument; mirrors the accepted text. |

## Prediction log structure

1. Each candidate conjecture has a folder `prediction_<n>_log/` with the text of the claim and one or more solver attempts.
2. Attempts live in `prediction_<n>_<m>_log/`. The companion file `prediction_<n>_<m>.log` summarises modals such as "Judge: REJECT" or "Judge: ACCEPT" and proof lengths.
3. Within a run folder, `iteration_<k>.log` alternates blocks labelled "Prover Output" and "Verifier Feedback", providing the full dialogue for that iteration.
4. When a judge accepts a proof, the run usually finishes with a `final_proof.md` and matching `final_statement.txt` in the parent `prediction_<n>_log/` directory. Runs that never reach acceptance will omit these files.

## Topic specific notes

### `convex optimization traces/`

- Guideline: "improve gradient descent in machine learning".
- Seeds highlight conjectures about convexity of gradient descent trajectories and robustness to noise (`seed_convex.txt`).
- Several runs explore variants of the proximal or implicit gradient method; `prediction_7_log` and similar folders include accepted proofs with `final_proof.md`.

### `graph traces/`

- Guideline: "graph theory" with emphasis on neighbor-sum distinguishing three-edge weightings (see `seed_graph.txt`).
- Contains both `novelty_kept.txt` and `novelty_rejected.txt`, documenting which conjectures were considered genuinely new.
- Many predictions (1 through 14) were attempted; each run is rich with judge feedback that references parity profiles, reconfiguration graphs, and related notions.

### `sphere traces/`

- Guideline: "sphere packing in Euclidean spaces".
- Seeds describe high-density lattices and energy bounds (`seed_sphere.txt`).
- Only a few novelty rejections appear; most conjectures were pursued, leading to dense lattice constructions and Markov chain analyses.

## Usage tips

- Expect raw LaTeX macros (`\mathbb`, `\Delta`, etc.) and occasional garbled symbols. They mirror the model output; refer back to the logs if a symbol looks suspicious.
- Paths such as `backend\seeds\...` in the summaries indicate the original sandbox location during the run; they are informational only.
- To trace the evolution of a claim, start with `predictions.txt`, locate the matching `prediction_<n>_log/statement.txt`, then walk through the run summaries and iteration transcripts.
- The `chosen_*_result.json` files reproduce the final statement and proof for quick reference; the underlying derivation can be audited inside the corresponding topic folder.
