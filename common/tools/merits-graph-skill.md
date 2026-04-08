# Merits Graph Workflow

These instructions describe how to build a merits graph for one `arb` run packet.  The canonical artifact is JSON.  The Mermaid file is a readable projection of that JSON, and the PNG is a generated preview.  The current worked example is [Example 6 merits graph JSON](../../arb/examples/ex6/merits-graph.json), [Example 6 Mermaid view](../../arb/examples/ex6/merits-graph.mmd), and [the schema note](../../arb/docs/merits-graphs.md).

Work from `arb/` as the current working directory.  The packet inputs are the run directory under `out/`, especially `run.json`, `digest.md`, and `transcript.md`.  `run.json` gives the complaint, technical reports, vote tally, and full event history in one file.  `digest.md` and `transcript.md` are easier to read when you are normalizing claims and checking whether a proposition is stated directly or only implied.

## Step 1: Build the Canonical JSON

Write `<run-dir>/merits-graph.json` first.  Use the schema in [Merits Graphs](../../arb/docs/merits-graphs.md): `source`, `fact`, `rule`, `claim`, `vote`, and, when a case needs them, `issue` or other proposition nodes.  Normalize repeated propositions across openings, arguments, rebuttal, closing, and council votes into one node with multiple `mentions`.  A fact node should contain only a proposition that a source states.  An interpretive move such as “temporary site control satisfies seize or hold territory” belongs in a claim node.

Keep the graph smaller than the packet.  The point is to capture the live dispute, not to restate every filing.  In most runs, the graph should include only the complaint rules that matter to the outcome, the source-backed facts that the parties actually used, the competing interpretive claims, and the vote rationales that adopted or rejected those claims.  Do not infer a node that the packet cannot support.  If a filing gestures toward a thought but never states it cleanly, omit it or record a narrower proposition.

## Step 2: Build the Mermaid View

Write `<run-dir>/merits-graph.mmd` from the JSON, not from the packet.  The Mermaid file is a view for readers, so it can simplify layout and reverse some edge directions for legibility.  The Example 6 view, for instance, points from claims to votes with `adopted by` labels even though the JSON keeps `vote -> claim` adoption edges.  That is acceptable because the JSON remains the canonical structure.

The Mermaid view should read left to right.  In the current layout, sources feed facts, facts and complaint rules feed the competing claims, votes adopt the claims, and the final proposition node receives only vote input.  Avoid orphaned abstraction nodes.  If an `issue` node does not clarify the dispute, leave it out of the Mermaid view even if the JSON schema allows it.

## Step 3: Render the PNG

Render the Mermaid view only after the JSON and Mermaid files are stable.  From `arb/`, run:

```bash
../common/tools/gendiagram.sh \
  examples/ex6/merits-graph.mmd \
  examples/ex6/merits-graph.png
```

Replace the `ex6` path with the packet you are working on.  The helper requires `mmdc` and a local Chromium binary.  The PNG is a generated artifact for inspection.  Do not commit it unless there is a specific reason to check in the rendered image.

## Review Pass

Review the graph against the packet before treating it as done.  Check four things.  First, every fact node should trace to a documentary source or a vote rationale.  Second, every claim node should be a live dispute proposition rather than a paraphrase of a whole paragraph.  Third, the vote nodes should reflect what the council members actually adopted, not what you think they should have adopted.  Fourth, the Mermaid view should preserve the structure of the JSON while remaining readable as one left-to-right argument map.
