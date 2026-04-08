# Merits Graph Workflow

These instructions describe how to build a merits graph for one `arb` run packet.  The canonical artifact is JSON.  The Mermaid file is a readable projection of that JSON, and the PNG is a generated preview.  The graph files belong in the packet directory under `out/`, beside `run.json`, `digest.md`, and `transcript.md`.  The schema note is [Merits Graphs](../../arb/docs/merits-graphs.md).

Work from `arb/` as the current working directory.  The packet inputs are the run directory under `out/`, especially `run.json`, `digest.md`, and `transcript.md`.  `run.json` gives the complaint, technical reports, vote tally, and full event history in one file.  `digest.md` and `transcript.md` are easier to read when you are normalizing claims and checking whether a proposition is stated directly or only implied.

Read the complaint before you draft the graph.  In many runs, the decisive structure comes from the complaint's own properties: source control, criteria, carve-outs, fallback rules, and expiration.  If those properties drove the filings or the votes, represent them as separate rule nodes instead of collapsing them into one broad rule block.

Start with the council votes, then work backward through the closings, rebuttals, and technical reports.  That reading order exposes what was operative in the decision and what remained background.  A merits graph should represent the propositions that moved the outcome, not every proposition that appeared somewhere in the packet.

## Step 1: Build the Canonical JSON

Write `<run-dir>/merits-graph.json` first.  Use the schema in [Merits Graphs](../../arb/docs/merits-graphs.md): `source`, `fact`, `rule`, `claim`, `vote`, and, when a case needs them, `issue` or other proposition nodes.  Normalize repeated propositions across openings, arguments, rebuttal, closing, and council votes into one node with multiple `mentions`.  A fact node should contain only a proposition that a source states.  An interpretive move such as “temporary site control satisfies seize or hold territory” belongs in a claim node.

Keep the graph smaller than the packet.  The point is to capture the live dispute, not to restate every filing.  In most runs, the graph should include only the complaint rules that matter to the outcome, the source-backed facts that the parties actually used, the competing interpretive claims, and the vote rationales that adopted or rejected those claims.  Do not infer a node that the packet cannot support.  If a filing gestures toward a thought but never states it cleanly, omit it or record a narrower proposition.

Use documentary sources as source nodes.  A White House release, a transcript, a report, or an exhibit belongs in the source layer.  A party filing usually does not.  The filing belongs in `mentions`, because it is the place where a party used or interpreted the source-backed material.  If a graph mixes documentary sources with advocacy filings in the same source block, the provenance will become opaque.

Keep fact nodes literal.  A fact node can say that the White House described a two-hour capture mission, or that a transcript described secured routes and landing zones.  A fact node should not say that those facts established territorial occupation or satisfied the objective requirement.  That second proposition is a claim.  If the graph blurs that line, it will overstate how much the record itself resolved.

Represent shared premises when the votes show consensus on an element.  If both sides and all council members accepted entry, combat, or timing, the graph should capture that as a shared claim or premise node rather than forcing it into one side's column.  That keeps the graph focused on the real point of dispute and stops the diagram from pretending that every element remained contested.

Treat complaint-property rules as legal pivots, not scenery.  If the votes turn on the source rule, the carve-out, the fallback rule, or the expiration line, connect claims and vote rationales to those rule nodes directly.  A generic rule node such as “blueprint” hides the structure that the council actually used.

## Step 2: Build the Mermaid View

Write `<run-dir>/merits-graph.mmd` from the JSON, not from the packet.  The Mermaid file is a view for readers, so it can simplify layout and reverse some edge directions for legibility.  A view may point from claims to votes with `adopted by` labels even though the JSON keeps `vote -> claim` adoption edges.  That is acceptable because the JSON remains the canonical structure.

The Mermaid view should read left to right.  In the current layout, sources feed facts, facts and complaint rules feed the competing claims, votes adopt the claims, and the final proposition node receives only vote input.  Avoid orphaned abstraction nodes.  If an `issue` node does not clarify the dispute, leave it out of the Mermaid view even if the JSON schema allows it.

The view should show what was operative without forcing every node type into the diagram.  Use an `issue` node only when it clarifies the dispute and remains connected to the legal and factual structure.  If the competing claims and rule nodes already make the dispute legible, omit the issue node.  If a rule mattered only as background and no claim or vote turned on it, leave it out of the Mermaid view even if it remains in the JSON.

## Step 3: Render the PNG

Render the Mermaid view only after the JSON and Mermaid files are stable.  From `arb/`, run:

```bash
../common/tools/gendiagram.sh \
  out/ex6-demo/merits-graph.mmd \
  out/ex6-demo/merits-graph.png
```

Replace the `ex6-demo` path with the packet you are working on.  The helper requires `mmdc` and a local Chromium binary.  The PNG is a generated artifact for inspection.  Do not commit it unless there is a specific reason to check in the rendered image.

## Review Pass

Review the graph against the packet before treating it as done.  First, every fact node should trace to a documentary source, not to a party's interpretation of the source.  Second, every rule node should correspond to a complaint property that mattered to the dispute.  Third, the graph should make clear which elements were shared premises and which remained contested.  Fourth, every claim node should be a live dispute proposition rather than a paraphrase of a whole paragraph.  Fifth, the vote nodes should reflect what the council members actually adopted, not what you think they should have adopted.  Sixth, the Mermaid view should preserve the structure of the JSON while remaining readable as one left-to-right argument map.

Run one last negative check before you stop.  Ask which facts, rules, or claims in the graph could disappear without changing the explanation of the result.  If a node can disappear without loss, it probably was not operative and should be cut.  Then ask the converse question: which complaint property or vote rationale would make the graph misleading if omitted?  If the answer is non-empty, the graph is still missing structure.
