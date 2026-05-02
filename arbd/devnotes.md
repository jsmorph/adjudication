# Development Notes

## 2026-05-02

### Initial fork from `arb`

`arbd/` began as a bounded fork of `arb/`, but it does not preserve the binary decision model.  The fork keeps the same high-level merits sequence and the same council-member machinery.  It changes the complaint from `Question` instead of `Proposition`, changes the policy field from `judgment_standard`, and changes the deliberation act from a binary vote to one integer answer in `[0,100]`.

The final result is the answer set itself.  The runtime exports that result as a Go map keyed by `member_id`.  The engine does not compute a threshold outcome, an aggregate, or a `no_majority` result.  Closure now follows one condition: every seated council member has answered once in the round.

### Proof scope

The copied `arb` proof surface was wrong for `arbd`, because those files proved properties of threshold closure, substantive-outcome viability, and binary neutrality.  The new proof set is narrow and direct.  It proves initialization rules, ordered merits flow, bounded council answers, answer completeness on closure, and the current removal guards.

### Documentation boundary

This first version keeps the new tree small on purpose.  It has one example, one proof batch, and one Makefile demo path.  It avoids importing `arb`'s binary-vote notes and examples under misleading names.

### Example 1 refresh

The first example now uses two sonnets rather than the earlier placeholder novelty prompt.  The record states that one sonnet was written in 2024 and that a very similar but not identical sonnet was written in 2025.  That makes the example fit the degree model directly, because the council has to answer how much of the later text was really the earlier text.

### Attorney image prerequisite

The first live `arbd` case run exposed a missing local prerequisite rather than an engine defect.  The ACP attorney wrapper expects the shared Podman image `agentcourt-pi-sandbox`, and `arbd` now exposes that requirement directly through a `build-image` target and a `build: build-image` dependency.  That keeps the local setup in line with the shared `common/pi-container` path instead of relying on a prebuilt image to happen to exist.

### Council answer transport

The first live council runs exposed a transport mismatch with the shared council pool, not a Lean defect.  `arb` asks council models for a string-valued tool argument, while the first `arbd` draft asked the same mixed pool for a JSON integer.  That difference was enough to trigger repeated invalid council submissions under the normal `make demo` path.

`arbd` now matches `arb` at the tool boundary: the council tool asks for digit-only string input, and the Go runner normalizes that input to an integer before it calls the Lean engine.  The engine and the final run artifacts still store numeric answers.  After that change, `make demo` completed successfully on the sonnet example with final answers `{"C1":82,"C2":82,"C3":82,"C4":82,"C5":87}`.
