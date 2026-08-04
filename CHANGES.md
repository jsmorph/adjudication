# Changes

## August 2, 2026

### Core and service branch split

The `service` branch now owns the ADC, ARB, and AARD multi-case services, MCP adapters, local-agent launchers, attested execution, Docker deployment, and web programs.  These programs use installed core executables from a selected `carve` revision through documented process, HTTP, and artifact interfaces.  The branch removed the duplicated procedure engines, proofs, one-case runtimes, rules, examples, evals, proof experiments, and research material after the service packages passed without their implementation packages.

The three attested image builds accept full core and service commit IDs, verify both checkouts, and compile them in separate stages.  The local launchers start `adc case` or `adc scenario`, `aar case`, and `aard case`, then connect service-owned MCP adapters and agent processes to the core Role APIs.  Compatibility tests exercise the command and HTTP boundary with explicit core binaries and a core checkout.

The retained Lean projects and all three attested build stages moved to Lean 4.32.0 before core source left this branch.  The proof migration matches `carve@e887cc3e0379b5a3eb9892a4183b6e6259d75305`.  Subsequent service commits retain only the image builders' 4.32.0 installation pins.

## July 23-24, 2026

### Web programs

`adjudication-report` provides a read-only view over configured run-output trees, including run summaries, events, votes, artifacts, rendered Markdown, structured data, and range-served raw files.  `adjudication-manage` starts and controls ARB Clerk, attested, and direct cases through the service API, while `adjudication-web` operates all three Clerk services.  The web programs use service APIs or configured filesystem roots and hold no case state.
