# Service Documents

This directory contains the cross-branch interface specification and the ownership record used during extraction.  Procedure rules, proofs, core manuals, and acceptance fixtures live on `carve`.  Deployment and operator instructions live beside their implementations under `service/` and `web/`.

| Document | Use |
| --- | --- |
| [Core Process Interface](core-interface.md) | Core commands, process behavior, private APIs, durable artifacts, and compatibility verification. |
| [Retention Ledger](retention-ledger.md) | Approved ownership decisions and the extraction conditions used to divide the branches. |

The [ADC service manual](../service/adc/README.md), [ARB service manual](../service/arb/README.md), and [AARD service manual](../service/arbd/README.md) describe the service commands and HTTP APIs.  The attested runbooks live under `service/attested/`, beside their drivers and image definitions.  The web documents live under `web/`, beside the operator programs.
