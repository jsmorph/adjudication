# Adjudication Web Servers

`web/` contains three separate servers.  `adjudication-web` is a server-rendered console for the ADC, ARB, and AARD service APIs: it creates cases, lists them, manages active runs, and reads results, artifacts, evidence, and attestation events through configured service base URLs.  `adjudication-report` is a read-only report over run output directories on disk: it scans configured root trees for runs and serves an index, run pages with facts, votes, and events, and views of every artifact.  `adjudication-manage` is an ARB management UI: it starts, monitors, and stops Clerk, attested, and direct cases through one `aar-service` process and links each case to its report run page.

The console and the management UI keep case state behind the service APIs, and the report reads only the filesystem.  [The web runbook](runbook.md) covers commands, configuration, page structure, limits, and troubleshooting for all three.
