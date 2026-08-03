# Pi Container Image

`service/pi-container/` builds the local Podman image used by the service-owned ADC, ARB, and AARD launchers.  Each launcher starts Pi containers directly, mounts a private agent home directory, writes the Pi and MCP configuration there, and supplies the current role instructions.  The image installs the pinned Pi MCP adapter at `/opt/pi-extensions/pi-mcp-adapter/node_modules/pi-mcp-adapter` and uses `agentcourt-pi-sandbox` as its default name.

## Files

| Path | Purpose |
| --- | --- |
| `Dockerfile` | Builds a local image with upstream Pi, the pinned Pi MCP adapter, and runtime dependencies. |
| `build-image.sh` | Runs `podman build` for the local image. |

## Build

Run `./build-image.sh` from `service/pi-container/`.  From the repository root, run `service/pi-container/build-image.sh`.  Set `PI_CONTAINER_IMAGE` to override the default tag.

```bash
./build-image.sh
PI_CONTAINER_IMAGE=my-pi-agent ./build-image.sh
```

## Runtime Use

The three live-agent commands use the image for Pi jurors or council members.  Each agent receives a private `/home/user` mount containing its settings, MCP server configuration, model request, and role instructions.  The launcher selects another image when its `--pi-image` option is set.

| Runtime | Agent role | Default adapter |
| --- | --- | --- |
| `adc-run` | Jurors | `/opt/pi-extensions/pi-mcp-adapter/node_modules/pi-mcp-adapter` |
| `aar-run` | Council members | `/opt/pi-extensions/pi-mcp-adapter/node_modules/pi-mcp-adapter` |
| `aard-run` | Council members | `/opt/pi-extensions/pi-mcp-adapter/node_modules/pi-mcp-adapter` |

Pi agents require the provider credentials named by their pool entries.  Current pool records use OpenRouter and therefore require `OPENROUTER_API_KEY`.  The records also supply the model, endpoint constraints, request parameters, and persona path.
