FROM debian:trixie-slim

RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates curl git nodejs npm openssl sudo && \
    rm -rf /var/lib/apt/lists/*

ARG PI_CODING_AGENT_PACKAGE=@earendil-works/pi-coding-agent@0.78.0
ARG PI_MCP_ADAPTER_PACKAGE=pi-mcp-adapter@2.11.0
RUN npm install -g node@22.19.0 && \
    node --version && \
    npm install -g "${PI_CODING_AGENT_PACKAGE}" && \
    npm install --prefix /opt/pi-extensions/pi-mcp-adapter "${PI_MCP_ADAPTER_PACKAGE}" --legacy-peer-deps && \
    chmod -R a+rX /opt/pi-extensions && \
    npm cache clean --force

RUN useradd -m user && echo 'user ALL=(ALL) NOPASSWD:ALL' > /etc/sudoers.d/user
USER user
WORKDIR /home/user/work
ENTRYPOINT ["pi"]
