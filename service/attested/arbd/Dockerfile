# syntax=docker/dockerfile:1

ARG CORE_REPO=https://github.com/jsmorph/adjudication.git
ARG SERVICE_REPO=https://github.com/jsmorph/adjudication.git
ARG CORE_COMMIT
ARG SERVICE_COMMIT
ARG PI_CODING_AGENT_PACKAGE=@earendil-works/pi-coding-agent@0.78.0

FROM golang:1.25-trixie AS core-build

ARG CORE_REPO
ARG CORE_COMMIT

ENV ELAN_HOME=/opt/elan
ENV PATH=/opt/elan/bin:$PATH

RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        build-essential \
        ca-certificates \
        curl \
        git \
        make \
        xz-utils \
    && rm -rf /var/lib/apt/lists/*

RUN curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh \
    && sh /tmp/elan-init.sh -y --default-toolchain leanprover/lean4:v4.27.0 \
    && rm /tmp/elan-init.sh

WORKDIR /src

RUN printf '%s\n' "$CORE_COMMIT" | grep -Eq '^[0-9a-f]{40}$' \
    && git init core \
    && cd core \
    && git remote add origin "$CORE_REPO" \
    && git fetch --depth 1 origin "$CORE_COMMIT" \
    && git checkout --detach FETCH_HEAD \
    && test "$(git rev-parse HEAD)" = "$CORE_COMMIT"

WORKDIR /src/core/arbd

RUN make build

FROM golang:1.25-trixie AS service-build

ARG SERVICE_REPO
ARG SERVICE_COMMIT

RUN apt-get update \
    && apt-get install -y --no-install-recommends ca-certificates git \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /src

RUN printf '%s\n' "$SERVICE_COMMIT" | grep -Eq '^[0-9a-f]{40}$' \
    && git init service \
    && cd service \
    && git remote add origin "$SERVICE_REPO" \
    && git fetch --depth 1 origin "$SERVICE_COMMIT" \
    && git checkout --detach FETCH_HEAD \
    && test "$(git rev-parse HEAD)" = "$SERVICE_COMMIT"

WORKDIR /src/service

RUN CGO_ENABLED=0 go build -buildvcs=false -o /out/aard-run ./cmd/aard-run

FROM debian:trixie-slim AS pi-rootfs

ARG PI_CODING_AGENT_PACKAGE

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        ca-certificates \
        curl \
        git \
        nodejs \
        npm \
        openssl \
        sudo \
    && rm -rf /var/lib/apt/lists/*

RUN npm install -g node@22.19.0 \
    && node --version \
    && npm install -g "${PI_CODING_AGENT_PACKAGE}" \
    && npm cache clean --force

RUN useradd -m user \
    && echo 'user ALL=(ALL) NOPASSWD:ALL' > /etc/sudoers.d/user

FROM pi-rootfs AS pi-export

RUN tar --numeric-owner --one-file-system \
    --exclude=./dev \
    --exclude=./proc \
    --exclude=./run \
    --exclude=./sys \
    --exclude=./tmp \
    -C / \
    -cpf /tmp/agentcourt-pi-sandbox-rootfs.tar \
    .

FROM docker:26-cli AS docker-cli

FROM debian:trixie-slim

ENV DEBIAN_FRONTEND=noninteractive
ENV AARD_PI_IMAGE=agentcourt-pi-sandbox:latest
ENV AARD_PI_ROOTFS_TAR=/opt/images/agentcourt-pi-sandbox-rootfs.tar
ENV PATH=/opt/core/arbd/.bin:/usr/local/bin:$PATH

RUN apt-get update \
    && apt-get install -y --no-install-recommends ca-certificates \
    && rm -rf /var/lib/apt/lists/*

COPY --from=docker-cli /usr/local/bin/docker /usr/local/bin/docker
COPY --from=core-build /src/core/arbd/.bin /opt/core/arbd/.bin
COPY --from=core-build /src/core/arbd/examples /opt/core/arbd/examples
COPY --from=core-build /src/core/arbd/prompts /opt/core/arbd/prompts
COPY --from=core-build /src/core/arbd/attorney-instructions /opt/core/arbd/attorney-instructions
COPY --from=core-build /src/core/common/data /opt/core/common/data
COPY --from=core-build /src/core/common/etc /opt/core/common/etc
COPY --from=service-build /out/aard-run /usr/local/bin/aard-run
COPY --from=pi-export /tmp/agentcourt-pi-sandbox-rootfs.tar /opt/images/agentcourt-pi-sandbox-rootfs.tar

RUN cat > /usr/local/bin/aard-run-entrypoint <<'EOF' \
    && chmod 755 /usr/local/bin/aard-run-entrypoint /usr/local/bin/aard-run
#!/bin/sh
set -eu

if [ -S /var/run/docker.sock ]; then
    if ! docker image inspect "$AARD_PI_IMAGE" >/dev/null 2>&1; then
        echo "Importing embedded Pi image as $AARD_PI_IMAGE" >&2
        docker import \
            --change 'ENTRYPOINT ["pi"]' \
            --change 'WORKDIR /home/user/work' \
            "$AARD_PI_ROOTFS_TAR" \
            "$AARD_PI_IMAGE" >/dev/null
    fi
fi

exec /usr/local/bin/aard-run \
    --aard-bin /opt/core/arbd/.bin/aard \
    --aard-working-dir /opt/core/arbd \
    --engine /opt/core/arbd/.bin/aardengine \
    --common-root /opt/core/common \
    "$@"
EOF

WORKDIR /opt/core/arbd

ENTRYPOINT ["/usr/local/bin/aard-run-entrypoint"]
CMD ["--help"]
