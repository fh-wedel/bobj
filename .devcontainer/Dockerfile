FROM debian:bullseye-slim

# Avoid prompts from apt.
ENV DEBIAN_FRONTEND=noninteractive

# This sets up a basic environment.

RUN apt-get update && apt-get install -y \
    git \
    rlwrap \
    curl \
    # for reqbuilding also install  default-jdk maven \
    # You can include other necessary tools here, depending on your development needs.
    && apt-get autoremove -y \
    && apt-get clean -y \
    && rm -rf /var/lib/apt/lists/*

RUN curl https://github.com/fh-wedel/bobj/raw/codespace/.vscode/extensions/bobj/bobj-0.1.6.vsix >/root/bobj-0.1.6.vsix

# Set the default shell to bash instead of sh
ENV SHELL /bin/bash
