FROM debian:bullseye-slim

# Avoid prompts from apt.
ENV DEBIAN_FRONTEND=noninteractive

# This sets up a basic environment.

RUN apt-get update && apt-get install -y \
    git rlwrap curl unzip \
    # for reqbuilding also install  default-jdk maven \
    # You can include other necessary tools here, depending on your development needs.
    && apt-get autoremove -y \
    && apt-get clean -y \
    && rm -rf /var/lib/apt/lists/*


# Fetch and install VS Code BOBJ extension
RUN curl -L -o /root/bobj-0.1.6.vsix https://github.com/fh-wedel/bobj/raw/codespace/.vscode/extensions/bobj/bobj-0.1.6.vsix
RUN mkdir -p /root/.vscode-remote/extensions/ulrich_hoffmann.bobj-0.1.6 
WORKDIR /root/.vscode-remote/extensions/ulrich_hoffmann.bobj-0.1.6
RUN unzip /root/bobj-0.1.6.vsix && mv extension.vsixmanifest .vsixmanifest && mv extension/* . && rm -rf "./[Content_Types].xml" extension

# Set the default shell to bash instead of sh
ENV SHELL /bin/bash
