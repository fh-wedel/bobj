#!/bin/bash

set -x

echo "export BOBJ_HOME=/workspaces/bobj/target" >> /root/.bashrc
code --install-extension /workspaces/bobj/.vscode/extensions/bobj/bobj-0.1.6.vsix
