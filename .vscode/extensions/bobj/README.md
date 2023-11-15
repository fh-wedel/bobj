## VS Code extension: Syntax Highlighting definition for the BOBJ algebraic specification language

uho 2023-11-15

### Installation

From the VS Code *Command Palette* (search for *VSIX*,) use the command `Extension: Install from VSIX` and point it to `bobj-x.y.z.vsix`

### Repackage the .vsix extension file

```bash
> cd .vscode/extensions/bobj
> vsce package
```

This creates `bobj-x.y.z.vsix`

(Get `vsce` with `npm install -g @vscode/vsce`)

### Customize

You can add entries to the user's `settings.json` to customize the colors. For example:

```json
{
    "editor.tokenColorCustomizations": {
        "textMateRules": [
            {
                "scope": "keyword.operator.bobj",
                "settings": {
                    "foreground": "#9090FF"
                }
            }
        ]
    },
    "workbench.colorTheme": "Monokai"
}
```