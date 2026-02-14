# TLA+ By Example

[![CI](../../actions/workflows/ci.yml/badge.svg)](../../actions/workflows/ci.yml)

An interactive website for learning TLA+ through guided examples with an in-browser model checker.

**Live at:** [tlabyexample.com](https://tlabyexample.com)

## What is this

A Next.js static site that teaches TLA+ specifications through two sections:

1. **Intro to TLA+** — step-by-step lessons on syntax, data structures, and TLC configuration
2. **BlockingQueue Tutorial** — an adaptation of [Markus Kuppe's BlockingQueue](https://github.com/lemmy/BlockingQueue) tutorial, walking through a concurrent bounded buffer spec commit by commit

Each lesson has a split layout: explanation on the left, interactive playground on the right. The playground runs the TLC model checker directly in the browser via [CheerpJ](https://cheerpj.com/) (TLA+ tools compiled to a JAR, executed in-browser).

## Development

```bash
npm install
npm run dev       # start dev server at http://localhost:3000
npm test          # run jest tests
npm run build     # static export to out/
```

Requires Node.js 20+.

## Project structure

```
src/
├── app/                        # Next.js App Router pages
│   ├── page.tsx                # Homepage with section cards
│   ├── intro/[slug]/           # Intro lesson pages
│   └── blocking-queue/[step]/  # BlockingQueue lesson pages
├── components/                 # React components
│   ├── Playground.tsx          # Tabbed editor + Run TLC + output panel
│   ├── LessonLayout.tsx        # Split view (description | playground)
│   ├── CodeEditor.tsx          # CodeMirror with TLA+ syntax highlighting
│   ├── MarkdownContent.tsx     # Lightweight markdown renderer
│   └── ...
├── content/
│   ├── intro/                  # 9 intro lesson definitions
│   └── blocking-queue/         # 12 BlockingQueue lesson definitions
└── lib/
    ├── lessons.ts              # Lesson types and data loading
    ├── cheerpj.ts              # CheerpJ/TLC integration
    └── tlaplus-lang.ts         # CodeMirror TLA+ language mode
public/
├── tlaplus-web-cheerpj.jar     # TLA+ tools JAR for in-browser execution
├── tlc-worker.html             # iframe worker for TLC runs
└── bq-images/                  # Images from BlockingQueue repo
```

## CI/CD

- **CI** (`.github/workflows/ci.yml`): runs tests and build on push/PR to main
- **CD** (`.github/workflows/cd.yml`): deploys to tlabyexample.com via rsync after CI passes on main
  - Requires `SSH_PRIVATE_KEY` secret and `HOST` variable in repo settings

## Related resources

- [TLA+ tools](https://github.com/tlaplus/tlaplus) — the TLA+ project
- [tlaplus-web](https://github.com/nicholasgasior/tlaplus-web) — TLA+ compiled for web (CheerpJ approach)
- [BlockingQueue](https://github.com/lemmy/BlockingQueue) — Markus Kuppe's original tutorial
- [TLA+ VS Code extension](https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus)
- [Learn TLA+](https://learntla.com/) — Hillel Wayne's guide
