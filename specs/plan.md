# TLA+ By Example — Implementation Plan

## Problem Statement

Build a learning website at `tla-by-example/` that teaches TLA+ through interactive examples. The site has two sections:

1. **Intro ("How to Write TLA+")** — step-by-step pages covering TLA+ syntax, data structures, and the standard modules
2. **BlockingQueue** — a guided walkthrough of [lemmy/BlockingQueue](https://github.com/lemmy/BlockingQueue) commits (v00–v13), where each page shows the spec at that commit with the commit message as explanation

Each page has a split layout: explanation on the left, interactive playground on the right. The playground uses CheerpJ to run TLC in-browser (reusing the `tlaplus-web` JAR and integration code).

## Approach

- Next.js (App Router) + Tailwind CSS, light theme
- Reuse code from `tlaplus-web`: CheerpJ integration, CodeMirror editor, TLA+ syntax highlighting
- Minimal dependencies — no extra UI frameworks
- TDD where practical (utility functions, data loading)
- Content stored as static data (TypeScript files with spec/cfg/description)
- BlockingQueue specs fetched from GitHub API at build time or stored locally

## Architecture

```
tla-by-example/
├── specs/                     # plan lives here
│   └── plan.md
├── public/
│   ├── tlaplus-web-cheerpj.jar
│   └── tlc-worker.html
├── src/
│   ├── app/
│   │   ├── layout.tsx         # root layout with footer
│   │   ├── page.tsx           # homepage with two section cards
│   │   ├── intro/
│   │   │   └── [slug]/
│   │   │       └── page.tsx   # intro lesson pages
│   │   └── blocking-queue/
│   │       └── [step]/
│   │           └── page.tsx   # blocking queue step pages
│   ├── components/
│   │   ├── CodeEditor.tsx     # CodeMirror editor (from tlaplus-web)
│   │   ├── Playground.tsx     # tabbed editor + run button + output panel
│   │   ├── LessonLayout.tsx   # split layout: explanation | playground
│   │   ├── Footer.tsx         # site footer
│   │   ├── Navbar.tsx         # navigation with prev/next
│   │   └── ResizableDivider.tsx
│   ├── lib/
│   │   ├── cheerpj.ts         # CheerpJ integration (from tlaplus-web)
│   │   ├── tlaplus-lang.ts    # TLA+ CodeMirror language (from tlaplus-web)
│   │   └── lessons.ts         # lesson registry & types
│   └── content/
│       ├── intro/             # intro lesson data files
│       │   ├── 01-platform.ts
│       │   ├── 02-module-structure.ts
│       │   ├── 03-variables-constants.ts
│       │   ├── 04-basic-operators.ts
│       │   ├── 05-sets.ts
│       │   ├── 06-functions.ts
│       │   ├── 07-sequences.ts
│       │   ├── 08-records.ts
│       │   └── 09-tlc-config.ts
│       └── blocking-queue/    # blocking queue step data files
│           ├── index.ts       # registry of steps
│           ├── v00-setup.ts
│           ├── v01-code.ts
│           ├── ...
│           └── v13-bugfix-two-mutexes.ts
├── __tests__/                 # tests
├── tailwind.config.ts
├── next.config.mjs
├── package.json
└── tsconfig.json
```

## Todos

### Phase 1: Project Scaffolding
- **scaffold-nextjs**: Initialize Next.js project with TypeScript, Tailwind CSS, and minimal config. Add testing framework (Jest + React Testing Library).
- **copy-tlaplus-web-assets**: Copy JAR, tlc-worker.html, cheerpj.ts, tlaplus-lang.ts, CodeEditor.tsx, ResizableDivider.tsx from tlaplus-web. Adapt imports.

### Phase 2: Core Components
- **footer-component**: Create Footer with "Made by Federico Ponzi — send questions and comments to me@fponzi.me". TDD.
- **playground-component**: Build Playground component — tabbed CodeMirror editors (spec + cfg tabs), "Run TLC" button, collapsible output panel that slides up from bottom. TDD for tab switching / output display logic.
- **lesson-layout**: Build LessonLayout — split view with markdown-rendered explanation on left, Playground on right. Responsive.
- **navbar-component**: Build Navbar with prev/next navigation between lessons, section title display.

### Phase 3: Homepage
- **homepage**: Build homepage with two sections: "How to Write TLA+" (intro cards) and "BlockingQueue Tutorial" (step cards). Each card links to its lesson page. Light, clean design.

### Phase 4: Intro Content
- **intro-platform**: Lesson 1 — Platform intro page explaining the playground, mention VS Code extension
- **intro-module-structure**: Lesson 2 — MODULE, EXTENDS, separators
- **intro-variables-constants**: Lesson 3 — VARIABLE, CONSTANT
- **intro-basic-operators**: Lesson 4 — Init/Next, boolean ops
- **intro-sets**: Lesson 5 — Sets and set operations
- **intro-functions**: Lesson 6 — Functions
- **intro-sequences**: Lesson 7 — Sequences module
- **intro-records**: Lesson 8 — Records
- **intro-tlc-config**: Lesson 9 — TLC configuration

### Phase 5: BlockingQueue Content
- **bq-clone-review**: Clone BlockingQueue repo, review commits v00–v13, extract .tla and .cfg files at each commit. Determine which commits to skip (v00 is setup-only). Build the content data files.
- **bq-content-pages**: Create blocking-queue step pages using extracted content. Each page attributes credit to Markus Kuppe and links to the repo.

### Phase 6: Polish & Verification
- **build-verify**: Run `next build`, fix any issues. Manual visual check.

## Key Decisions

- **Light theme** for documentation-friendly readability
- **v00–v13 only** for BlockingQueue (core learning arc; advanced topics deferred)
- **JAR copied** into `public/` (self-contained project)
- **No commits** until you review — all changes stay local
- **Testing**: Jest + React Testing Library for TDD

## Credits

- BlockingQueue spec & tutorial: [Markus Kuppe (lemmy)](https://github.com/lemmy/BlockingQueue) — MIT License
- TLA+ tools: [tlaplus/tlaplus](https://github.com/tlaplus/tlaplus)
- CheerpJ integration from [tlaplus-web](../tlaplus-web)
