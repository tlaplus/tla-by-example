# Copilot Instructions

## Build & Test

```bash
npm run dev        # dev server at localhost:3000
npm run build      # static export to out/
npm test           # all tests
npx jest __tests__/lessons.test.ts              # single test file
npx jest --testNamePattern "unique slugs"       # single test by name
npm run lint       # ESLint via next lint
```

CI runs `npm test` then `npm run build` on Node 20 (ubuntu-latest).

## Architecture

This is a **Next.js 14 static site** (`output: "export"`) that teaches TLA+ through interactive lessons. Each lesson pairs a markdown explanation with a code playground that runs the TLC model checker in the browser.

**Content → Pages → Components flow:**

1. **Lesson definitions** (`src/content/intro/`, `src/content/blocking-queue/`) are TypeScript files exporting a `Lesson` object with `slug`, `title`, `section`, `description` (markdown), `spec` (TLA+ code), `cfg` (TLC config), and optional `extraTabs`/`commitSha` fields.
2. **Dynamic routes** (`src/app/intro/[slug]/page.tsx`, `src/app/blocking-queue/[step]/page.tsx`) use `generateStaticParams()` to pre-build all lesson pages.
3. **LessonLayout** renders a resizable split view: markdown explanation on the left, **Playground** on the right.
4. **Playground** manages tabbed CodeMirror editors (spec/cfg/extra tabs) and runs TLC via CheerpJ.

**In-browser TLC execution** (`src/lib/cheerpj.ts`): TLC runs inside a hidden iframe (`public/tlc-worker.html`) that loads a JAR via CheerpJ. Communication uses `postMessage` with "ready", "progress", "result", and "error" message types. The iframe is recreated after each run to reset JVM state.

**TLA+ syntax highlighting** (`src/lib/tlaplus-lang.ts`): Custom CodeMirror language mode supporting both `.tla` specs and `.cfg` configs, with nested block comments (`(* *)`).

## Conventions

- **Lesson file pattern**: Each lesson is a single TS file in `src/content/<section>/` that default-exports a `Lesson` object. Sections re-export lessons as arrays from their `index.ts`. When adding a lesson, also update the array export and ensure the slug is unique within its section.
- **`@/` path alias**: Configured in tsconfig and jest for imports from `src/`.
- **No SSR for CodeEditor**: The `CodeEditor` component is loaded with `dynamic(() => import(...), { ssr: false })` because CodeMirror requires browser APIs.
- **Tests validate content integrity**: `__tests__/lessons.test.ts` checks lesson counts, unique slugs, non-empty spec/cfg, and correct section assignments. Update expected counts when adding/removing lessons.
- **Styling**: Tailwind CSS with default config.
