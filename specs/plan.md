# TLA+ By Example — Implementation Plan

## Problem Statement

Build a learning website at `tla-by-example/` that teaches TLA+ through interactive examples. The site has two sections:

1. **Intro ("How to Write TLA+")** — step-by-step pages covering TLA+ syntax, data structures, and the standard modules
2. **BlockingQueue** — a guided walkthrough of [lemmy/BlockingQueue](https://github.com/lemmy/BlockingQueue) commits (v00–v13), where each page shows the spec at that commit with the commit message as explanation

Each page has a split layout: explanation on the left, interactive playground on the right. The playground uses CheerpJ to run TLC in-browser (reusing the `tlaplus-web` JAR and integration code).

## Current State (Phase 1-6 Complete)

The project is fully scaffolded and functional:
- Next.js 14 + Tailwind CSS (light theme) + Jest (13 tests passing)
- Homepage with two sections, 9 intro lessons, 11 blocking-queue lessons
- Playground with CodeMirror, CheerpJ integration, tabbed editors
- Split LessonLayout, Navbar with prev/next, Footer
- All 24 pages build successfully

## New Changes Required

### 1. BlockingQueue Introduction Page
- Add a new "section 0" page before v02 that serves as an introduction to the BlockingQueue tutorial
- Include overview description from the README (tutorial-style talk, inspiration from Michel Charpentier, etc.)
- Embed the p1c1b1.svg state graph image
- Include Java source code (App.java, BlockingQueue.java, Producer.java, Consumer.java) in a new "Java" tab
- Include C source code (producer_consumer.c) in a new "C" tab
- Add instructions on how to clone the repo and run the Java/C implementations

### 2. Copy Images from BlockingQueue Repo
Copy these images to `public/bq-images/`:
- `p1c1b1.svg` (v02 state graph)
- `p1c2b1.svg` (v03 state graph)
- `animation/BlockingQueue-Proc2_Cons1_Buff1_Len08.gif` (v10 animation)
- `animation/BlockingQueue-Proc4_Cons3_Buff3_Len46.gif` (v10 animation)
- `screencasts/v03-StateGraph.gif` (v03 explore)
- `screencasts/v04-PickSuccessor.gif` (v04 debug)
- `R/ContinueInequation.svg` (v08 inequation plot)
- `R/TraceLengthCorrelation.svg` (v08 correlation plot)

### 3. Enrich Descriptions with README Content
Enrich (not replace) existing lesson descriptions by integrating relevant text from the BlockingQueue README. Keep existing explanations that are already good; augment with README details and images where they add value.

### 4. Remove "vXX" Prefix from Titles
Change titles like "v02: State Graph (Minimum Config)" → "State Graph (Minimum Config)"

### 5. Add Commit Reference Links
Each blocking-queue page should have a link to the specific commit on GitHub.

### 6. Add Java/C Source Tab to Intro Page
The Playground component needs to support additional read-only code tabs (Java, C) beyond spec and cfg. These are shown only on the introduction page.

## Todos

- **bq-download-images**: Download all referenced images from lemmy/BlockingQueue into public/bq-images/
- **bq-intro-page**: Create introduction page with overview, p1c1b1.svg, Java/C source, run instructions
- **bq-enrich-descriptions**: Update all 11 lesson descriptions with README text and images
- **bq-remove-version-prefix**: Strip "vXX:" from all blocking-queue lesson titles
- **bq-add-commit-links**: Add commit SHA links to each blocking-queue lesson page
- **playground-extra-tabs**: Extend Playground to support read-only code tabs (Java, C)
- **bq-build-verify**: Build, test, verify everything works
