# Lesson File Format

Lessons are written as Markdown files with YAML frontmatter and custom divider tags.

## Structure

```markdown
---
slug: my-lesson
title: "My Lesson Title"
section: intro
commitSha: "abc123"
commitUrl: "https://github.com/..."
---
Description content goes here (Markdown).

---TLA_BY_EXAMPLE_SPEC---
---- MODULE MySpec ----
EXTENDS Naturals
...
======================

---TLA_BY_EXAMPLE_CFG---
INIT Init
NEXT Next
INVARIANT TypeOK

---TLA_BY_EXAMPLE_TAB label="Java"---
// Java source code...

---TLA_BY_EXAMPLE_TAB label="C"---
// C source code...
```

## Frontmatter Fields

| Field | Required | Description |
|-------|----------|-------------|
| `slug` | Yes | URL-friendly identifier for the lesson |
| `title` | Yes | Display title |
| `section` | Yes | `"intro"` or `"blocking-queue"` |
| `commitSha` | No | Git commit SHA (shown in blocking-queue lessons) |
| `commitUrl` | No | Link to the commit on GitHub |

## Divider Tags

Content is split into sections using divider tags on their own line:

- `---TLA_BY_EXAMPLE_SPEC---` - Everything after this tag (until the next tag) is the TLA+ specification shown in the Spec editor tab.
- `---TLA_BY_EXAMPLE_CFG---` - Everything after this tag (until the next tag) is the TLC configuration shown in the Cfg editor tab.
- `---TLA_BY_EXAMPLE_TAB label="Name"---` - Everything after this tag (until the next tab tag or end of file) is shown as an extra read-only tab with the given label. Multiple tab tags can be used for multiple extra tabs.

## File Naming and Ordering

Lesson files are sorted alphabetically by filename. Use numeric prefixes to control order:

```
01-introduction.md
02-state-graph.md
03-larger-config.md
```

## Adding a New Lesson

1. Create a new `.md` file in the appropriate `src/content/` subdirectory
2. Add frontmatter with `slug`, `title`, and `section`
3. Write the description in Markdown
4. Add `---TLA_BY_EXAMPLE_SPEC---` followed by the TLA+ spec
5. Add `---TLA_BY_EXAMPLE_CFG---` followed by the TLC config
6. Optionally add `---TLA_BY_EXAMPLE_TAB label="..."---` sections for extra tabs

The lesson will be automatically discovered and included - no need to update `index.ts`.
