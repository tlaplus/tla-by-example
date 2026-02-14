import { Lesson } from "@/lib/lessons";

const lesson: Lesson = {
  slug: "module-structure",
  title: "Module Structure",
  section: "intro",
  description: `# Module Structure

Every TLA+ specification lives inside a **module**. A module is delimited by a header and a footer:

\`\`\`
---- MODULE MySpec ----
(* your spec goes here *)
========================
\`\`\`

## The Header

The header line starts with four or more dashes, followed by \`MODULE\`, the module name, and four or more dashes:

\`\`\`
---- MODULE MySpec ----
\`\`\`

The module name must match the filename (e.g., \`MySpec.tla\`).

## The Footer

The footer is a line of four or more equals signs:

\`\`\`
========================
\`\`\`

Everything after the footer is ignored.

## EXTENDS

The \`EXTENDS\` keyword imports definitions from other modules. You'll almost always extend at least one standard module:

\`\`\`
EXTENDS Naturals, Sequences
\`\`\`

Common standard modules:
- **Naturals** — natural numbers and arithmetic (+, -, *, \\div, %)
- **Integers** — integers (adds negative numbers)
- **Sequences** — sequence operations (Append, Head, Tail, Len)
- **FiniteSets** — Cardinality, IsFiniteSet
- **TLC** — TLC-specific operators (Print, Assert)

## Separator Lines

Inside a module, you can use separator lines (four or more dashes) to visually organize your spec:

\`\`\`
----
\`\`\`

These have no semantic meaning — they're just for readability.

## Try It

The spec on the right shows a minimal module structure. Try modifying it and running TLC to see what happens.`,
  spec: `----------------------------- MODULE MySpec ----------------------------------
(***************************************************************************)
(* A minimal TLA+ module demonstrating the basic structure.                *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE x

Init == x = 0

Next == x' = x + 1

Spec == Init /\\ [][Next]_x

Bound == x < 5

=============================================================================`,
  cfg: `INIT Init
NEXT Next
INVARIANT Bound
`,
};

export default lesson;
