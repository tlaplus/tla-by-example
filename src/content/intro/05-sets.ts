import { Lesson } from "@/lib/lessons";

const lesson: Lesson = {
  slug: "sets",
  title: "Sets",
  section: "intro",
  description: `# Sets

Sets are one of the most fundamental data structures in TLA+. Unlike programming languages, TLA+ is built on set theory.

## Set Literals

\`\`\`
{1, 2, 3}          \\* a set of numbers
{"a", "b", "c"}    \\* a set of strings
{}                  \\* the empty set
\`\`\`

## Set Membership

\`\`\`
x \\in S            \\* x is a member of S
x \\notin S         \\* x is NOT a member of S
\`\`\`

## Set Operators

| Operator | Meaning |
|----------|---------|
| \`S \\union T\` | Union - elements in S or T |
| \`S \\intersect T\` | Intersection - elements in both |
| \`S \\\\ T\` | Set difference - elements in S but not T |
| \`SUBSET S\` | Power set - all subsets of S |
| \`S \\subseteq T\` | S is a subset of T |
| \`Cardinality(S)\` | Number of elements (needs FiniteSets) |

## Set Comprehension (Filtering)

\`\`\`
{x \\in S : P(x)}   \\* elements of S satisfying predicate P
\`\`\`

Example: \`{x \\in 1..10 : x > 5}\` gives \`{6, 7, 8, 9, 10}\`

## Set Mapping

\`\`\`
{f(x) : x \\in S}   \\* apply f to each element of S
\`\`\`

Example: \`{x * 2 : x \\in 1..3}\` gives \`{2, 4, 6}\`

## Ranges

\`\`\`
1..5               \\* the set {1, 2, 3, 4, 5}
\`\`\`

## Try It

The spec on the right demonstrates various set operations. Run TLC to verify the invariants.`,
  spec: `------------------------------- MODULE Sets ----------------------------------
EXTENDS Naturals, FiniteSets

VARIABLE picked

Colors == {"red", "green", "blue"}

Init == picked = {}

AddColor == /\\ Cardinality(picked) < Cardinality(Colors)
            /\\ \\E c \\in Colors :
                 /\\ c \\notin picked
                 /\\ picked' = picked \\union {c}

RemoveColor == /\\ picked # {}
               /\\ \\E c \\in picked :
                    picked' = picked \\ {c}

Next == AddColor \\/ RemoveColor

TypeOK == picked \\subseteq Colors

AlwaysSmall == Cardinality(picked) <= Cardinality(Colors)

=============================================================================`,
  cfg: `INIT Init
NEXT Next
INVARIANT TypeOK
INVARIANT AlwaysSmall
`,
};

export default lesson;
