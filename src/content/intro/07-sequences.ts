import { Lesson } from "@/lib/lessons";

const lesson: Lesson = {
  slug: "sequences",
  title: "Sequences",
  section: "intro",
  description: `# Sequences

Sequences are ordered lists of elements in TLA+. In TLA+, sequences are simply functions whose domain is \`1..n\`, but because this pattern occurs so frequently, TLA+ provides dedicated syntax for them. You need to \`EXTENDS Sequences\` to use sequence operators.

## Creating Sequences

\`\`\`
<<1, 2, 3>>         \\* a sequence of three elements
<<>>                 \\* the empty sequence
<< "hello" >>       \\* a sequence with one element
\`\`\`

## Accessing Elements

Sequences are 1-indexed:

\`\`\`
s[1]                 \\* first element
s[Len(s)]            \\* last element
\`\`\`

## Sequence Operators

| Operator | Meaning |
|----------|---------|
| \`Len(s)\` | Length of s |
| \`Head(s)\` | First element |
| \`Tail(s)\` | All elements except the first |
| \`Append(s, e)\` | Add e to the end |
| \`s \\o t\` | Concatenate sequences s and t |
| \`SubSeq(s, m, n)\` | Subsequence from index m to n |

## Sequences as Functions

A sequence is actually a function from \`1..n\` to values. So \`DOMAIN s = 1..Len(s)\`.

## Common Patterns

**Stack (LIFO):**
\`\`\`
Push(s, e) == <<e>> \\o s
Pop(s)     == Tail(s)
Peek(s)    == Head(s)
\`\`\`

**Queue (FIFO):**
\`\`\`
Enqueue(s, e) == Append(s, e)
Dequeue(s)    == Tail(s)
Front(s)      == Head(s)
\`\`\`

## Try It

The spec on the right models a simple bounded stack.`,
  spec: `------------------------------ MODULE Stack ----------------------------------
EXTENDS Naturals, Sequences

CONSTANT MaxSize

VARIABLE stack

TypeOK == /\\ stack \\in Seq(Nat)
          /\\ Len(stack) <= MaxSize

Init == stack = <<>>

Push == /\\ Len(stack) < MaxSize
        /\\ \\E val \\in 1..5 :
             stack' = <<val>> \\o stack

Pop == /\\ Len(stack) > 0
       /\\ stack' = Tail(stack)

Next == Push \\/ Pop

NeverOverflows == Len(stack) <= MaxSize

=============================================================================`,
  cfg: `CONSTANT MaxSize = 3
INIT Init
NEXT Next
INVARIANT TypeOK
INVARIANT NeverOverflows
`,
};

export default lesson;
