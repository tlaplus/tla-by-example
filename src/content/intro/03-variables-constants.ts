import { Lesson } from "@/lib/lessons";

const lesson: Lesson = {
  slug: "variables-constants",
  title: "Variables & Constants",
  section: "intro",
  description: `# Variables & Constants

TLA+ has two kinds of declarations for values that appear in your spec:

## VARIABLE (or VARIABLES)

Variables represent the **state** of your system. They change over time as the system transitions between states.

\`\`\`
VARIABLES x, y, z
\`\`\`

You can also write \`VARIABLE x\` for a single variable. Both keywords work the same.

In the **next-state relation**, you refer to the value of a variable in the next state using a prime (\`'\`):

\`\`\`
Next == x' = x + 1
\`\`\`

## CONSTANT (or CONSTANTS)

Constants are values that are **fixed** for a given model run. They're set in the TLC configuration file.

\`\`\`
CONSTANTS N, MaxVal
\`\`\`

Constants let you parameterize your spec. For example, you might define a buffer size as a constant so you can model-check with different sizes.

## TypeOK Invariant

A common pattern is to define a **type-correctness invariant** called \`TypeOK\`. It specifies the expected types/ranges of all variables:

\`\`\`
TypeOK == /\\ x \\in Nat
          /\\ y \\in 1..N
\`\`\`

This isn't enforced by TLA+ itself — it's checked by TLC as an invariant. It's useful for catching bugs early.

## Try It

The spec on the right uses both variables and constants. Check the \`Spec.cfg\` tab to see how the constant \`N\` is assigned a value.`,
  spec: `--------------------------- MODULE VarsAndConsts ----------------------------
EXTENDS Naturals

CONSTANT N

VARIABLES count, total

TypeOK == /\\ count \\in 0..N
          /\\ total \\in Nat

Init == /\\ count = 0
        /\\ total = 0

Increment == /\\ count < N
             /\\ count' = count + 1
             /\\ total' = total + 1

Reset == /\\ count = N
         /\\ count' = 0
         /\\ total' = total

Next == Increment \\/ Reset

=============================================================================`,
  cfg: `CONSTANT N = 3
INIT Init
NEXT Next
INVARIANT TypeOK
`,
};

export default lesson;
