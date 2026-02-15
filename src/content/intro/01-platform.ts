import { Lesson } from "@/lib/lessons";

const lesson: Lesson = {
  slug: "platform",
  title: "Welcome",
  section: "intro",
  description: `Welcome to TLA+ By Example! This platform lets you learn TLA+ by reading explanations and running specifications directly in your browser.

## How It Works

On the right side of this page, you'll see the **playground**. It has two tabs:

- **Spec.tla** — the TLA+ specification you're writing
- **Spec.cfg** — the TLC model checker configuration

Click **▶ Run TLC** to model-check the specification. The output will appear in the panel at the bottom of the playground.

## What is TLA+?

TLA+ is a formal specification language developed by Leslie Lamport. It's used to design, model, and verify concurrent and distributed systems. Companies like Amazon, Microsoft, and Intel use TLA+ to find bugs in critical systems before they're built.

A TLA+ specification describes:
- **State**: the variables that define your system
- **Initial state**: how the system starts
- **Next-state relation**: how the system can transition between states
- **Invariants**: properties that must always hold

## Try It Now

The playground on the right has a classic example: the **DieHard** water jugs puzzle from the movie Die Hard 3. The heroes need exactly 4 gallons using a 5-gallon and a 3-gallon jug.

![youtube](https://www.youtube.com/watch?v=m9F0i-1Jys0)

Click **▶ Run TLC** to see TLC find a solution (it will report an invariant violation — which is actually the solution!).

## Follow Along Locally

You can also install the [TLA+ VS Code Extension](https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus) to write and check specs on your machine.`,
  spec: `----------------------------- MODULE DieHard --------------------------------
(***************************************************************************)
(* The DieHard water jugs puzzle: get exactly 4 gallons using a            *)
(* 5-gallon jug and a 3-gallon jug.                                        *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES big,   \\* gallons in the 5-gallon jug
          small  \\* gallons in the 3-gallon jug

TypeOK == /\\ small \\in 0..3
          /\\ big   \\in 0..5

Init == /\\ big = 0
        /\\ small = 0

FillSmallJug  == /\\ small' = 3
                 /\\ big' = big

FillBigJug    == /\\ big' = 5
                 /\\ small' = small

EmptySmallJug == /\\ small' = 0
                 /\\ big' = big

EmptyBigJug   == /\\ big' = 0
                 /\\ small' = small

Min(m,n) == IF m < n THEN m ELSE n

SmallToBig == /\\ big'   = Min(big + small, 5)
              /\\ small' = small - (big' - big)

BigToSmall == /\\ small' = Min(big + small, 3)
              /\\ big'   = big - (small' - small)

Next == \\/ FillSmallJug
        \\/ FillBigJug
        \\/ EmptySmallJug
        \\/ EmptyBigJug
        \\/ SmallToBig
        \\/ BigToSmall

NotSolved == big # 4

=============================================================================`,
  cfg: `INIT Init
NEXT Next
INVARIANT TypeOK
INVARIANT NotSolved
`,
};

export default lesson;
