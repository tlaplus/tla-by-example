import { introLessons } from "@/content/intro";
import TlaIntuitionClient from "./TlaIntuitionClient";

const DIEHARD_SPEC = `----------------------------- MODULE DieHard --------------------------------
EXTENDS Naturals

VARIABLES big,   \\* gallons in the 5-gallon jug
          small  \\* gallons in the 3-gallon jug

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
=============================================================================`;

export function generateMetadata() {
  return { title: "The TLA+ / TLC Intuition - TLA+ By Example" };
}

export default function TlaIntuitionPage() {
  const idx = introLessons.findIndex((l) => l.slug === "tla-intuition");
  const lesson = introLessons[idx];
  const prev = idx > 0 ? introLessons[idx - 1] : undefined;
  const next =
    idx < introLessons.length - 1 ? introLessons[idx + 1] : undefined;

  return (
    <TlaIntuitionClient
      description={lesson.description}
      spec={DIEHARD_SPEC}
      prev={
        prev
          ? { slug: prev.slug, title: prev.title, section: prev.section }
          : undefined
      }
      next={
        next
          ? { slug: next.slug, title: next.title, section: next.section }
          : undefined
      }
    />
  );
}
