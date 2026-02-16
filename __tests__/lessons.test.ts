import { introLessons } from "@/content/intro";
import { blockingQueueLessons } from "@/content/blocking-queue";

describe("Lesson data", () => {
  it("has 10 intro lessons", () => {
    expect(introLessons).toHaveLength(10);
  });

  it("has 12 blocking queue lessons", () => {
    expect(blockingQueueLessons).toHaveLength(12);
  });

  it("all intro lessons have unique slugs", () => {
    const slugs = introLessons.map((l) => l.slug);
    expect(new Set(slugs).size).toBe(slugs.length);
  });

  it("all blocking queue lessons have unique slugs", () => {
    const slugs = blockingQueueLessons.map((l) => l.slug);
    expect(new Set(slugs).size).toBe(slugs.length);
  });

  it("all lessons have non-empty spec and cfg", () => {
    const allLessons = [...introLessons, ...blockingQueueLessons];
    for (const lesson of allLessons) {
      // tla-intuition uses an animation instead of a spec/cfg playground
      if (lesson.slug === "tla-intuition") continue;
      expect(lesson.spec.length).toBeGreaterThan(0);
      expect(lesson.cfg.length).toBeGreaterThan(0);
    }
  });

  it("all blocking queue lessons are in the blocking-queue section", () => {
    for (const lesson of blockingQueueLessons) {
      expect(lesson.section).toBe("blocking-queue");
    }
  });

  it("all intro lessons are in the intro section", () => {
    for (const lesson of introLessons) {
      expect(lesson.section).toBe("intro");
    }
  });
});
