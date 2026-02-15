import fs from "fs";
import path from "path";
import { Lesson } from "@/lib/lessons";
import { parseLesson } from "@/lib/parse-lesson";

const dir = path.join(process.cwd(), "src", "content", "blocking-queue");

const mdFiles = fs
  .readdirSync(dir)
  .filter((f) => f.endsWith(".md"))
  .sort();

const mdLessons: Lesson[] = mdFiles.map((f) =>
  parseLesson(fs.readFileSync(path.join(dir, f), "utf-8"))
);

export const blockingQueueLessons: Lesson[] = [...mdLessons];
