import fs from "fs";
import path from "path";
import { Lesson } from "@/lib/lessons";
import { parseLesson } from "@/lib/parse-lesson";

const dir = path.join(process.cwd(), "src", "content", "intro");

const mdFiles = [
  "platform.md",
  "tla-intuition.md",
  "module-structure.md",
  "variables-constants.md",
  "basic-operators.md",
  "sets.md",
  "functions.md",
  "sequences.md",
  "records.md",
  "tlc-config.md",
];

const mdLessons: Lesson[] = mdFiles.map((f) =>
  parseLesson(fs.readFileSync(path.join(dir, f), "utf-8"))
);

export const introLessons: Lesson[] = [...mdLessons];
