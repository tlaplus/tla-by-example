// Export every lesson's spec and config as real files, so the lessons can be
// opened and model-checked with the TLA+ VS Code extension (e.g. in a
// codespace, see .devcontainer/devcontainer.json):
//
//   lessons/<section>/<lesson>/<Module>.tla
//   lessons/<section>/<lesson>/<Module>.cfg
//
// Reuses src/lib/parse-lesson.ts, which needs Node >= 22.18 (built-in
// TypeScript type stripping) and `npm install` (for gray-matter).
//
// Usage: node scripts/export-lessons.mjs [outDir]   (default: ./lessons)
import fs from "fs";
import path from "path";
import { fileURLToPath } from "url";
import { parseLesson } from "../src/lib/parse-lesson.ts";

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const contentDir = path.join(root, "src", "content");
const outDir = path.resolve(process.argv[2] ?? path.join(root, "lessons"));

function moduleName(spec) {
  return spec.match(/^-{4,}\s*MODULE\s+(\w+)/m)?.[1];
}

let exported = 0;
for (const section of fs.readdirSync(contentDir).sort()) {
  const sectionDir = path.join(contentDir, section);
  if (!fs.statSync(sectionDir).isDirectory()) continue;
  // Only clear what this script generates, so removed lessons don't linger.
  fs.rmSync(path.join(outDir, section), { recursive: true, force: true });

  for (const file of fs.readdirSync(sectionDir).filter((f) => f.endsWith(".md")).sort()) {
    const lesson = parseLesson(fs.readFileSync(path.join(sectionDir, file), "utf-8"));
    const mod = moduleName(lesson.spec);
    if (!mod) continue; // e.g. animation-only lessons without a spec

    const lessonDir = path.join(outDir, section, file.replace(/\.md$/, ""));
    fs.mkdirSync(lessonDir, { recursive: true });
    fs.writeFileSync(path.join(lessonDir, `${mod}.tla`), lesson.spec + "\n");
    if (lesson.cfg) fs.writeFileSync(path.join(lessonDir, `${mod}.cfg`), lesson.cfg + "\n");
    exported++;
  }
}

console.log(`Exported ${exported} lessons to ${path.relative(process.cwd(), outDir) || "."}`);
