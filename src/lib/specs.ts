import fs from "fs";
import path from "path";

const EXAMPLES_DIR = path.resolve(process.cwd(), "../Examples/specifications");

interface ManifestModel {
  path: string;
  runtime?: string;
  mode?: string;
  result?: string;
  distinctStates?: number;
  totalStates?: number;
  stateDepth?: number;
}

interface ManifestModule {
  path: string;
  features: string[];
  models: ManifestModel[];
}

interface Manifest {
  sources: string[];
  authors: string[];
  tags: string[];
  modules: ManifestModule[];
}

export interface SpecSummary {
  slug: string;
  name: string;
  authors: string[];
  tags: string[];
}

export interface SpecModule {
  filename: string;
  content: string;
  cfgFiles: { filename: string; content: string }[];
}

export interface SpecDetail {
  slug: string;
  name: string;
  authors: string[];
  tags: string[];
  readme: string;
  modules: SpecModule[];
}

function readManifest(specDir: string): Manifest | null {
  const manifestPath = path.join(specDir, "manifest.json");
  if (!fs.existsSync(manifestPath)) return null;
  return JSON.parse(fs.readFileSync(manifestPath, "utf-8"));
}

function formatName(slug: string): string {
  return slug.replace(/[-_]/g, " ");
}

/** Extract the leading (* ... *) comment block(s) from a TLA+ source file. */
function extractTlaDescription(tlaContent: string): string {
  const lines = tlaContent.split("\n");
  const descLines: string[] = [];
  let inComment = false;
  let foundModule = false;

  for (const line of lines) {
    // Skip the MODULE header line
    if (!foundModule) {
      if (/^-+\s*MODULE\s+\w+\s*-+/.test(line)) {
        foundModule = true;
      }
      continue;
    }

    const trimmed = line.trim();

    // Start of a comment block
    if (trimmed.startsWith("(*")) {
      inComment = true;
    }

    if (inComment) {
      // Strip TLA+ comment delimiters and asterisk borders
      let clean = trimmed;
      clean = clean.replace(/^\(\*+\s?/, "").replace(/\s?\*+\)$/, "");
      // Handle bare ")" left after greedy (* strip on border lines
      clean = clean.replace(/^\)$/, "");
      clean = clean.replace(/^\*+$/, "");
      descLines.push(clean);
    }

    if (trimmed.endsWith("*)")) {
      inComment = false;
    }

    // Stop once we hit non-comment, non-blank content after the first comment block
    if (foundModule && !inComment && descLines.length > 0 && trimmed && !trimmed.startsWith("(*")) {
      break;
    }
  }

  const text = descLines.join("\n").trim();
  return text || "";
}

export function getBeginnerSpecs(): SpecSummary[] {
  if (!fs.existsSync(EXAMPLES_DIR)) return [];

  const dirs = fs.readdirSync(EXAMPLES_DIR, { withFileTypes: true })
    .filter((d) => d.isDirectory())
    .map((d) => d.name)
    .sort();

  const specs: SpecSummary[] = [];
  for (const dir of dirs) {
    const manifest = readManifest(path.join(EXAMPLES_DIR, dir));
    if (!manifest) continue;
    if (!manifest.tags.includes("beginner")) continue;

    specs.push({
      slug: dir,
      name: formatName(dir),
      authors: manifest.authors,
      tags: manifest.tags,
    });
  }
  return specs;
}

export function getSpecBySlug(slug: string): SpecDetail | null {
  const specDir = path.join(EXAMPLES_DIR, slug);
  if (!fs.existsSync(specDir)) return null;

  const manifest = readManifest(specDir);
  if (!manifest) return null;

  const readmePath = path.join(specDir, "README.md");
  let readme: string;
  if (fs.existsSync(readmePath)) {
    readme = fs.readFileSync(readmePath, "utf-8");
  } else {
    readme = `# ${formatName(slug)}\n\nNo description available.`;
  }

  // Separate root modules from toolbox modules
  const rootModules = manifest.modules.filter(
    (mod) => !mod.path.includes(".toolbox/")
  );
  const toolboxModules = manifest.modules.filter(
    (mod) => mod.path.includes(".toolbox/")
  );

  // Collect cfg files from toolbox models, keyed by the base .tla filename they belong to
  const toolboxCfgs = new Map<string, { filename: string; content: string }[]>();
  for (const mod of toolboxModules) {
    // Toolbox paths look like: specs/X/X.toolbox/ModelName/MC.tla
    // The parent .tla is typically the spec dir name (e.g. CarTalkPuzzle.tla)
    for (const model of mod.models) {
      const cfgPath = path.join(EXAMPLES_DIR, "..", model.path);
      if (!fs.existsSync(cfgPath)) continue;
      // Extract model name from path: .toolbox/ModelName/MC.cfg → ModelName
      const parts = model.path.split("/");
      const toolboxIdx = parts.findIndex((p) => p.endsWith(".toolbox"));
      const modelName = toolboxIdx >= 0 && toolboxIdx + 1 < parts.length
        ? parts[toolboxIdx + 1]
        : path.basename(model.path, ".cfg");
      const cfgFilename = `${modelName}.cfg`;
      const specBase = toolboxIdx >= 0 ? parts[toolboxIdx].replace(".toolbox", "") : slug;

      const key = specBase;
      if (!toolboxCfgs.has(key)) toolboxCfgs.set(key, []);
      toolboxCfgs.get(key)!.push({
        filename: cfgFilename,
        content: fs.readFileSync(cfgPath, "utf-8"),
      });
    }
  }

  const modules: SpecModule[] = [];
  for (const mod of rootModules) {
    const tlaPath = path.join(EXAMPLES_DIR, "..", mod.path);
    if (!fs.existsSync(tlaPath)) continue;

    const content = fs.readFileSync(tlaPath, "utf-8");
    const filename = path.basename(mod.path);
    const baseName = path.basename(mod.path, ".tla");

    const cfgFiles: { filename: string; content: string }[] = [];
    // Add cfg files from root module models
    for (const model of mod.models) {
      const cfgPath = path.join(EXAMPLES_DIR, "..", model.path);
      if (!fs.existsSync(cfgPath)) continue;
      cfgFiles.push({
        filename: path.basename(model.path),
        content: fs.readFileSync(cfgPath, "utf-8"),
      });
    }
    // Add cfg files from toolbox models that belong to this .tla
    const extraCfgs = toolboxCfgs.get(baseName) ?? [];
    for (const cfg of extraCfgs) {
      // Avoid duplicates by filename
      if (!cfgFiles.some((c) => c.filename === cfg.filename)) {
        cfgFiles.push(cfg);
      }
    }

    modules.push({ filename, content, cfgFiles });
  }

  // If no README, extract description from the first .tla module header
  if (!fs.existsSync(readmePath) && modules.length > 0) {
    const desc = extractTlaDescription(modules[0].content);
    if (desc) {
      readme = `# ${formatName(slug)}\n\n${desc}`;
    }
  }

  return {
    slug,
    name: formatName(slug),
    authors: manifest.authors,
    tags: manifest.tags,
    readme,
    modules,
  };
}
