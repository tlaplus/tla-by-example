// "Run in VS Code": hand the playground's current spec/cfg over to a GitHub
// codespace of this repo (see .devcontainer/devcontainer.json). The site and
// the codespace cannot talk to each other directly, so the files travel in a
// one-line command that the learner pastes into the codespace's terminal;
// scripts/run-in-codespace.mjs decodes it, writes the files under
// playground/<dir>/, opens them and runs TLC.

const codespacesRepo = process.env.NEXT_PUBLIC_CODESPACES_REPO || "tlaplus/tla-by-example";
const codespacesRef = process.env.NEXT_PUBLIC_CODESPACES_REF;

export const CODESPACES_URL =
  `https://codespaces.new/${codespacesRepo}` +
  (codespacesRef ? `/tree/${codespacesRef}` : "") +
  "?quickstart=1";

export interface HandoffFile {
  name: string;
  content: string;
}

export interface HandoffPayload {
  v: 1;
  /** Folder under playground/, e.g. "intro/platform" or "specs/DieHard". */
  dir: string;
  spec: HandoffFile;
  cfg: HandoffFile;
  extra: HandoffFile[];
}

function moduleName(spec: string): string | undefined {
  return spec.match(/^-{4,}\s*MODULE\s+(\w+)/m)?.[1];
}

/** Names of the modules a spec EXTENDS or INSTANCEs. */
function referencedModules(spec: string): string[] {
  const names: string[] = [];
  for (const m of spec.matchAll(/\bEXTENDS\s+(\w+(?:\s*,\s*\w+)*)/g)) names.push(...m[1].split(/\s*,\s*/));
  for (const m of spec.matchAll(/\bINSTANCE\s+(\w+)/g)) names.push(m[1]);
  return names;
}

/**
 * Keep only the extra modules the spec (transitively) depends on: spec pages
 * offer every module of an example, which would make the pasted command huge.
 */
function usedModules(spec: string, extra: HandoffFile[]): HandoffFile[] {
  const byName = new Map(extra.map((m) => [m.name.replace(/\.tla$/, ""), m]));
  const used = new Set<string>();
  const pending = referencedModules(spec);
  while (pending.length > 0) {
    const name = pending.pop()!;
    const mod = byName.get(name);
    if (!mod || used.has(name)) continue;
    used.add(name);
    pending.push(...referencedModules(mod.content));
  }
  return extra.filter((m) => used.has(m.name.replace(/\.tla$/, "")));
}

/**
 * TLC on disk requires the file name to match the MODULE name, so name the
 * spec after its module (falling back to the tab label) and the cfg after it.
 * Extra modules the spec does not use are left out.
 */
export function buildPayload(
  dir: string,
  spec: HandoffFile,
  cfg: HandoffFile,
  extra: HandoffFile[] = [],
): HandoffPayload {
  const base = moduleName(spec.content) ?? spec.name.replace(/\.tla$/, "");
  const named = extra.map((m) => ({
    name: `${moduleName(m.content) ?? m.name.replace(/\.tla$/, "")}.tla`,
    content: m.content,
  }));
  return {
    v: 1,
    dir: dir.replace(/[^\w/-]/g, "-"),
    spec: { name: `${base}.tla`, content: spec.content },
    cfg: { name: `${base}.cfg`, content: cfg.content },
    extra: usedModules(spec.content, named),
  };
}

function toBase64Url(text: string): string {
  const bytes = new TextEncoder().encode(text);
  let binary = "";
  for (const b of bytes) binary += String.fromCharCode(b);
  return btoa(binary).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
}

/**
 * The command the learner pastes into the codespace terminal. The payload is
 * piped in by the shell's builtin echo rather than passed as an argument,
 * because Linux caps a single program argument at 128 KiB (MAX_ARG_STRLEN).
 */
export function buildCommand(payload: HandoffPayload): string {
  return `echo ${toBase64Url(JSON.stringify(payload))} | node scripts/run-in-codespace.mjs`;
}
