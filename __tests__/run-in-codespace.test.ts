/**
 * @jest-environment node
 */
import fs from "fs";
import os from "os";
import path from "path";
import { spawnSync } from "child_process";

// The script writes to <its repo root>/playground/, so run a copy of it in a
// temporary "repo". With no TLA+ extension under HOME it stops after writing
// the files, before opening an editor or starting TLC.
let root: string;

beforeEach(() => {
  root = fs.mkdtempSync(path.join(os.tmpdir(), "run-in-codespace-"));
  fs.mkdirSync(path.join(root, "scripts"));
  fs.copyFileSync(
    path.join(__dirname, "..", "scripts", "run-in-codespace.mjs"),
    path.join(root, "scripts", "run-in-codespace.mjs"),
  );
});

afterEach(() => fs.rmSync(root, { recursive: true, force: true }));

// The site's command is `echo <payload> | node scripts/run-in-codespace.mjs`.
function runRaw(input: string) {
  return spawnSync(process.execPath, [path.join(root, "scripts", "run-in-codespace.mjs")], {
    input,
    encoding: "utf-8",
    env: { ...process.env, PATH: "", HOME: root, TLA2TOOLS_JAR: "" },
  });
}
const run = (payload: unknown) => runRaw(Buffer.from(JSON.stringify(payload)).toString("base64url") + "\n");

const file = (name: string) => ({ name, content: "x" });
const payload = (overrides: object = {}) => ({
  v: 1,
  dir: "intro/sets",
  spec: file("Sets.tla"),
  cfg: file("Sets.cfg"),
  extra: [],
  ...overrides,
});
const written = () =>
  fs.existsSync(path.join(root, "playground")) ? fs.readdirSync(path.join(root, "playground"), { recursive: true }) : [];

describe("run-in-codespace.mjs", () => {
  it("writes valid files under playground/<dir>/", () => {
    const res = run(payload({ extra: [file("Helper.tla")] }));
    expect(res.stdout).toContain("Wrote 3 file(s) to playground/intro/sets/");
    expect(res.stderr).toContain("TLA+ extension not installed yet");
    expect(fs.readdirSync(path.join(root, "playground", "intro", "sets")).sort()).toEqual([
      "Helper.tla",
      "Sets.cfg",
      "Sets.tla",
    ]);
  });

  it.each(["../../etc", "/etc", "intro/../..", "intro/", "a b", ""])("rejects folder %p", (dir) => {
    const res = run(payload({ dir }));
    expect(res.status).toBe(1);
    expect(res.stderr).toContain("invalid folder");
    expect(written()).toEqual([]);
  });

  it.each([
    ["spec", { spec: file("../evil.tla") }],
    ["spec", { spec: file("Sets.cfg") }],
    ["spec", { spec: { content: "x" } }],
    ["cfg", { cfg: file("Sets.tla") }],
    ["cfg", { cfg: file("../Sets.cfg") }],
    ["extra", { extra: [file("sub/Helper.tla")] }],
  ])("rejects a bad %s file name", (_, overrides) => {
    const res = run(payload(overrides));
    expect(res.status).toBe(1);
    expect(res.stderr).toContain("invalid file name");
    expect(fs.existsSync(path.join(root, "evil.tla"))).toBe(false);
    expect(fs.existsSync(path.join(root, "playground", "Sets.cfg"))).toBe(false);
  });

  it.each([
    ["a missing payload", "\n", "missing payload"],
    ["an undecodable payload", "not-json\n", "could not decode"],
    ["an unknown version", Buffer.from(JSON.stringify({ ...payload(), v: 2 })).toString("base64url"), "unsupported payload version"],
  ])("rejects %s", (_, input, message) => {
    const res = runRaw(input);
    expect(res.status).toBe(1);
    expect(res.stderr).toContain(message);
    expect(written()).toEqual([]);
  });

  it("accepts payloads larger than a single program argument may be", () => {
    // Linux caps one argv entry at 128 KiB; stdin has no such limit.
    const big = { name: "Sets.tla", content: `(* ${"x".repeat(300_000)} *)` };
    const res = run(payload({ spec: big }));
    expect(res.stdout).toContain("Wrote 2 file(s)");
    expect(fs.readFileSync(path.join(root, "playground", "intro", "sets", "Sets.tla"), "utf-8")).toBe(big.content + "\n");
  });
});
