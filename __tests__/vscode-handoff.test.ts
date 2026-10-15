/**
 * @jest-environment node
 */
import { buildCommand, buildPayload, CODESPACES_URL } from "@/lib/vscode-handoff";

function decodeCommand(command: string) {
  const [echo, arg, ...rest] = command.split(" ");
  expect([echo, rest]).toEqual(["echo", ["|", "node", "scripts/run-in-codespace.mjs"]]);
  expect(arg).toMatch(/^[A-Za-z0-9_-]+$/); // shell-safe base64url
  return JSON.parse(Buffer.from(arg, "base64url").toString("utf-8"));
}

describe("vscode-handoff", () => {
  it("points at the tlaplus repo by default", () => {
    expect(CODESPACES_URL).toBe("https://codespaces.new/tlaplus/tla-by-example?quickstart=1");
  });

  it("names files after the MODULE so TLC can find them on disk", () => {
    const payload = buildPayload(
      "intro/module-structure",
      { name: "MySpec.tla", content: "---- MODULE Renamed ----\nEXTENDS Helper\n====" },
      { name: "MySpec.cfg", content: "INIT Init" },
      [{ name: "Helper.tla", content: "---- MODULE Helper ----\n====" }],
    );
    expect(payload.spec.name).toBe("Renamed.tla");
    expect(payload.cfg.name).toBe("Renamed.cfg");
    expect(payload.extra.map((m) => m.name)).toEqual(["Helper.tla"]);
  });

  it("sanitizes the target folder", () => {
    const payload = buildPayload("specs/My Spec (v2)", { name: "A.tla", content: "" }, { name: "A.cfg", content: "" });
    expect(payload.dir).toBe("specs/My-Spec--v2-");
  });

  it("round-trips non-ASCII content through the pasted command", () => {
    const spec = "---- MODULE U ----\n(* ∀ x ∈ S : x ≥ 0 — ok *)\n====";
    const payload = buildPayload("intro/u", { name: "U.tla", content: spec }, { name: "U.cfg", content: "INIT Init" });
    expect(decodeCommand(buildCommand(payload))).toEqual(payload);
  });

  it("leaves out extra modules the spec does not (transitively) use", () => {
    const mod = (name: string, body = "") => ({ name: `${name}.tla`, content: `---- MODULE ${name} ----\n${body}\n====` });
    const payload = buildPayload(
      "specs/x",
      mod("MC", "EXTENDS Naturals, Spec"),
      { name: "MC.cfg", content: "" },
      [mod("Spec", "LOCAL I == INSTANCE Channel WITH x <- y"), mod("Channel", "EXTENDS Base"), mod("Base"), mod("Unused")],
    );
    expect(payload.extra.map((m) => m.name).sort()).toEqual(["Base.tla", "Channel.tla", "Spec.tla"]);
  });
});
