/**
 * @jest-environment jsdom
 */
import React from "react";
import { TextEncoder } from "util";
import { render, screen, fireEvent } from "@testing-library/react";
import "@testing-library/jest-dom";
import Playground, { type PlaygroundTab, type PlaygroundTlcConfig } from "@/components/Playground";
import { CODESPACES_URL } from "@/lib/vscode-handoff";

// jest-environment-jsdom lacks TextEncoder, which browsers have.
Object.assign(globalThis, { TextEncoder });

// CodeMirror and CheerpJ need a real browser; neither matters for the handoff.
jest.mock("next/dynamic", () => () => () => null);
jest.mock("@/lib/useTlcRunner", () => ({
  useTlcRunner: () => ({
    rawOutput: "",
    isRunning: false,
    isReady: true,
    outputOpen: false,
    setOutputOpen: jest.fn(),
    run: jest.fn(),
  }),
}));

const SPEC = "---- MODULE Counter ----\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1\n====";

function setup(props: { vscodeDir?: string }) {
  const tabs: PlaygroundTab[] = [
    { id: "spec", label: "Counter.tla", initialContent: SPEC, lang: "tla" },
    { id: "cfg", label: "Counter.cfg", initialContent: "INIT Init\nNEXT Next", lang: "cfg" },
  ];
  const tlcConfigs: PlaygroundTlcConfig[] = [{ label: "Counter.cfg", specTabId: "spec", cfgTabId: "cfg" }];
  render(<Playground tabs={tabs} tlcConfigs={tlcConfigs} vscodeDir={props.vscodeDir} />);
}

describe("Playground: Run in VS Code", () => {
  let writeText: jest.Mock;
  let open: jest.SpyInstance;

  beforeEach(() => {
    writeText = jest.fn().mockResolvedValue(undefined);
    Object.defineProperty(navigator, "clipboard", { value: { writeText }, configurable: true });
    open = jest.spyOn(window, "open").mockImplementation(() => null);
  });

  afterEach(() => open.mockRestore());

  it("is hidden without vscodeDir", () => {
    setup({});
    expect(screen.queryByRole("button", { name: "Run in VS Code" })).not.toBeInTheDocument();
  });

  it("copies the command, opens the codespace and shows the command", () => {
    setup({ vscodeDir: "intro/counter" });
    fireEvent.click(screen.getByRole("button", { name: "Run in VS Code" }));

    expect(open).toHaveBeenCalledWith(CODESPACES_URL, "_blank", "noopener");
    expect(writeText).toHaveBeenCalledTimes(1);
    const command = writeText.mock.calls[0][0] as string;
    const payload = JSON.parse(Buffer.from(command.split(" ")[1], "base64url").toString("utf-8"));
    expect(payload).toMatchObject({
      dir: "intro/counter",
      spec: { name: "Counter.tla", content: SPEC },
      cfg: { name: "Counter.cfg", content: "INIT Init\nNEXT Next" },
    });
    expect(screen.getByLabelText("Command to paste into the codespace terminal")).toHaveValue(command);

    fireEvent.click(screen.getByRole("button", { name: "Dismiss" }));
    expect(screen.queryByLabelText("Command to paste into the codespace terminal")).not.toBeInTheDocument();
  });
});
