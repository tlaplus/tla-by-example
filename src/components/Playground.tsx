"use client";

import { useState, useCallback, useEffect } from "react";
import dynamic from "next/dynamic";
import { initCheerpJ, runTlc, isCheerpJReady } from "@/lib/cheerpj";
import { tlaplus, tlaCfg } from "@/lib/tlaplus-lang";
import type { ExtraTab } from "@/lib/lessons";

const CodeEditor = dynamic(() => import("@/components/CodeEditor"), { ssr: false });

type EditorTab = "spec" | "cfg";

interface PlaygroundProps {
  initialSpec: string;
  initialCfg: string;
  tabs?: EditorTab[];
  extraTabs?: ExtraTab[];
}

export default function Playground({
  initialSpec,
  initialCfg,
  tabs = ["spec", "cfg"],
  extraTabs = [],
}: PlaygroundProps) {
  const [spec, setSpec] = useState(initialSpec);
  const [cfg, setCfg] = useState(initialCfg);
  const [activeTab, setActiveTab] = useState<string>(tabs[0] || "spec");
  const [rawOutput, setRawOutput] = useState("");
  const [isRunning, setIsRunning] = useState(false);
  const [isReady, setIsReady] = useState(false);
  const [outputOpen, setOutputOpen] = useState(false);

  useEffect(() => {
    initCheerpJ()
      .then(() => setIsReady(true))
      .catch((err) => {
        setRawOutput(`Failed to initialize CheerpJ: ${err.message}`);
      });
  }, []);

  const handleRun = useCallback(async () => {
    if (!isCheerpJReady()) return;
    setIsRunning(true);
    setRawOutput("");
    setOutputOpen(true);

    try {
      const result = await runTlc(spec, cfg, { workers: 1, checkDeadlock: true }, (line) => {
        if (line.trim()) setRawOutput((prev) => prev + line + "\n");
      });
      setRawOutput(result);
    } catch (err: unknown) {
      const message = err instanceof Error ? err.message : String(err);
      setRawOutput(`Error: ${message}`);
    } finally {
      setIsRunning(false);
      setIsReady(false);
      setRawOutput((prev) => prev + "\nReloading CheerpJ...");
      initCheerpJ()
        .then(() => {
          setIsReady(true);
          setRawOutput((prev) => prev.replace("\nReloading CheerpJ...", ""));
        })
        .catch(() => setIsReady(false));
    }
  }, [spec, cfg]);

  const activeExtra = extraTabs.find((t) => t.label === activeTab);

  return (
    <div className="flex flex-col h-full border-l border-gray-200">
      {/* Tab bar */}
      <div className="flex items-center border-b border-gray-200 bg-gray-50 px-2">
        {tabs.map((tab) => (
          <button
            key={tab}
            onClick={() => setActiveTab(tab)}
            className={`px-4 py-2 text-sm font-medium border-b-2 transition-colors ${
              activeTab === tab
                ? "border-blue-600 text-blue-600"
                : "border-transparent text-gray-500 hover:text-gray-700"
            }`}
          >
            {tab === "spec" ? "Spec.tla" : "Spec.cfg"}
          </button>
        ))}
        {extraTabs.map((et) => (
          <button
            key={et.label}
            onClick={() => setActiveTab(et.label)}
            className={`px-4 py-2 text-sm font-medium border-b-2 transition-colors ${
              activeTab === et.label
                ? "border-blue-600 text-blue-600"
                : "border-transparent text-gray-500 hover:text-gray-700"
            }`}
          >
            {et.label}
          </button>
        ))}
        <div className="ml-auto pr-2">
          <button
            onClick={handleRun}
            disabled={isRunning || !isReady}
            className={`rounded px-4 py-1.5 text-sm font-semibold transition-colors ${
              isRunning || !isReady
                ? "bg-gray-200 text-gray-400 cursor-not-allowed"
                : "bg-green-600 text-white hover:bg-green-700"
            }`}
          >
            {isRunning ? "⏳ Running..." : isReady ? "▶ Run TLC" : "⏳ Loading..."}
          </button>
        </div>
      </div>

      {/* Editor area */}
      <div className="flex-1 relative min-h-0">
        {tabs.includes("spec") && (
          <div
            className="absolute inset-0"
            style={{ display: activeTab === "spec" ? "block" : "none" }}
          >
            <CodeEditor value={spec} onChange={setSpec} language={tlaplus()} />
          </div>
        )}
        {tabs.includes("cfg") && (
          <div
            className="absolute inset-0"
            style={{ display: activeTab === "cfg" ? "block" : "none" }}
          >
            <CodeEditor value={cfg} onChange={setCfg} language={tlaCfg()} />
          </div>
        )}
        {extraTabs.map((et) => (
          <div
            key={et.label}
            className="absolute inset-0"
            style={{ display: activeTab === et.label ? "block" : "none" }}
          >
            {activeExtra?.label === et.label && (
              <div className="h-full overflow-auto bg-gray-50 p-4">
                <pre className="text-sm font-mono text-gray-800 whitespace-pre-wrap leading-relaxed">
                  {et.content}
                </pre>
              </div>
            )}
          </div>
        ))}
      </div>

      {/* Output panel */}
      <div
        className={`border-t border-gray-200 bg-gray-50 transition-all duration-300 ${
          outputOpen ? "h-48" : "h-8"
        }`}
      >
        <button
          onClick={() => setOutputOpen(!outputOpen)}
          className="flex w-full items-center gap-2 px-3 py-1.5 text-xs font-medium text-gray-500 hover:text-gray-700"
        >
          <span className={`transition-transform ${outputOpen ? "rotate-180" : ""}`}>▼</span>
          TLC Output
        </button>
        {outputOpen && (
          <div className="h-[calc(100%-2rem)] overflow-auto px-3 pb-2">
            <pre className="text-xs font-mono text-gray-700 whitespace-pre-wrap leading-relaxed">
              {rawOutput || "Press ▶ Run TLC to check the model."}
            </pre>
          </div>
        )}
      </div>
    </div>
  );
}
