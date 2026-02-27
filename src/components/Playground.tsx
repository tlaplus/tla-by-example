"use client";

import { useState, useCallback, useMemo } from "react";
import dynamic from "next/dynamic";
import { tlaplus, tlaCfg } from "@/lib/tlaplus-lang";
import { useTlcRunner } from "@/lib/useTlcRunner";
import RunTlcButton from "@/components/RunTlcButton";
import TlcOutputPanel from "@/components/TlcOutputPanel";

const CodeEditor = dynamic(() => import("@/components/CodeEditor"), { ssr: false });

export interface PlaygroundTab {
  id: string;
  label: string;
  initialContent: string;
  lang: "tla" | "cfg" | "text";
}

export interface PlaygroundTlcConfig {
  label: string;
  specTabId: string;
  cfgTabId: string;
  extraModuleTabIds?: string[];
  isDefault?: boolean;
}

interface PlaygroundProps {
  tabs: PlaygroundTab[];
  tlcConfigs?: PlaygroundTlcConfig[];
}

export default function Playground({ tabs, tlcConfigs = [] }: PlaygroundProps) {
  const [activeTabId, setActiveTabId] = useState(tabs[0]?.id ?? "");
  const [showConfigPicker, setShowConfigPicker] = useState(false);

  // Editable content state per tab
  const [tabContents, setTabContents] = useState<Record<string, string>>(() => {
    const m: Record<string, string> = {};
    for (const t of tabs) m[t.id] = t.initialContent;
    return m;
  });

  const updateTabContent = useCallback((id: string, value: string) => {
    setTabContents((prev) => ({ ...prev, [id]: value }));
  }, []);

  const hasConfigs = tlcConfigs.length > 0;
  const runner = useTlcRunner(hasConfigs);

  const defaultIdx = useMemo(
    () => Math.max(0, tlcConfigs.findIndex((c) => c.isDefault)),
    [tlcConfigs],
  );

  const doRun = useCallback(
    (config: PlaygroundTlcConfig) => {
      setShowConfigPicker(false);
      const specContent = tabContents[config.specTabId] ?? "";
      const cfgContent = tabContents[config.cfgTabId] ?? "";
      const extraModules = (config.extraModuleTabIds ?? []).map((id) => {
        const tab = tabs.find((t) => t.id === id);
        return { name: tab?.label ?? id, content: tabContents[id] ?? "" };
      });
      runner.run(specContent, cfgContent, extraModules);
    },
    [tabContents, tabs, runner],
  );

  const handleRunClick = useCallback(() => {
    if (tlcConfigs.length === 1) {
      doRun(tlcConfigs[0]);
    } else {
      setShowConfigPicker((prev) => !prev);
    }
  }, [tlcConfigs, doRun]);

  if (tabs.length === 0) {
    return (
      <div className="flex h-full items-center justify-center text-gray-400 text-sm">
        No modules available
      </div>
    );
  }

  return (
    <div className="flex flex-col h-full border-l border-gray-200">
      {/* Tab bar */}
      <div className="flex items-center border-b border-gray-200 bg-gray-50 px-2 overflow-x-auto">
        {tabs.map((tab) => (
          <button
            key={tab.id}
            onClick={() => setActiveTabId(tab.id)}
            className={`px-4 py-2 text-sm font-medium border-b-2 transition-colors whitespace-nowrap ${
              activeTabId === tab.id
                ? "border-blue-600 text-blue-600"
                : "border-transparent text-gray-500 hover:text-gray-700"
            }`}
          >
            {tab.label}
          </button>
        ))}
        {hasConfigs && (
          <div className="ml-auto pr-2 relative">
            <RunTlcButton
              isRunning={runner.isRunning}
              isReady={runner.isReady}
              onClick={handleRunClick}
            />
            {showConfigPicker && (
              <div className="absolute right-0 top-full mt-1 z-20 bg-white border border-gray-200 rounded-lg shadow-lg py-1 min-w-[220px]">
                <div className="px-3 py-1.5 text-xs font-medium text-gray-400 uppercase tracking-wide">
                  Select configuration
                </div>
                {tlcConfigs.map((config, i) => (
                  <button
                    key={`${config.specTabId}-${config.cfgTabId}`}
                    onClick={() => doRun(config)}
                    className={`w-full text-left px-3 py-2 text-sm hover:bg-blue-50 transition-colors ${
                      i === defaultIdx ? "font-medium text-blue-700" : "text-gray-700"
                    }`}
                  >
                    <span className="block">{config.label}</span>
                    {tlcConfigs.length > 1 && (
                      <span className="block text-xs text-gray-400">
                        spec: {tabs.find((t) => t.id === config.specTabId)?.label}
                        {i === defaultIdx && " (default)"}
                      </span>
                    )}
                  </button>
                ))}
              </div>
            )}
          </div>
        )}
      </div>

      {/* Editor area */}
      <div className="flex-1 relative min-h-0">
        {tabs.map((tab) => (
          <div
            key={tab.id}
            className="absolute inset-0"
            style={{ display: activeTabId === tab.id ? "block" : "none" }}
          >
            {tab.lang === "text" ? (
              <div className="h-full overflow-auto bg-gray-50 p-4">
                <pre className="text-sm font-mono text-gray-800 whitespace-pre-wrap leading-relaxed">
                  {tabContents[tab.id]}
                </pre>
              </div>
            ) : (
              <CodeEditor
                value={tabContents[tab.id] ?? ""}
                onChange={(v) => updateTabContent(tab.id, v)}
                language={tab.lang === "tla" ? tlaplus() : tlaCfg()}
              />
            )}
          </div>
        ))}
      </div>

      <TlcOutputPanel runner={runner} />
    </div>
  );
}
