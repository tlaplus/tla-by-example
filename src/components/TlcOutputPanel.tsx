"use client";

import type { TlcRunnerState } from "@/lib/useTlcRunner";

interface TlcOutputPanelProps {
  runner: TlcRunnerState;
}

export default function TlcOutputPanel({ runner }: TlcOutputPanelProps) {
  return (
    <div
      className={`border-t border-gray-200 bg-gray-50 transition-all duration-300 ${
        runner.outputOpen ? "h-48" : "h-8"
      }`}
    >
      <button
        onClick={() => runner.setOutputOpen(!runner.outputOpen)}
        className="flex w-full items-center gap-2 px-3 py-1.5 text-xs font-medium text-gray-500 hover:text-gray-700"
      >
        <span className={`transition-transform ${runner.outputOpen ? "rotate-180" : ""}`}>▼</span>
        TLC Output
      </button>
      {runner.outputOpen && (
        <div className="h-[calc(100%-2rem)] overflow-auto px-3 pb-2">
          <pre className="text-xs font-mono text-gray-700 whitespace-pre-wrap leading-relaxed">
            {runner.rawOutput || "Press ▶ Run TLC to check the model."}
          </pre>
        </div>
      )}
    </div>
  );
}
