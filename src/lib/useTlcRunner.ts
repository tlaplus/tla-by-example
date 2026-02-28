"use client";

import { useState, useCallback, useEffect } from "react";
import { initCheerpJ, runTlc, isCheerpJReady } from "@/lib/cheerpj";
import type { ExtraModule } from "@/lib/cheerpj";

export interface TlcRunnerState {
  rawOutput: string;
  isRunning: boolean;
  isReady: boolean;
  outputOpen: boolean;
  setOutputOpen: (open: boolean) => void;
  run: (spec: string, cfg: string, extraModules?: ExtraModule[]) => void;
}

export function useTlcRunner(enabled = true): TlcRunnerState {
  const [rawOutput, setRawOutput] = useState("");
  const [isRunning, setIsRunning] = useState(false);
  const [isReady, setIsReady] = useState(false);
  const [outputOpen, setOutputOpen] = useState(false);

  useEffect(() => {
    if (!enabled) return;
    initCheerpJ()
      .then(() => setIsReady(true))
      .catch((err) => {
        setRawOutput(`Failed to initialize CheerpJ: ${err.message}`);
      });
  }, [enabled]);

  const run = useCallback(
    async (spec: string, cfg: string, extraModules?: ExtraModule[]) => {
      if (!isCheerpJReady()) return;
      setIsRunning(true);
      setRawOutput("");
      setOutputOpen(true);

      try {
        const result = await runTlc(
          spec,
          cfg,
          { workers: 1, checkDeadlock: true },
          (line) => {
            if (line.trim()) setRawOutput((prev) => prev + line + "\n");
          },
          extraModules,
        );
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
    },
    [],
  );

  return { rawOutput, isRunning, isReady, outputOpen, setOutputOpen, run };
}
