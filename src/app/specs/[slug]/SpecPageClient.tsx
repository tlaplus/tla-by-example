"use client";

import Navbar from "@/components/Navbar";
import MarkdownContent from "@/components/MarkdownContent";
import SplitLayout from "@/components/SplitLayout";
import dynamic from "next/dynamic";
import type { SpecModule } from "@/lib/specs";
import type { PlaygroundTab, PlaygroundTlcConfig } from "@/components/Playground";

const Playground = dynamic(() => import("@/components/Playground"), { ssr: false });

function buildSpecTabs(modules: SpecModule[]): PlaygroundTab[] {
  const tabs: PlaygroundTab[] = [];
  for (const mod of modules) {
    tabs.push({
      id: `tla-${mod.filename}`,
      label: mod.filename,
      initialContent: mod.content,
      lang: "tla",
    });
    for (const cfg of mod.cfgFiles) {
      tabs.push({
        id: `cfg-${cfg.filename}`,
        label: cfg.filename,
        initialContent: cfg.content,
        lang: "cfg",
      });
    }
  }
  return tabs;
}

function buildSpecTlcConfigs(modules: SpecModule[]): PlaygroundTlcConfig[] {
  const configs: PlaygroundTlcConfig[] = [];
  for (const mod of modules) {
    for (const cfg of mod.cfgFiles) {
      const extraModuleTabIds = modules
        .filter((m) => m.filename !== mod.filename)
        .map((m) => `tla-${m.filename}`);
      const isMC = mod.filename.startsWith("MC") || mod.filename.startsWith("MC_");
      configs.push({
        label: cfg.filename,
        specTabId: `tla-${mod.filename}`,
        cfgTabId: `cfg-${cfg.filename}`,
        extraModuleTabIds,
        isDefault: isMC,
      });
    }
  }
  return configs;
}

interface SpecPageClientProps {
  name: string;
  readme: string;
  modules: SpecModule[];
}

export default function SpecPageClient({ name, readme, modules }: SpecPageClientProps) {
  const tabs = buildSpecTabs(modules);
  const tlcConfigs = buildSpecTlcConfigs(modules);

  return (
    <SplitLayout
      navbar={
        <Navbar
          breadcrumbs={[
            { label: "Specifications", href: "/#specifications" },
            { label: name },
          ]}
        />
      }
      left={<MarkdownContent content={readme} />}
      right={<Playground tabs={tabs} tlcConfigs={tlcConfigs} />}
    />
  );
}
