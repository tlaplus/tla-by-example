"use client";

import dynamic from "next/dynamic";
import Navbar from "@/components/Navbar";
import SplitLayout from "@/components/SplitLayout";
import type { Lesson, LessonNavInfo } from "@/lib/lessons";
import type { PlaygroundTab, PlaygroundTlcConfig } from "@/components/Playground";

const Playground = dynamic(() => import("@/components/Playground"), { ssr: false });

function sectionPath(lesson: LessonNavInfo): string {
  return lesson.section === "intro"
    ? `/intro/${lesson.slug}`
    : `/blocking-queue/${lesson.slug}`;
}

function sectionLabel(section: string): string {
  return section === "intro" ? "How to Write TLA+" : "BlockingQueue Tutorial";
}

function extractModuleName(spec: string): string {
  const match = spec.match(/^-{4,}\s*MODULE\s+(\w+)\s*-{4,}/m);
  return match ? match[1] : "Spec";
}

interface LessonLayoutProps {
  lesson: Lesson;
  prev?: LessonNavInfo;
  next?: LessonNavInfo;
  children: React.ReactNode;
}

export default function LessonLayout({ lesson, prev, next, children }: LessonLayoutProps) {
  const moduleName = extractModuleName(lesson.spec);
  const lessonTabs = lesson.tabs ?? ["spec", "cfg"];

  const tabs: PlaygroundTab[] = [];
  if (lessonTabs.includes("spec")) {
    tabs.push({ id: "spec", label: `${moduleName}.tla`, initialContent: lesson.spec, lang: "tla" });
  }
  if (lessonTabs.includes("cfg")) {
    tabs.push({ id: "cfg", label: `${moduleName}.cfg`, initialContent: lesson.cfg, lang: "cfg" });
  }
  for (const et of lesson.extraTabs ?? []) {
    tabs.push({ id: `extra-${et.label}`, label: et.label, initialContent: et.content, lang: "text" });
  }

  const tlcConfigs: PlaygroundTlcConfig[] = (lessonTabs.includes("spec") && lessonTabs.includes("cfg"))
    ? [{ label: `${moduleName}.cfg`, specTabId: "spec", cfgTabId: "cfg" }]
    : [];

  return (
    <SplitLayout
      navbar={
        <Navbar
          breadcrumbs={[
            { label: sectionLabel(lesson.section) },
            { label: lesson.title },
          ]}
          prev={prev ? { label: prev.title, href: sectionPath(prev) } : undefined}
          next={next ? { label: next.title, href: sectionPath(next) } : undefined}
        />
      }
      left={children}
      right={<Playground tabs={tabs} tlcConfigs={tlcConfigs} />}
    />
  );
}
