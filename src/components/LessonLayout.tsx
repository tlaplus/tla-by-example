"use client";

import { useState, useCallback } from "react";
import dynamic from "next/dynamic";
import Navbar from "@/components/Navbar";
import Footer from "@/components/Footer";
import ResizableDivider from "@/components/ResizableDivider";
import type { Lesson, LessonNavInfo } from "@/lib/lessons";

const Playground = dynamic(() => import("@/components/Playground"), { ssr: false });

interface LessonLayoutProps {
  lesson: Lesson;
  prev?: LessonNavInfo;
  next?: LessonNavInfo;
  children: React.ReactNode;
}

export default function LessonLayout({ lesson, prev, next, children }: LessonLayoutProps) {
  const [explanationWidth, setExplanationWidth] = useState(45);

  const handleResize = useCallback((delta: number) => {
    setExplanationWidth((w) => {
      const containerWidth = window.innerWidth;
      const deltaPercent = (delta / containerWidth) * 100;
      return Math.max(25, Math.min(65, w + deltaPercent));
    });
  }, []);

  const current: LessonNavInfo = {
    slug: lesson.slug,
    title: lesson.title,
    section: lesson.section,
  };

  return (
    <div className="flex flex-col h-screen">
      <Navbar current={current} prev={prev} next={next} />

      <div className="flex flex-1 min-h-0">
        {/* Left: explanation */}
        <div
          className="overflow-y-auto bg-white"
          style={{ width: `${explanationWidth}%` }}
        >
          <div className="max-w-none px-8 py-6 prose prose-sm prose-gray">
            {children}
          </div>
        </div>

        <ResizableDivider direction="horizontal" onResize={handleResize} />

        {/* Right: playground */}
        <div className="flex-1 min-w-0">
          <Playground
            initialSpec={lesson.spec}
            initialCfg={lesson.cfg}
            tabs={lesson.tabs}
          />
        </div>
      </div>

      <Footer />
    </div>
  );
}
