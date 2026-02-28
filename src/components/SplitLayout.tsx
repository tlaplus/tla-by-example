"use client";

import { useState, useCallback } from "react";
import Footer from "@/components/Footer";
import ResizableDivider from "@/components/ResizableDivider";

interface SplitLayoutProps {
  navbar: React.ReactNode;
  left: React.ReactNode;
  right: React.ReactNode;
}

export default function SplitLayout({ navbar, left, right }: SplitLayoutProps) {
  const [leftWidth, setLeftWidth] = useState(45);

  const handleResize = useCallback((delta: number) => {
    setLeftWidth((w) => {
      const containerWidth = window.innerWidth;
      const deltaPercent = (delta / containerWidth) * 100;
      return Math.max(25, Math.min(65, w + deltaPercent));
    });
  }, []);

  return (
    <div className="flex flex-col h-screen">
      {navbar}

      <div className="flex flex-1 min-h-0">
        <div
          className="overflow-y-auto bg-white"
          style={{ width: `${leftWidth}%` }}
        >
          <div className="max-w-none px-8 py-6 prose prose-sm prose-gray">
            {left}
          </div>
        </div>

        <ResizableDivider direction="horizontal" onResize={handleResize} />

        <div className="flex-1 min-w-0">
          {right}
        </div>
      </div>

      <Footer />
    </div>
  );
}
