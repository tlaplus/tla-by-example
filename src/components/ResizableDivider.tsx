"use client";

import { useCallback, useRef } from "react";

interface ResizableDividerProps {
  direction: "horizontal" | "vertical";
  onResize: (delta: number) => void;
}

export default function ResizableDivider({ direction, onResize }: ResizableDividerProps) {
  const dragging = useRef(false);
  const lastPos = useRef(0);

  const onMouseDown = useCallback((e: React.MouseEvent) => {
    e.preventDefault();
    dragging.current = true;
    lastPos.current = direction === "horizontal" ? e.clientX : e.clientY;

    const onMouseMove = (ev: MouseEvent) => {
      if (!dragging.current) return;
      const pos = direction === "horizontal" ? ev.clientX : ev.clientY;
      const delta = pos - lastPos.current;
      lastPos.current = pos;
      onResize(delta);
    };

    const onMouseUp = () => {
      dragging.current = false;
      document.removeEventListener("mousemove", onMouseMove);
      document.removeEventListener("mouseup", onMouseUp);
      document.body.style.cursor = "";
      document.body.style.userSelect = "";
    };

    document.addEventListener("mousemove", onMouseMove);
    document.addEventListener("mouseup", onMouseUp);
    document.body.style.cursor = direction === "horizontal" ? "col-resize" : "row-resize";
    document.body.style.userSelect = "none";
  }, [direction, onResize]);

  const isH = direction === "horizontal";

  return (
    <div
      onMouseDown={onMouseDown}
      style={{
        width: isH ? "4px" : "100%",
        height: isH ? "100%" : "4px",
        cursor: isH ? "col-resize" : "row-resize",
        backgroundColor: "transparent",
        flexShrink: 0,
        position: "relative",
        zIndex: 10,
      }}
    >
      <div style={{
        position: "absolute",
        [isH ? "left" : "top"]: "1px",
        [isH ? "top" : "left"]: 0,
        [isH ? "width" : "height"]: "2px",
        [isH ? "height" : "width"]: "100%",
        backgroundColor: "#e5e7eb",
        transition: "background-color 0.15s",
      }} />
    </div>
  );
}
