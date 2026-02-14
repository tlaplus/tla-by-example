"use client";

import { useEffect, useRef } from "react";
import { basicSetup, EditorView } from "codemirror";
import { EditorState, Extension } from "@codemirror/state";

interface CodeEditorProps {
  value: string;
  onChange: (value: string) => void;
  height?: string;
  language?: Extension;
}

const lightTheme = EditorView.theme({
  "&": { fontSize: "14px", backgroundColor: "#ffffff" },
  ".cm-scroller": { overflow: "auto" },
  ".cm-content": { fontFamily: "'JetBrains Mono', 'Fira Code', 'Consolas', monospace" },
  ".cm-gutters": { backgroundColor: "#f8f9fa", borderRight: "1px solid #e5e7eb" },
  ".cm-activeLineGutter": { backgroundColor: "#e8f0fe" },
  ".cm-activeLine": { backgroundColor: "#f3f4f6" },
});

export default function CodeEditor({ value, onChange, height = "100%", language }: CodeEditorProps) {
  const containerRef = useRef<HTMLDivElement>(null);
  const viewRef = useRef<EditorView | null>(null);

  useEffect(() => {
    if (!containerRef.current) return;

    const extensions: Extension[] = [
      basicSetup,
      lightTheme,
      EditorView.theme({ "&": { height } }),
      EditorView.updateListener.of((update) => {
        if (update.docChanged) {
          onChange(update.state.doc.toString());
        }
      }),
    ];
    if (language) extensions.push(language);

    const state = EditorState.create({ doc: value, extensions });
    const view = new EditorView({ state, parent: containerRef.current });
    viewRef.current = view;

    return () => { view.destroy(); };
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  return <div ref={containerRef} style={{ height, overflow: "hidden" }} />;
}
