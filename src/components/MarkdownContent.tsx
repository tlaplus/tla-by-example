"use client";

import { useMemo } from "react";

interface MarkdownContentProps {
  content: string;
}

function parseMarkdown(md: string): string {
  let html = md;

  // Code blocks (```) - extract to placeholders to protect from further processing
  const codeBlocks: string[] = [];
  html = html.replace(/```([a-z]*)\n([\s\S]*?)```/g, (_match, _lang, code) => {
    const placeholder = `<!--codeblock-${codeBlocks.length}-->`;
    codeBlocks.push(`<pre class="bg-gray-100 border border-gray-200 rounded-lg p-4 overflow-x-auto text-sm"><code>${escapeHtml(code.trim())}</code></pre>`);
    return placeholder;
  });

  // Inline code
  html = html.replace(/`([^`]+)`/g, (_match, code) => `<code class="bg-gray-100 px-1.5 py-0.5 rounded text-sm font-mono text-gray-800">${escapeHtml(code)}</code>`);

  // Headers
  html = html.replace(/^### (.+)$/gm, '<h3 class="text-lg font-semibold text-gray-900 mt-6 mb-2">$1</h3>');
  html = html.replace(/^## (.+)$/gm, '<h2 class="text-xl font-semibold text-gray-900 mt-8 mb-3">$1</h2>');
  html = html.replace(/^# (.+)$/gm, '<h1 class="text-2xl font-bold text-gray-900 mt-4 mb-4">$1</h1>');

  // Bold and italic
  html = html.replace(/\*\*(.+?)\*\*/g, '<strong class="font-semibold">$1</strong>');
  html = html.replace(/\*(.+?)\*/g, '<em>$1</em>');

  // YouTube embeds: ![youtube](URL)
  html = html.replace(/!\[youtube\]\((?:https?:\/\/)?(?:www\.)?(?:youtube\.com\/watch\?v=|youtu\.be\/)([a-zA-Z0-9_-]+)[^)]*\)/g,
    '<div class="my-4 aspect-video"><iframe src="https://www.youtube.com/embed/$1" class="w-full h-full rounded-lg" frameborder="0" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture" allowfullscreen></iframe></div>');

  // Images (must be before links)
  html = html.replace(/!\[([^\]]*)\]\(([^)]+)\)/g, '<img src="$2" alt="$1" class="my-4 max-w-full rounded-lg border border-gray-200" />');

  // Links
  html = html.replace(/\[([^\]]+)\]\(([^)]+)\)/g, '<a href="$2" class="text-blue-600 hover:underline" target="_blank" rel="noopener noreferrer">$1</a>');

  // Tables
  html = html.replace(/^\|(.+)\|$/gm, (match) => {
    const cells = match.split('|').filter(c => c.trim());
    if (cells.every(c => /^[\s-:]+$/.test(c))) {
      return '<!-- table-separator -->'; // separator row placeholder to keep rows consecutive
    }
    const tag = 'td';
    const cellsHtml = cells.map(c =>
      `<${tag} class="border border-gray-200 px-3 py-2 text-sm">${c.trim()}</${tag}>`
    ).join('');
    return `<tr>${cellsHtml}</tr>`;
  });
  // Wrap consecutive tr elements in table (skip separator placeholders)
  html = html.replace(/((?:(?:<tr>.*<\/tr>|<!-- table-separator -->)\n?)+)/g, (match) => {
    const cleaned = match.replace(/<!-- table-separator -->\n?/g, '');
    return `<div class="overflow-x-auto my-4"><table class="border-collapse border border-gray-200 w-full">${cleaned}</table></div>`;
  });

  // Unordered lists
  html = html.replace(/^- (.+)$/gm, '<li class="ml-4 list-disc text-gray-700">$1</li>');
  html = html.replace(/((?:<li[^>]*>.*<\/li>\n?)+)/g, '<ul class="my-2 space-y-1">$1</ul>');

  // Ordered lists
  html = html.replace(/^\d+\. (.+)$/gm, '<li class="ml-4 list-decimal text-gray-700">$1</li>');

  // Paragraphs: wrap remaining lines that aren't already HTML
  const lines = html.split('\n');
  const result: string[] = [];
  let inParagraph = false;

  for (const line of lines) {
    const trimmed = line.trim();
    if (!trimmed) {
      if (inParagraph) {
        result.push('</p>');
        inParagraph = false;
      }
      continue;
    }
    if (trimmed.startsWith('<')) {
      if (inParagraph) {
        result.push('</p>');
        inParagraph = false;
      }
      result.push(line);
    } else {
      if (!inParagraph) {
        result.push('<p class="text-gray-700 leading-relaxed mb-3">');
        inParagraph = true;
      }
      result.push(line);
    }
  }
  if (inParagraph) result.push('</p>');

  // Restore code blocks from placeholders
  let output = result.join('\n');
  codeBlocks.forEach((block, i) => {
    output = output.replace(`<!--codeblock-${i}-->`, block);
  });

  return output;
}

function escapeHtml(s: string): string {
  return s
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;');
}

export default function MarkdownContent({ content }: MarkdownContentProps) {
  const html = useMemo(() => parseMarkdown(content), [content]);
  return <div dangerouslySetInnerHTML={{ __html: html }} />;
}
