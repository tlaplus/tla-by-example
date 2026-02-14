import Link from "next/link";
import type { LessonNavInfo } from "@/lib/lessons";

interface NavbarProps {
  current: LessonNavInfo;
  prev?: LessonNavInfo;
  next?: LessonNavInfo;
}

function sectionPath(lesson: LessonNavInfo): string {
  return lesson.section === "intro"
    ? `/intro/${lesson.slug}`
    : `/blocking-queue/${lesson.slug}`;
}

export default function Navbar({ current, prev, next }: NavbarProps) {
  const sectionLabel =
    current.section === "intro" ? "How to Write TLA+" : "BlockingQueue Tutorial";

  return (
    <nav className="flex items-center justify-between border-b border-gray-200 bg-white px-4 py-3">
      <div className="flex items-center gap-3">
        <Link
          href="/"
          className="text-lg font-bold text-gray-900 hover:text-blue-600 transition-colors"
        >
          TLA+ By Example
        </Link>
        <span className="text-gray-300">/</span>
        <span className="text-sm text-gray-500">{sectionLabel}</span>
        <span className="text-gray-300">/</span>
        <span className="text-sm font-medium text-gray-700">{current.title}</span>
      </div>
      <div className="flex items-center gap-2">
        {prev ? (
          <Link
            href={sectionPath(prev)}
            className="rounded border border-gray-300 px-3 py-1.5 text-sm text-gray-700 hover:bg-gray-50 transition-colors"
          >
            ← {prev.title}
          </Link>
        ) : (
          <span />
        )}
        {next && (
          <Link
            href={sectionPath(next)}
            className="rounded bg-blue-600 px-3 py-1.5 text-sm text-white hover:bg-blue-700 transition-colors"
          >
            {next.title} →
          </Link>
        )}
      </div>
    </nav>
  );
}
