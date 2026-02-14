"use client";

import LessonLayout from "@/components/LessonLayout";
import MarkdownContent from "@/components/MarkdownContent";
import type { Lesson, LessonNavInfo } from "@/lib/lessons";

interface Props {
  lesson: Lesson;
  prev?: LessonNavInfo;
  next?: LessonNavInfo;
}

export default function BQPageClient({ lesson, prev, next }: Props) {
  return (
    <LessonLayout lesson={lesson} prev={prev} next={next}>
      <MarkdownContent content={lesson.description} />
      <div className="mt-6 rounded-lg border border-blue-100 bg-blue-50 px-4 py-3 text-sm text-blue-800">
        <strong>Credit:</strong> This tutorial is based on the{" "}
        <a
          href="https://github.com/lemmy/BlockingQueue"
          className="text-blue-600 hover:underline font-medium"
          target="_blank"
          rel="noopener noreferrer"
        >
          BlockingQueue
        </a>{" "}
        repository by{" "}
        <a
          href="https://github.com/lemmy"
          className="text-blue-600 hover:underline font-medium"
          target="_blank"
          rel="noopener noreferrer"
        >
          Markus Kuppe
        </a>
        , licensed under MIT.
      </div>
    </LessonLayout>
  );
}
