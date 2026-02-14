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
      <hr className="my-6 border-gray-200" />
      <div className="text-xs text-gray-500">
        Based on the{" "}
        <a
          href="https://github.com/lemmy/BlockingQueue"
          className="text-blue-600 hover:underline"
          target="_blank"
          rel="noopener noreferrer"
        >
          BlockingQueue
        </a>{" "}
        repository by{" "}
        <a
          href="https://github.com/lemmy"
          className="text-blue-600 hover:underline"
          target="_blank"
          rel="noopener noreferrer"
        >
          Markus Kuppe
        </a>
        , licensed under MIT.
        {lesson.commitUrl && (
          <>
            {" · "}
            <a
              href={lesson.commitUrl}
              className="text-blue-600 hover:underline"
              target="_blank"
              rel="noopener noreferrer"
            >
              View commit on GitHub
            </a>
          </>
        )}
      </div>
    </LessonLayout>
  );
}
