"use client";

import LessonLayout from "@/components/LessonLayout";
import MarkdownContent from "@/components/MarkdownContent";
import type { Lesson, LessonNavInfo } from "@/lib/lessons";

interface Props {
  lesson: Lesson;
  prev?: LessonNavInfo;
  next?: LessonNavInfo;
}

export default function LessonPageClient({ lesson, prev, next }: Props) {
  return (
    <LessonLayout lesson={lesson} prev={prev} next={next}>
      <MarkdownContent content={lesson.description} />
    </LessonLayout>
  );
}
