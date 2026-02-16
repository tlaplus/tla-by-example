import { introLessons } from "@/content/intro";
import { notFound } from "next/navigation";
import LessonPageClient from "./LessonPageClient";

interface PageProps {
  params: { slug: string };
}

export function generateStaticParams() {
  // tla-intuition has a dedicated route, exclude from dynamic params
  return introLessons
    .filter((l) => l.slug !== "tla-intuition")
    .map((l) => ({ slug: l.slug }));
}

export function generateMetadata({ params }: PageProps) {
  const lesson = introLessons.find((l) => l.slug === params.slug);
  if (!lesson) return {};
  return { title: `${lesson.title} - TLA+ By Example` };
}

export default function IntroLessonPage({ params }: PageProps) {
  const idx = introLessons.findIndex((l) => l.slug === params.slug);
  if (idx === -1) notFound();

  const lesson = introLessons[idx];
  const prev = idx > 0 ? introLessons[idx - 1] : undefined;
  const next = idx < introLessons.length - 1 ? introLessons[idx + 1] : undefined;

  return (
    <LessonPageClient
      lesson={lesson}
      prev={prev ? { slug: prev.slug, title: prev.title, section: prev.section } : undefined}
      next={next ? { slug: next.slug, title: next.title, section: next.section } : undefined}
    />
  );
}
