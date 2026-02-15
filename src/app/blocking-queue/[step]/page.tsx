import { blockingQueueLessons } from "@/content/blocking-queue";
import { notFound } from "next/navigation";
import BQPageClient from "./BQPageClient";

interface PageProps {
  params: { step: string };
}

export function generateStaticParams() {
  return blockingQueueLessons.map((l) => ({ step: l.slug }));
}

export function generateMetadata({ params }: PageProps) {
  const lesson = blockingQueueLessons.find((l) => l.slug === params.step);
  if (!lesson) return {};
  return { title: `${lesson.title} - TLA+ By Example` };
}

export default function BlockingQueuePage({ params }: PageProps) {
  const idx = blockingQueueLessons.findIndex((l) => l.slug === params.step);
  if (idx === -1) notFound();

  const lesson = blockingQueueLessons[idx];
  const prev = idx > 0 ? blockingQueueLessons[idx - 1] : undefined;
  const next = idx < blockingQueueLessons.length - 1 ? blockingQueueLessons[idx + 1] : undefined;

  return (
    <BQPageClient
      lesson={lesson}
      prev={prev ? { slug: prev.slug, title: prev.title, section: prev.section } : undefined}
      next={next ? { slug: next.slug, title: next.title, section: next.section } : undefined}
    />
  );
}
