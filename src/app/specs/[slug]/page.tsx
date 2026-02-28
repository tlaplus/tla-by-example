import { getBeginnerSpecs, getSpecBySlug } from "@/lib/specs";
import { notFound } from "next/navigation";
import SpecPageClient from "./SpecPageClient";

interface PageProps {
  params: { slug: string };
}

export function generateStaticParams() {
  return getBeginnerSpecs().map((s) => ({ slug: s.slug }));
}

export function generateMetadata({ params }: PageProps) {
  const spec = getSpecBySlug(params.slug);
  if (!spec) return {};
  return { title: `${spec.name} - TLA+ By Example` };
}

export default function SpecPage({ params }: PageProps) {
  const spec = getSpecBySlug(params.slug);
  if (!spec) notFound();

  return (
    <SpecPageClient
      name={spec.name}
      readme={spec.readme}
      modules={spec.modules}
    />
  );
}
