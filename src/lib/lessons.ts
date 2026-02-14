export interface ExtraTab {
  label: string;
  content: string;
  language?: string;
}

export interface Lesson {
  slug: string;
  title: string;
  section: "intro" | "blocking-queue";
  description: string;
  spec: string;
  cfg: string;
  tabs?: ("spec" | "cfg")[];
  extraTabs?: ExtraTab[];
  commitSha?: string;
  commitUrl?: string;
}

export interface LessonNavInfo {
  slug: string;
  title: string;
  section: "intro" | "blocking-queue";
}
