export interface Lesson {
  slug: string;
  title: string;
  section: "intro" | "blocking-queue";
  description: string;
  spec: string;
  cfg: string;
  tabs?: ("spec" | "cfg")[];
}

export interface LessonNavInfo {
  slug: string;
  title: string;
  section: "intro" | "blocking-queue";
}
