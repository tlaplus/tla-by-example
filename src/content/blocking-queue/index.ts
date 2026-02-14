import introduction from "./introduction";
import v02 from "./v02-state-graph";
import v03 from "./v03-larger-config";
import v04 from "./v04-debug-config";
import v05 from "./v05-safety";
import v06 from "./v06-variables";
import v07 from "./v07-symmetry";
import v08 from "./v08-inequation";
import v08a from "./v08a-view";
import v11 from "./v11-notify-nondeterministic";
import v12 from "./v12-notify-all";
import v13 from "./v13-two-mutexes";
import { Lesson } from "@/lib/lessons";

export const blockingQueueLessons: Lesson[] = [
  introduction,
  v02,
  v03,
  v04,
  v05,
  v06,
  v07,
  v08,
  v08a,
  v11,
  v12,
  v13,
];
