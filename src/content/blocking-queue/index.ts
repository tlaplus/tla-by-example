import introduction from "./introduction";
import stateGraph from "./state-graph";
import largerConfig from "./larger-config";
import debugConfig from "./debug-config";
import safety from "./safety";
import variables from "./variables";
import symmetry from "./symmetry";
import inequation from "./inequation";
import viewAbstraction from "./view";
import notifyNondeterministic from "./notify-nondeterministic";
import notifyAll from "./notify-all";
import twoMutexes from "./two-mutexes";
import { Lesson } from "@/lib/lessons";

export const blockingQueueLessons: Lesson[] = [
  introduction,
  stateGraph,
  largerConfig,
  debugConfig,
  safety,
  variables,
  symmetry,
  inequation,
  viewAbstraction,
  notifyNondeterministic,
  notifyAll,
  twoMutexes,
];
