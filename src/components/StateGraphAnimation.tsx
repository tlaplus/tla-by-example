"use client";

// Pure visualization component — receives all state as props, renders SVG graph + BFS state

type State = [number, number]; // [big, small]

const stateKey = (s: State) => `${s[0]},${s[1]}`;

export interface GraphEdge {
  from: State;
  to: State;
}

export interface AnimationProps {
  discoveredStates: State[];
  edges: GraphEdge[];
  highlightState?: State | null;
  sourceState?: State | null; // node being expanded (green outline)
  ghostActions?: { action: string; state: State }[];
  violationStates?: State[];
  traceStates?: State[]; // counterexample trace path
  traceEdges?: GraphEdge[]; // counterexample trace edges
  visitedStates?: State[]; // already-expanded states
  queueStates?: State[]; // states still to expand
}

// All 24 possible grid positions (big 0..5 × small 0..3), not all are reachable
const ALL_GRID: State[] = [];
for (let b = 0; b <= 5; b++) {
  for (let s = 0; s <= 3; s++) {
    ALL_GRID.push([b, s]);
  }
}

const SVG_W = 520;
const SVG_H = 380;
const MARGIN_X = 55;
const MARGIN_Y = 50;
const CELL_W = (SVG_W - 2 * MARGIN_X) / 5;
const CELL_H = (SVG_H - 2 * MARGIN_Y) / 3;
const NODE_R = 18;

function statePos(s: State): { x: number; y: number } {
  return {
    x: MARGIN_X + s[0] * CELL_W,
    y: SVG_H - MARGIN_Y - s[1] * CELL_H,
  };
}

export default function StateGraphAnimation({
  discoveredStates,
  edges,
  highlightState,
  sourceState,
  ghostActions = [],
  violationStates = [],
  traceStates = [],
  traceEdges = [],
  visitedStates = [],
  queueStates = [],
}: AnimationProps) {
  const discoveredSet = new Set(discoveredStates.map(stateKey));
  const highlightKey = highlightState ? stateKey(highlightState) : null;
  const sourceKey = sourceState ? stateKey(sourceState) : null;
  const violationSet = new Set(violationStates.map(stateKey));
  const traceSet = new Set(traceStates.map(stateKey));
  const traceEdgeSet = new Set(
    traceEdges.map((e) => stateKey(e.from) + "->" + stateKey(e.to))
  );

  const showBfsState = visitedStates.length > 0 || queueStates.length > 0;

  return (
    <div className="flex flex-col h-full bg-gray-50">
      <div className="px-4 py-3 border-b border-gray-200 bg-white">
        <h3 className="text-sm font-semibold text-gray-700">
          DieHard State Graph
        </h3>
      </div>

      <div className="flex-1 flex items-center justify-center p-4 min-h-0">
        <svg
          viewBox={`0 0 ${SVG_W} ${SVG_H}`}
          className="w-full h-full max-h-[500px]"
        >
          <defs>
            <marker id="arrow" markerWidth="7" markerHeight="5" refX="7" refY="2.5" orient="auto">
              <path d="M0,0 L7,2.5 L0,5" fill="#94a3b8" />
            </marker>
            <marker id="arrow-trace" markerWidth="7" markerHeight="5" refX="7" refY="2.5" orient="auto">
              <path d="M0,0 L7,2.5 L0,5" fill="#ef4444" />
            </marker>
          </defs>

          {/* Axis labels */}
          <text x={SVG_W / 2} y={SVG_H - 8} textAnchor="middle" fontSize="11" fill="#94a3b8" fontFamily="monospace">
            big (0–5)
          </text>
          <text x={12} y={SVG_H / 2} textAnchor="middle" fontSize="11" fill="#94a3b8" fontFamily="monospace"
            transform={`rotate(-90, 12, ${SVG_H / 2})`}>
            small (0–3)
          </text>

          {/* Grid dots for all positions */}
          {ALL_GRID.map((s) => {
            const k = stateKey(s);
            if (discoveredSet.has(k)) return null;
            // Don't show dot if there's a ghost action for this position
            if (ghostActions.some((g) => stateKey(g.state) === k)) return null;
            const pos = statePos(s);
            return <circle key={`dot-${k}`} cx={pos.x} cy={pos.y} r={3} fill="#e2e8f0" />;
          })}

          {/* Ghost nodes for candidate actions */}
          {ghostActions.map((a) => {
            const k = stateKey(a.state);
            if (discoveredSet.has(k)) return null;
            const pos = statePos(a.state);
            return (
              <g key={`ghost-${k}`}>
                <circle cx={pos.x} cy={pos.y} r={NODE_R} fill="none" stroke="#93c5fd"
                  strokeWidth="1.5" strokeDasharray="4 3" opacity={0.7} />
                <text x={pos.x} y={pos.y - 2} textAnchor="middle" fontSize="8"
                  fill="#93c5fd" fontFamily="monospace">{a.state[0]},{a.state[1]}</text>
                <text x={pos.x} y={pos.y + 8} textAnchor="middle" fontSize="7"
                  fill="#93c5fd" fontFamily="monospace">{a.action}</text>
              </g>
            );
          })}

          {/* Edges */}
          {edges.map((edge, i) => {
            const fp = statePos(edge.from);
            const tp = statePos(edge.to);
            const dx = tp.x - fp.x;
            const dy = tp.y - fp.y;
            const dist = Math.sqrt(dx * dx + dy * dy);
            if (dist === 0) return null;
            const nx = dx / dist;
            const ny = dy / dist;
            const x1 = fp.x + nx * (NODE_R + 1);
            const y1 = fp.y + ny * (NODE_R + 1);
            const x2 = tp.x - nx * (NODE_R + 5);
            const y2 = tp.y - ny * (NODE_R + 5);
            const ek = stateKey(edge.from) + "->" + stateKey(edge.to);
            const isTrace = traceEdgeSet.has(ek);
            return (
              <line key={`e-${i}`} x1={x1} y1={y1} x2={x2} y2={y2}
                stroke={isTrace ? "#ef4444" : "#94a3b8"}
                strokeWidth={isTrace ? 2 : 1}
                markerEnd={isTrace ? "url(#arrow-trace)" : "url(#arrow)"}
                opacity={isTrace ? 0.9 : 0.4} />
            );
          })}

          {/* Discovered nodes */}
          {discoveredStates.map((s) => {
            const k = stateKey(s);
            const pos = statePos(s);
            const isHighlight = highlightKey === k;
            const isSource = sourceKey === k;
            const isViolation = violationSet.has(k);
            const isTrace = traceSet.has(k);
            return (
              <g key={`n-${k}`}>
                <circle cx={pos.x} cy={pos.y} r={NODE_R}
                  fill={
                    isHighlight ? "#3b82f6"
                    : isViolation ? "#fbbf24"
                    : isTrace ? "#fecaca"
                    : "#e2e8f0"
                  }
                  stroke={
                    isSource ? "#16a34a"
                    : isHighlight ? "#1d4ed8"
                    : isViolation ? "#d97706"
                    : isTrace ? "#ef4444"
                    : "#94a3b8"
                  }
                  strokeWidth={isSource ? 3 : isHighlight || isViolation ? 2.5 : 1.5}
                  className="transition-all duration-300"
                />
                <text x={pos.x} y={pos.y + 1} textAnchor="middle" dominantBaseline="central"
                  fontSize="9" fontWeight={isHighlight || isViolation ? "bold" : "normal"}
                  fontFamily="monospace" fill={isHighlight ? "white" : "#334155"}>
                  {s[0]},{s[1]}
                </text>
              </g>
            );
          })}
        </svg>
      </div>

      {/* BFS state: Visited and Queue */}
      {showBfsState && (
        <div className="px-4 py-3 border-t border-gray-200 bg-white text-xs space-y-1.5 overflow-y-auto max-h-[120px]">
          <div>
            <span className="font-semibold text-gray-500">Visited: </span>
            <span className="text-gray-600">
              {"{ "}
              {visitedStates.map((s, i) => (
                <span key={stateKey(s)}>
                  {i > 0 && ", "}
                  <span className="font-mono">({s[0]},{s[1]})</span>
                </span>
              ))}
              {" }"}
            </span>
          </div>
          <div>
            <span className="font-semibold text-gray-500">Queue: </span>
            <span className="text-gray-600">
              {"[ "}
              {queueStates.map((s, i) => (
                <span key={stateKey(s)}>
                  {i > 0 && ", "}
                  <span className={`font-mono ${i === 0 ? "text-green-600 font-semibold" : ""}`}>({s[0]},{s[1]})</span>
                </span>
              ))}
              {" ]"}
            </span>
          </div>
        </div>
      )}
    </div>
  );
}
