"use client";

interface RunTlcButtonProps {
  isRunning: boolean;
  isReady: boolean;
  onClick: () => void;
}

export default function RunTlcButton({ isRunning, isReady, onClick }: RunTlcButtonProps) {
  return (
    <button
      onClick={onClick}
      disabled={isRunning || !isReady}
      className={`rounded px-4 py-1.5 text-sm font-semibold transition-colors ${
        isRunning || !isReady
          ? "bg-gray-200 text-gray-400 cursor-not-allowed"
          : "bg-green-600 text-white hover:bg-green-700"
      }`}
    >
      {isRunning ? "⏳ Running..." : isReady ? "▶ Run TLC" : "⏳ Loading..."}
    </button>
  );
}
