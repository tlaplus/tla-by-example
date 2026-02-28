export interface TlcOptions {
  workers: number;
  checkDeadlock: boolean;
}

let iframe: HTMLIFrameElement | null = null;
let iframeReady = false;
let readyResolve: (() => void) | null = null;
let readyReject: ((err: Error) => void) | null = null;
let resultResolve: ((output: string) => void) | null = null;
let resultReject: ((err: Error) => void) | null = null;
let progressCallback: ((line: string) => void) | null = null;

function getWorkerUrl(): string {
  const basePath = process.env.NEXT_PUBLIC_BASE_PATH || "";
  return `${basePath}/tlc-worker.html`;
}

function handleMessage(event: MessageEvent) {
  const data = event.data;
  if (!data || !data.type) return;

  if (data.type === "ready") {
    iframeReady = true;
    readyResolve?.();
    readyResolve = null;
    readyReject = null;
  } else if (data.type === "error" && readyResolve) {
    readyReject?.(new Error(data.message));
    readyResolve = null;
    readyReject = null;
  } else if (data.type === "result") {
    progressCallback = null;
    resultResolve?.(data.output);
    resultResolve = null;
    resultReject = null;
  } else if (data.type === "progress") {
    progressCallback?.(data.line);
  }
}

function createIframe(): Promise<void> {
  return new Promise((resolve, reject) => {
    readyResolve = resolve;
    readyReject = reject;
    iframeReady = false;

    if (iframe) {
      iframe.remove();
    }

    iframe = document.createElement("iframe");
    iframe.src = getWorkerUrl();
    iframe.style.display = "none";
    document.body.appendChild(iframe);

    // Timeout after 120 seconds
    setTimeout(() => {
      if (!iframeReady) {
        readyReject?.(new Error("CheerpJ initialization timed out"));
        readyResolve = null;
        readyReject = null;
      }
    }, 120000);
  });
}

let initPromise: Promise<void> | null = null;

export function initCheerpJ(): Promise<void> {
  if (typeof window === "undefined") {
    return Promise.resolve();
  }
  if (!initPromise) {
    window.addEventListener("message", handleMessage);
    initPromise = createIframe();
  }
  return initPromise;
}

export interface ExtraModule {
  name: string;
  content: string;
}

export async function runTlc(
  spec: string,
  cfg: string,
  options: TlcOptions,
  onProgress?: (line: string) => void,
  extraModules?: ExtraModule[],
): Promise<string> {
  if (!iframeReady || !iframe?.contentWindow) {
    throw new Error("CheerpJ not initialized. Call initCheerpJ() first.");
  }

  progressCallback = onProgress || null;

  const output = await new Promise<string>((resolve, reject) => {
    resultResolve = resolve;
    resultReject = reject;
    iframe!.contentWindow!.postMessage({
      type: "run",
      spec,
      cfg,
      workers: options.workers,
      checkDeadlock: options.checkDeadlock,
      extraModules: extraModules || [],
    }, "*");
  });

  // After run completes, reload iframe to reset all Java static state.
  // This creates a fresh CheerpJ/JVM for the next run.
  initPromise = createIframe();

  return output;
}

export function isCheerpJReady(): boolean {
  return iframeReady;
}
