export default function Footer() {
  return (
    <footer className="border-t border-gray-200 bg-gray-50 py-6 text-center text-sm text-gray-500">
      {"Questions? Comments? "}
      <a
        href="https://github.com/tlaplus/tla-by-example/issues/new"
        className="text-blue-600 hover:underline"
        target="_blank"
        rel="noopener noreferrer"
      >
        Open an issue on GitHub
      </a>
    </footer>
  );
}
