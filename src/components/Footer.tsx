export default function Footer() {
  return (
    <footer className="border-t border-gray-200 bg-gray-50 py-6 text-center text-sm text-gray-500">
      Made by{" "}
      <a
        href="https://fponzi.me"
        className="text-blue-600 hover:underline"
        target="_blank"
        rel="noopener noreferrer"
      >
        Federico Ponzi
      </a>
      {" — send questions and comments to "}
      <a
        href="mailto:me@fponzi.me"
        className="text-blue-600 hover:underline"
      >
        me@fponzi.me
      </a>
    </footer>
  );
}
