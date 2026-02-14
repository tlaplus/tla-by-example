import type { Metadata } from "next";
import "./globals.css";

export const metadata: Metadata = {
  title: "TLA+ By Example",
  description: "Learn TLA+ specifications through interactive examples in your browser",
};

export default function RootLayout({
  children,
}: {
  children: React.ReactNode;
}) {
  return (
    <html lang="en">
      <body className="bg-white text-gray-900 antialiased">
        {children}
      </body>
    </html>
  );
}
