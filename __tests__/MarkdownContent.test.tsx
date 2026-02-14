/**
 * @jest-environment jsdom
 */
import React from "react";
import { render, screen } from "@testing-library/react";
import "@testing-library/jest-dom";
import MarkdownContent from "@/components/MarkdownContent";

describe("MarkdownContent", () => {
  it("renders headings", () => {
    render(<MarkdownContent content="# Hello World" />);
    expect(screen.getByText("Hello World")).toBeInTheDocument();
  });

  it("renders bold text", () => {
    render(<MarkdownContent content="This is **bold** text" />);
    expect(screen.getByText("bold")).toBeInTheDocument();
  });

  it("renders links", () => {
    render(<MarkdownContent content="[Click here](https://example.com)" />);
    const link = screen.getByText("Click here");
    expect(link).toHaveAttribute("href", "https://example.com");
  });

  it("renders code blocks", () => {
    render(<MarkdownContent content="Use `inline code` here" />);
    expect(screen.getByText("inline code")).toBeInTheDocument();
  });
});
