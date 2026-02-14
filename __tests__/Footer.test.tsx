/**
 * @jest-environment jsdom
 */
import React from "react";
import { render, screen } from "@testing-library/react";
import "@testing-library/jest-dom";
import Footer from "@/components/Footer";

describe("Footer", () => {
  it("renders Federico Ponzi credit", () => {
    render(<Footer />);
    expect(screen.getByText("Federico Ponzi")).toBeInTheDocument();
  });

  it("has a mailto link to me@fponzi.me", () => {
    render(<Footer />);
    const link = screen.getByText("me@fponzi.me");
    expect(link).toHaveAttribute("href", "mailto:me@fponzi.me");
  });
});
