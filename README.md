# Lean Workshop

## Week 1 — Primes & Irrationality

Start with a few tactic exercises, then formalize proofs that there are infinitely many primes and that the square root of two is irrational.

- [Week1.lean](Week1.lean) — the exercise file. Replace each `sorry` with your proof.
- [Week1Solutions.lean](Week1Solutions.lean) — complete solutions with matching exercise labels.
- [Workshop Sheet - Week 1.pdf](Workshop%20Sheet%20-%20Week%201.pdf) — the one-page workshop sheet.

## Get started

1. Follow the [Lean installation guide](https://lean-lang.org/install/) to install VS Code, the official Lean 4 extension, and complete its setup.
2. **[Download the project as a ZIP](https://github.com/AdamMonteleone/LeanWorkshop/archive/refs/heads/main.zip)** and extract it. You can also use the green **Code → Download ZIP** button above.
3. In VS Code, choose **File → Open Folder** and open the extracted project folder containing `lakefile.toml`.
4. Choose **Terminal → New Terminal** and run:

   ```sh
   lake exe cache get
   ```

   This downloads the precompiled mathematics library used by the exercises. The first setup can take several minutes, so doing it before the workshop helps.
5. Open `Week1.lean` and start with Exercise 1. Place your cursor inside a proof to see the goal and hypotheses in Lean's Infoview. Warnings about `sorry` are expected until you complete the exercises.

Keep the whole project folder together: the Lean files need the included project configuration to find the correct library and Lean version.

### Prefer Git?

Clone the project, then follow steps 3–5 above:

```sh
git clone https://github.com/AdamMonteleone/LeanWorkshop.git
```

## Useful links

- [Loogle](https://loogle.lean-lang.org/) — search for library lemmas; use `#check` in Lean to inspect a result.
- [Lean installation help](https://lean-lang.org/install/).
- [Mathlib setup and cached builds](https://github.com/leanprover-community/mathlib4#downloading-cached-build-files).

## Project version

This project uses Lean **4.32.1** and mathlib **v4.32.1**, pinned by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

To check the files from a terminal in the project folder:

```sh
lake env lean Week1.lean
lake env lean Week1Solutions.lean
```

The exercise file contains intentional unfinished proofs; the solutions file is complete.
