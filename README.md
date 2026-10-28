### Lean Workshop

Resources for Lean workshops held as part of the [Melbourne Lean Seminar](https://mcdoll.github.io/leanseminar.html).

#### Week 1 - Primes & Irrationality

The goal this week is to become acquainted with the basic tactics in Lean and formalize two familiar proofs: Euclid’s proof that there are infinitely many primes, and the proof that $\sqrt{2}$ is irrational.

Open [Week 1 exercises](Week1/Week1.lean) in VS Code. [Worksheet (PDF)](Week1/Workshop%20Sheet%20-%20Week%201.pdf).

#### Week 2 - Sets, Functions, and Relations

The goal this week is to gain familiarity with the basics of sets, functions and equivalence relations. We prove Cantor's theorem in Lean, and look at equivalence relations for sets, in preparation for groups next the following week. 

Open [Week 2 exercises](Week2/Week2.lean) in VS Code. [Worksheet (PDF)](Week2/Workshop%20Sheet%20-%20Week%202.pdf).

#### Week 3 - Groups, Homomorphisms, and the First Isomorphism Theorem

The goal this week is to gain familiarity with the basics of group theory in Lean. We prove the subgroup test, the first isomorphism theorem and use our equivalence relation from week 2 to prove an instance of the chinese remainder theorem (the general case is left as a challenge). 

Open [Week 3 exercises](Week3/Week3.lean) in VS Code. [Worksheet (PDF)](Week3/Workshop%20Sheet%20-%20Week%203.pdf).

#### Week 4 - Rings and Modules

The goal this week is to learn how to work with rings, ideals and modules in Lean. 

Open [Week 4 exercises](Week4/Week4.lean) in VS Code. [Worksheet (PDF)](Week4/Workshop%20Sheet%20-%20Week%204.pdf). Follow the setup steps below to download Mathlib.

#### Get started

1. Follow the [Lean installation guide](https://lean-lang.org/install/) to install VS Code, the official Lean 4 extension, and complete its setup.
2. Clone the repository by running:

   ```sh
   git clone https://github.com/AdamMonteleone/LeanWorkshop.git
   cd LeanWorkshop
   ```

3. In VS Code, choose **File → Open Folder** and open the cloned `LeanWorkshop` folder containing `lakefile.toml`.
4. Choose **Terminal → New Terminal** and run:

   ```sh
   lake exe cache get
   ```

   This downloads the precompiled mathematics library used by the exercises. The first setup can take several minutes, so doing it before the workshop helps.
5. Open the exercise file for your week (`Week1/Week1.lean`, `Week2/Week2.lean`, `Week3/Week3.lean` or `Week4/Week4.lean`) and start with Exercise 1. Place your cursor inside a proof to see the goal and hypotheses in Lean's Infoview. Warnings about `sorry` are expected until you complete the exercises.

Keep the whole project folder together: the Lean files need the included project configuration to find the correct library and Lean version.

#### Useful links

- [Loogle](https://loogle.lean-lang.org/) - search for library lemmas; use `#check` in Lean to inspect a result.
- [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4) - further practice with tactics and elementary proofs.
- [Lean installation help](https://lean-lang.org/install/).
- [Mathlib setup and cached builds](https://github.com/leanprover-community/mathlib4#downloading-cached-build-files).

#### Project version

This project uses Lean **4.33.1** and mathlib **v4.33.1**, pinned by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.
