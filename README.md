# The Mechanics of Proof — Personal Working Copy

This repository is a fork of the Lean code for the book
[*The Mechanics of Proof*](https://hrmacbeth.github.io/math2001), by
[Heather Macbeth](https://faculty.fordham.edu/hmacbeth1), developed for the
course Math 2001 at Fordham University.

> **Attribution.** The textbook, the Lean code, and all exercises in this
> repository are the work of **Dr. Heather Macbeth**. This fork is simply my
> personal working copy, where I keep my own solutions as I work through the
> exercises to learn Lean. All credit for the underlying content belongs to
> Dr. Macbeth. Please refer to the
> [original repository](https://github.com/hrmacbeth/math2001) and the
> [book website](https://hrmacbeth.github.io/math2001) as the canonical sources.

The Lean files corresponding to each chapter of the book are in the folder
[`Math2001`](Math2001).

---

## About this fork

This is my personal working copy of Dr. Macbeth's materials. I am working
through the code and exercises from *The Mechanics of Proof* to learn Lean, and
I keep my own solutions here as I go. It contains no original content of my own beyond worked exercises.

---

## Getting started

There are two ways to work with these materials. A detailed, beginner-friendly
setup guide (for both faculty and students) is available separately; the short
version is below.

### Option 1 — In your browser (no installation)

The easiest way to get started, especially if you have never used Lean before,
is **GitHub Codespaces**, which runs a full editor in your browser with nothing
to install.

1. Sign in to (or create) a free [GitHub account](https://github.com/).
2. On this repository's page, click the green **Code** button.
3. Choose the **Codespaces** tab and click **Create codespace on main**.
4. Wait for the automatic setup (cloning, downloading, and compiling the Lean
   mathematics library) to finish before opening a file.

> **Note.** Earlier versions of these instructions used **Gitpod**. As of
> April 2025, Gitpod is deprecated for this purpose and **GitHub Codespaces**
> is the recommended cloud option. The legacy Gitpod link below is retained for
> reference but Codespaces is preferred.

For very quick, one-off experiments (without the course library), there is also
the zero-setup [online Lean editor](https://live.lean-lang.org/).

### Option 2 — On your own computer

1. Install Lean and VS Code by following the official, always-current
   instructions at [https://lean-lang.org/install](https://lean-lang.org/install).
   The recommended method installs Lean for you through a setup wizard inside
   VS Code.
2. Clone this repository:
   ```
   git clone https://github.com/<your-username>/math2001.git
   ```
3. Move into the folder and download the prebuilt mathematics library (this
   avoids a very long from-source compile):
   ```
   cd math2001
   lake exe cache get
   ```
4. Build the project:
   ```
   lake build
   ```
5. Open the `math2001` folder in VS Code, open a file in the `Math2001` folder,
   and wait for Lean to finish loading. Place your cursor inside a proof to see
   the goal state in the **Lean Infoview** panel.

> **Tip.** Do not skip `lake exe cache get`. Opening a file before running it
> can cause Lean to compile the entire mathematics library from source, which
> may take a very long time.

---

## Legacy Gitpod link (deprecated)

The original repository offered a one-click Gitpod workspace. This option is
**deprecated** (see the note above) and is preserved here only for reference:

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/hrmacbeth/math2001)

---

## Credit and license

All textbook content, Lean code, and exercises originate from
**Dr. Heather Macbeth**, *The Mechanics of Proof*
([book](https://hrmacbeth.github.io/math2001),
[original repository](https://github.com/hrmacbeth/math2001)).

This is a personal fork kept for my own learning. Any license terms in the
original repository continue to apply; please consult the upstream repository
for the authoritative license.
