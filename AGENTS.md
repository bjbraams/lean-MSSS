# Project instructions — lean-MSSS

Before working, read and follow [the shared Lean instructions](../lean-codes/AGENTS.common.md),
then apply the project-specific rules below. Resolve that path relative to this file.
Local rules take precedence over the shared defaults. If the shared file is unavailable,
report that fact rather than proceeding without it.

## Build settings

- Lake root: the directory containing this `AGENTS.md`.
- Build output: `.lake/build-MSSS`; preserve the matching `buildDir` in `lakefile.toml`.
- Ordinary build command: `lake build > /tmp/MSSS-build.log 2>&1`.
- `.lake` points to the shared `/export/scratch1/braams/lean-codes-lake` on local disk.
  MSSS uses the shared `.lake/packages` checkouts.
  The pins in `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain`
  are authoritative.
- In this project the library search order is Mathlib → pinned TauCeti → local project code.

## Project

This project is in the area of Mathematical Statistics - Spatial Statistics (MSSS). The
project follows the style of the sibling ~/lean-CKSD project that is devoted to core knowledge
in statistics and data science and the sibling ~/lean-MSBT project that is devoted to bandit
theory.

One component of the lean-MSSS project is to assemble a bibliography. The main working file is
`MSSS-bib.md`. This file is meant for the human reader.

PDF files for some of the references are in the directory ../lean-MSSS/References/.

There may be additional files, for example `*.json`, for precise bibliographical data.

There will be a file `SYNOPSIS.md` that describes the core mathematical content of the
references in the area of spatial statistics. This file is meant for the human mathematician
reader; it does not reference any technical Lean concepts. Proofs are outside the scope of
the synopsis.

Coverage of the synopsis in Lean Mathlib and TauCeti will be documented in the file
`STRUCTURE.md` following the style of the various STRUCTURE files in the sibling ~/lean-CKSD
project. File `GAPS.md` restates the principal results that none of the libraries proves.

Following the bibliographical work and the development of the inventories the project continues
with the formalization of content of `GAPS.md`. The Lean codes for this formalization are
developed in the subdirectory MSSS. The Lean codes created there should all live in a MSSS
namespace. Within that namespace the naming should adhere to Mathlib standards. (I have in mind
that at some point this becomes a TauCeti project, and then the namespace MSSS will be replaced
by namespace TauCeti.) So one task is to go through all of `GAPS.md` and for the identified gaps,
create code according to Mathlib standards in the MSSS subdirectory. At first any such code may
only be admitted, but in time the `sorry`s should be removed.

You may be asked to edit, revise or expand any of the files in the project directory or to create
new files.
- Keep changes narrowly related to the request.
- Preserve unrelated user changes.
- Do not commit changes unless explicitly requested.

## File length

A Lean file of about 1000 lines is a candidate for splitting along a natural mathematical seam;
1500 lines is the hard limit, and a longer Lean file must be split.

## Documentation consistency

- Describe the present mathematical content and coverage. Do not include development histories,
  review rounds, or accounts of additions, removals, renumbering, or changes in inventory counts.
  Retain source provenance and the library revisions needed to interpret coverage claims.
- Treat each numbered SYNOPSIS statement as the mathematical source for its restatements in
  GAPS.md. Propagate corrections to hypotheses, conventions, and conclusions to every affected
  restatement and STRUCTURE assessment.
  A Scope or Argument paragraph must not silently add a missing hypothesis to a Statement
  paragraph.
- After changing statements or selections, recount synopsis entries, coverage classifications,
  selected gaps, easy entries, and Scope paragraphs. Update the indexes and library summaries,
  and check local Markdown links. New entries take the next free identifier.
