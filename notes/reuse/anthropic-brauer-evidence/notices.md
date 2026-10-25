# Anthropic Brauer audit source notices

Supporting source provenance for [the audit](../anthropic-brauer-audit.md). Source registration: `anthropic-flt-complete-lean-source-6e837e75`; repository commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Copyright 2026 Anthropic, PBC; Apache-2.0. Worker 18 authored the private compatibility changes and the independent bridge experiments.

All eight exact paths and filenames in the closure were checked against upstream `ATTRIBUTION.md`; none has a matching per-file row. No individual author header occurs in those original eight files. This records the supplied provenance, not a claim that all underlying ideas originated with Anthropic. Upstream NOTICE explicitly says shorter Mathlib restatements were not traced individually. The original global notices are reproduced in full below. No applicable source-specific errata file was present at the checked public/library paths on 2026-10-25.

| Original notice file | SHA256 |
| --- | --- |
| `LICENSE` | `746bc52848eabf8765635fe532e0680756a10b18e7b3fb26e7433ab4edf34034` |
| `NOTICE` | `42b1821f19a6aaa25e6811d22ab8f2fdc6433d4a37bc810b1cfafa5b6dd6b0b6` |
| `ATTRIBUTION.md` | `698fb76c8d80b2ed78ebd48b271f2ee5815b3654fb8ec5c699b21b16ce0d9698` |

## Original LICENSE

```text

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright 2026 Anthropic, PBC

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
```

## Original NOTICE

```text
Fermat's Last Theorem in Lean 4
Copyright 2026 Anthropic, PBC

This repository is made available under the Apache License, Version 2.0 (see the file LICENSE).

Portions of this repository are derived from the third-party works listed in items 1-3 below, each licensed under
the Apache License, Version 2.0; item 4 lists the libraries bundled with the web pages, under their own licences.
The file ATTRIBUTION.md lists, file by file, the files of this repository that contain such material (106 files
with material from items 1 and 2, 54 under Definitions/ and 52 under P2M/Sol/; and, in its §4, the 23 files that
reproduce Mathlib text, item 3), with the upstream file each portion comes from and that file's copyright holder
and authors. The Lean files are published byte-for-byte as they were checked and carry no attribution headers,
apart from five files that retained an FLT-project notice in place (marked in ATTRIBUTION.md) and the Mathlib
provenance header of Definitions/Def_Compat_Mathlib430.lean; for all the others ATTRIBUTION.md is where the
per-file notices are reproduced. The notices below cover the works as a whole.

1. The FLT project — the Lean formalisation of Fermat's Last Theorem led by Kevin Buzzard at
   Imperial College London. https://github.com/ImperialCollegeLondon/FLT
   Material was taken from the project's `main` branch as of 2026-05-21, two files from commit
   8387d589441c1097d606ea89370c4165147255d5 (2026-05-27) and one from commit
   7a87d3b25db19d008cd45b29edd2b92803e785b1, as recorded per file in ATTRIBUTION.md.
   Copyright (c) 2024-2026 Kevin Buzzard, Andrew Yang, Matthew Jasper, Salvatore Mercuri, Javier López-Contreras,
   Madison Crim, Yaël Dillies, David Ledvinka, Ruben Van de Velde and the other authors named in the per-file
   notices (Anatole Dedecker, Bhavik Mehta, Bryan Wang Peng Jun, David Renshaw, James Sundstrom, Michael Rothgang,
   Pietro Monticone, William Coram), and the FLT project contributors.
   Released under the Apache License, Version 2.0 ("Released under Apache 2.0 license as described in the file
   LICENSE" in the per-file notices; that project's LICENSE file is the Apache License, Version 2.0, the same licence as in this
   repository's LICENSE file).
   104 files of this repository contain such material: definition modules under Definitions/ (in particular
   Def_Mathlib_*.lean — the project's "FLT/Mathlib" files —, Def_DedekindDomain_*, Def_Deformations_*, Def_HaarMeasure_*,
   Def_NumberField_*, Def_FLTPrelim_FreyPackage/GaloisRep, Def_AbstractHeckeOperator, Def_Patching_SystemTypes,
   Def_Representation_AbsolutelyIrreducible and others) and proof modules under P2M/Sol/ that inline upstream lemmas
   (patching, depth, adic valuations and finite adeles, restricted products, Haar characters, Frobenius elements,
   the Frey curve); ATTRIBUTION.md §§1-2 is the complete list.

2. flt-regular — the Lean formalisation of Fermat's Last Theorem for regular primes (Kummer's theorem).
   https://github.com/leanprover-community/flt-regular
   A. J. Best, C. Birkbeck, R. Brasca, E. Rodriguez Boidi, R. Van de Velde, A. Yang, "A complete formalization of
   Fermat's Last Theorem for regular primes in Lean", arXiv:2410.01466.
   Copyright (c) the flt-regular authors, as recorded in that repository.
   Released under the Apache License, Version 2.0.
   P2M/Sol/S_flt_regular.lean is a port, with proofs, of that project's FltRegular/NumberTheory/* (regular primes,
   cyclotomic units, Hilbert 90/92/94, Kummer's lemma), FltRegular/MayAssume/*, FltRegular/CaseI/* and FltRegular/CaseII/*
   files, ending in the theorem that Fermat's Last Theorem holds for odd regular prime exponents; it is used here for
   the exponents 7, 11 and 13. P2M/Sol/S_IsCyclotomicExtension_Rat_seven_pid.lean adapts FltRegular/SmallNumbers/*.
   That project's per-file headers are not reproduced in this revision; this notice and ATTRIBUTION.md §3 stand in
   their place.

3. Mathlib — https://github.com/leanprover-community/mathlib4
   Copyright (c) the respective Mathlib authors, as recorded in the headers of the Mathlib source files.
   Released under the Apache License, Version 2.0.
   This repository is built against a pinned Mathlib revision (see lake-manifest.json); some files adapt or restate
   Mathlib material. One file copies Mathlib text wholesale: Definitions/Def_Compat_Mathlib430.lean reproduces,
   under new names and without their docstrings, the Mathlib v4.30.0 (commit
   c5ea00351c28e24afc9f0f84379aa41082b1188f) text of a few definitions, lemmas and one notation whose form changed
   in Mathlib v4.33.0 — verbatim apart from four lines marked `-- [port]` — each copied block headed by the Mathlib
   file and line range it is taken from, together with two small bridging declarations of our own
   (Representation.ofMulActionFinsuppEquiv, Rep.ofMulActionFinsuppIso), three one-line `example` checks and, in its
   last block, four lemmas adapted and re-proved from Mathlib/NumberTheory/RamificationInertia/Galois.lean rather
   than copied. In addition, twenty-two other modules (twenty-one under P2M/Sol/, one under Definitions/) inline or
   adapt an individual proof or auxiliary construction from one of thirteen further Mathlib files — for example the
   exactness construction of Mathlib/RingTheory/AdicCompletion/Exactness.lean and the proof of `integral_comp_abs`
   from Mathlib/MeasureTheory/Measure/Lebesgue/Integral.lean — typically a private Mathlib lemma re-proved in
   place. ATTRIBUTION.md §4 lists the modules so identified, each with the Mathlib file drawn on and that file's
   copyright and author lines, twenty-one Mathlib files in all. Shorter restatements of Mathlib lemmas elsewhere in
   the tree have not been traced individually; this notice covers Mathlib as a whole.

4. Libraries bundled with the web pages, in html/assets/vendor/ (used only by the html/ documentation, not by the Lean
   build), each distributed under its own licence; html/assets/vendor/LICENSES.txt lists them:
   - KaTeX 0.18.4 (katex/katex.min.js, and katex/katex-embedded.css with the KaTeX fonts inlined).
     Copyright (c) 2013-2020 Khan Academy and other contributors. MIT License, reproduced in
     html/assets/vendor/katex/LICENSE. The bundled KaTeX fonts are Copyright (c) 2009-2010 Design Science, Inc. and
     Copyright (c) 2014-2018 Khan Academy, under the SIL Open Font License 1.1, whose text and the fonts' notice are
     reproduced in html/assets/vendor/katex/FONTS-LICENSE.txt.
   - @hpcc-js/wasm 2.35.0 (graphviz.umd.js: Graphviz compiled to WebAssembly). Apache License, Version 2.0, reproduced
     in html/assets/vendor/graphviz.LICENSE.txt. It includes Graphviz as compiled code, licensed under the Eclipse
     Public License 1.0 / Common Public License; the Graphviz source code is published at
     https://gitlab.com/graphviz/graphviz (Eclipse Public License 1.0).

The Lean 4 toolchain (https://github.com/leanprover/lean4) and the other Lake packages listed in lake-manifest.json
are dependencies fetched at build time and are not distributed in this repository.
```
