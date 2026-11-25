/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import WeilConjectures.RingTheory.FormallySmoothAdic
import WeilConjectures.RingTheory.FormallySmoothAdicCompletion
import Mathlib.RingTheory.Smooth.Basic

/-!
# Adic formal smoothness of a completed polynomial local ring

Source: Stacks Project, More on Algebra, proof of Lemma 15.51.9 (Tag 07PU),
via Lemmas 15.38.2 (Tag 07EC) and 15.38.4 (Tag 07ED)
(blueprint: lem-weil-pbc-polynomial-local-completion-formally-smooth).
-/

@[expose] public section

universe u

namespace Algebra

/-- If `A` is Noetherian and `q` is a prime of `A[X]`, the completion of `A[X]` localized
at `q` is formally smooth over `A` for the topology defined by the extension of `q`.
The algebra structures are the canonical ones through the polynomial ring, localization,
and completion. Source: Stacks Project, proof of Tag 07PU, using Tags 07EC(1) and 07ED.
(blueprint: lem-weil-pbc-polynomial-local-completion-formally-smooth)

Proof:
1. The polynomial algebra `A[X]` is smooth, hence has square-zero lifting
   (`lem-weil-pbc-polynomial-ring-smooth`,
   `lem-weil-pbc-smooth-ring-map-square-zero-lifting`; Tag 00TK).
2. Given a lifting problem for `T = A[X]_q`, first restrict to `A[X]` and lift there.
   Localization lifts across square-zero ideals, extending that lift to `T`
   (`lem-weil-pbc-localization-square-zero-lifting`,
   `def-weil-pbc-algebra-hom-quotient`; Tags 04EG and 031H).
3. Discrete formal smoothness implies formal smoothness for the `qT`-adic topology:
   it supplies a lift even without requiring the initial map to kill a power of `qT`
   (`theorem-finite-etale-covers-proper-henselian--2`; Tag 07EC(1)).
4. The polynomial ring over the Noetherian ring `A` is Noetherian, so `q` is
   finitely generated (`lem-weil-pbc-finite-type-algebra-noetherian`,
   `def-weil-pbc-noetherian-ring`). By `Ideal.FG.map`, its extension `qT` is
   finitely generated as well; Noetherianity of the localization is not needed.
5. Apply `lem-weil-pbc-fs-adic-completion` (Tag 07ED(1) implies (2)) to obtain formal
   smoothness of the completion for the extended ideal `(qT)C`. This equals `qC`:
   elements of `qT` are fractions with numerator in `q` and denominator outside `q`,
   and the inverses of those denominators also map into `C`
   (`def-weil-pbc-adic-completion`, `def-weil-pbc-localization-at-prime`).
-/
theorem polynomial_local_completion_formallySmoothAdic
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (q : Ideal (Polynomial A)) [q.IsPrime] :
    FormallySmoothAdic A
      (AdicCompletion (q.map (algebraMap (Polynomial A) (Localization.AtPrime q)))
        (Localization.AtPrime q))
      (q.map (algebraMap (Polynomial A)
        (AdicCompletion (q.map (algebraMap (Polynomial A) (Localization.AtPrime q)))
          (Localization.AtPrime q)))) := by
  let T := Localization.AtPrime q
  let n : Ideal T := q.map (algebraMap (Polynomial A) T)
  have hT : FormallySmoothAdic A T n := by
    intro D _ _ J hJ g _
    exact FormallySmooth.comp_surjective A T J hJ g
  have hn : n.FG := q.fg_of_isNoetherianRing.map _
  have hC := FormallySmoothAdic.adicCompletion A T n hn hT
  simpa only [n, Ideal.map_map, ← IsScalarTower.algebraMap_eq] using hC

end Algebra
