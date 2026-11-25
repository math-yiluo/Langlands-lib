/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import WeilConjectures.RingTheory.WellOrderedPresentationKernelProjectionData

public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.Order.RelClasses
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The kernel filtration of a well-ordered projective presentation

Source: Stacks Project, Algebra, Lemma 0D1U, successor argument, with the
projective presentations supplied by the quotient resolutions in place of free modules.
(blueprint: lem-weil-pbc-well-ordered-presentation-kernel-filtration).
-/

@[expose] public section

universe u v w

namespace ModuleCat

open CategoryTheory CategoryTheory.Limits

/-- The degree-zero presentations of the successive quotients give a projective
presentation of the union with a compatible exhaustive kernel filtration.
No dimension bound or induction hypothesis is used here.
Source: Stacks Project, Algebra, Lemma 0D1U, successor argument.
(blueprint: lem-weil-pbc-well-ordered-presentation-kernel-filtration).

Proof: put `U e = sup_{i<e} F i` and `Q e = F e / U e`. At a stage with nonzero
`Q e`, use the given augmentation `P e` in degree zero and lift it to `F e`
through its quotient epimorphism by categorical projectivity. At a zero quotient
use a zero summand instead. Sum these lifts followed by the inclusions into `M`.
Transfinite induction shows that the sum through `e` maps onto `F e`: subtract
a lift of the quotient class and apply induction to the difference in `U e`.
The predecessor family is directed when nonempty, so its supremum is its union;
at a least index the predecessor supremum is zero. Exhaustion gives surjectivity.

The nonzero quotients form a small index set in universe `v`: choose for each
such index an element of `F e` outside `U e`. Distinct chosen elements cannot
coincide, since the one at a smaller index belongs to the larger predecessor
supremum. This injects the active indices into `M`. Shrink this set to universe
`v`, form the direct sum of its degree-zero projectives there, and denote it by
`B`. For a map from `B` through any epimorphism lift on each summand and sum the
lifts. Thus `B` is categorically projective without assuming the ring is small.

Take the kernel `K` of the resulting surjection `B → M`, and let `G e` be the
intersection of `K` with the partial sum through index `e`. The inclusions make
`G` monotone. Every vector has finite support, hence is contained in some partial
sum; the covering assumption gives a nonempty index set also for the zero vector.
The sum strictly before `e` is the union of the earlier partial sums and maps
onto `U e`. Projection onto the `e` summand consequently maps `G e` onto the
kernel of the given augmentation: for a vector in that augmentation kernel,
its lifted image lies in `U e`; choose a preimage in the preceding sum and
subtract it. The kernel of this projection is precisely the union of the
preceding `G i`, by intersection with the predecessor partial sum and finite
support. The first isomorphism theorem identifies the successive kernel quotient
with the augmentation kernel. At an inactive index the partial sum does not
change, so the successive kernel quotient is zero. Package `K → B → M` as a
short exact complex with third object exactly `M`.

Edge cases: repeated stages contribute zero kernel quotients; at a least stage
all predecessor submodules are zero; for a single stage this is the usual
augmentation presentation. An empty index type is excluded by covering zero.
The resolution family is input to this proposition, never chosen as library data. -/
theorem exists_projective_presentation_kernel_filtration
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    {E : Type w} [LinearOrder E] [IsWellOrder E (· < ·)]
    (F : E → Submodule R M) (hF : Monotone F)
    (hcover : ∀ x : M, ∃ e : E, x ∈ F e)
    (P : ∀ e : E, ProjectiveResolution
      (ModuleCat.of R ((F e) ⧸
        ((⨆ i : {j : E // j < e}, F i.val).comap (F e).subtype)))) :
    ∃ S : ShortComplex (ModuleCat.{v} R), S.X₃ = M ∧ S.ShortExact ∧
      Projective S.X₂ ∧ ∃ G : E → Submodule R S.X₁,
        Monotone G ∧ (∀ x : S.X₁, ∃ e : E, x ∈ G e) ∧
        ∀ e : E,
          IsZero (ModuleCat.of R ((G e) ⧸
            ((⨆ i : {j : E // j < e}, G i.val).comap (G e).subtype))) ∨
          Nonempty (ModuleCat.of R ((G e) ⧸
            ((⨆ i : {j : E // j < e}, G i.val).comap (G e).subtype)) ≅
              kernel ((P e).π.f 0)) := by
  obtain ⟨S, hM, hS, hproj, H, hH, hHcover, hpieces⟩ :=
    exists_projective_presentation_kernel_projection_data M F hF hcover P
  let G : E → Submodule R S.X₁ := fun e ↦ (H e).comap S.f.hom
  refine ⟨S, hM, hS, hproj, G, ?_, ?_, ?_⟩
  · intro i j hij
    exact Submodule.comap_mono (hH hij)
  · intro x
    obtain ⟨e, he⟩ := hHcover (S.f.hom x)
    exact ⟨e, he⟩
  · intro e
    rcases hpieces e with hzero | ⟨q, hq, hker⟩
    · left
      change (⨆ i : {j : E // j < e}, G i.val).comap (G e).subtype = ⊤ at hzero
      rw [hzero]
      exact ModuleCat.isZero_of_subsingleton _
    · right
      exact ⟨((Submodule.quotEquivOfEq _ _ hker.symm).trans
        (q.quotKerEquivOfSurjective hq)).toModuleIso⟩

end ModuleCat
