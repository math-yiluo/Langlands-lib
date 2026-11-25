/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.AlgebraicGeometry.Native.NativeBasicComparisons
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenProperInterchange

/-! # Native Weil calculation on a compatible proper/open tower

Source: Stacks Project, Tag 0F7J, `lemma-shriek-composition`, the first four
identifications in its proof; adapted to the native coefficient realization of
`def-sf-native-weil-derived-framework`.
(blueprint: lem-sf-native-weil-compatible-tower-calculation)

The compactification functors are expanded as termwise native open extension followed
by native total derived direct image. The three natural isomorphisms below give the
first intermediate identification, the proper/open identification, and their composite.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

/-- The compatible-tower calculation, on bounded constructible native Weil complexes.
The first conjunct says that `J_s` preserves the bounded constructible object property.
The remaining conjuncts are the two intermediate natural isomorphisms and the resulting
natural isomorphism from `F_(ts,qp)` to `F_(i,q) F_(s,pW)`. Their components and inverses
are morphisms in the native equivariant derived category.

Source: Stacks Project, Tag 0F7J, `lemma-shriek-composition`, first four displayed
identifications; native adaptation, not an application of the torsion coefficient result.
(blueprint: lem-sf-native-weil-compatible-tower-calculation)

Proof:
1. Compose the quasi-compact open immersions `s,t` and the proper maps `p,q`.
The permanence statements of `lem-weil-pbc-proper-fp-permanence` and the open and
finite-type definitions show that `(s ≫ t,p ≫ q)`, `(s,pW)`, and `(i,q)` are the
specified open/proper factorizations. The Cartesian square gives `t ≫ p = pW ≫ i`,
so their underlying composites agree. Absolute separatedness is not used.
2. Apply part (b) of `lem-sf-native-weil-basic-comparisons` to `s`. Thus `J_s K`
is bounded constructible for every bounded constructible `K` on `V`.
3. Part (a) of that lemma gives `R(qp)_* ≅ Rq_* Rp_*` on the entire native derived
category. Part (b) gives `J_t J_s ≅ J_(ts)`. Whisker the inverse of the latter by
the direct images and compose with the former to obtain the first displayed isomorphism.
These comparisons impose no boundedness requirement on an intermediate direct image.
4. Apply `lem-sf-native-weil-open-proper-interchange` with `j'=t`, `p'=pW`,
`j=i`, and vertical map `p`. Its comparison `J_i RpW_* ≅ Rp_* J_t` has source
`WC^der(U)`. Restrict it along `J_s`, using step 2, invert it, and whisker by
`Rq_*`. This is exactly the second intermediate natural isomorphism below.
5. Compose the natural isomorphisms of steps 3 and 4. Expanding the notation
`F_(j,r) = Rr_* J_j` identifies its endpoints with the claimed compactification
functors. Naturality follows by pasting the naturality squares of the comparisons;
the inverse reverses their order and uses their inverses. All comparisons, their
inverses, and their functorial images remain in the native derived categories.
-/
theorem nativeWeilCompatibleTowerCalculation
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {V U Vbar W Wbar T : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of k₀))] [U.Over (Spec (CommRingCat.of k₀))]
    [Vbar.Over (Spec (CommRingCat.of k₀))] [W.Over (Spec (CommRingCat.of k₀))]
    [Wbar.Over (Spec (CommRingCat.of k₀))] [T.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (V ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Vbar ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Vbar ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (W ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Wbar ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Wbar ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (T ↘ Spec (CommRingCat.of k₀))]
    (s : V ⟶ U) (t : U ⟶ Vbar) (i : W ⟶ Wbar)
    (p : Vbar ⟶ Wbar) (pW : U ⟶ W) (q : Wbar ⟶ T)
    [s.IsOver (Spec (CommRingCat.of k₀))] [t.IsOver (Spec (CommRingCat.of k₀))]
    [i.IsOver (Spec (CommRingCat.of k₀))] [p.IsOver (Spec (CommRingCat.of k₀))]
    [pW.IsOver (Spec (CommRingCat.of k₀))] [q.IsOver (Spec (CommRingCat.of k₀))]
    [IsOpenImmersion s] [QuasiCompact s] [IsOpenImmersion t] [QuasiCompact t]
    [IsOpenImmersion i] [QuasiCompact i] [IsProper p] [IsProper pW] [IsProper q]
    (hcart : IsPullback t pW p i) :
    (∀ (K : _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l V)),
      objectProperty k₀ l V K → objectProperty k₀ l U
        ((ProEtaleWeilSheaf.extensionByZero k₀ l s).mapDerivedCategory.obj K)) ∧
    Nonempty
      ((objectProperty k₀ l V).ι ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l (s ≫ t)).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l (p ≫ q)).rightDerivedFunctor ≅
        (objectProperty k₀ l V).ι ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l s).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l t).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l q).rightDerivedFunctor) ∧
    Nonempty
      ((objectProperty k₀ l V).ι ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l s).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l t).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l q).rightDerivedFunctor ≅
        (objectProperty k₀ l V).ι ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l s).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l pW).rightDerivedFunctor ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l i).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l q).rightDerivedFunctor) ∧
    Nonempty
      ((objectProperty k₀ l V).ι ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l (s ≫ t)).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l (p ≫ q)).rightDerivedFunctor ≅
        (objectProperty k₀ l V).ι ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l s).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l pW).rightDerivedFunctor ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l i).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l q).rightDerivedFunctor) := by
  obtain ⟨hcomp, _, hopen, hopenComp, _⟩ := nativeWeilBasicComparisons k₀ l
  have hs := (hopen V U s).2.2
  obtain ⟨α⟩ := hcomp Vbar Wbar T p q
  obtain ⟨β⟩ := hopenComp V U Vbar s t
  obtain ⟨γ⟩ := nonempty_extensionByZero_rightDerivedLowerStar_iso
    k₀ l t pW p i hcart.w
  let Js := (ProEtaleWeilSheaf.extensionByZero k₀ l s).mapDerivedCategory
  let Jz := (ProEtaleWeilSheaf.extensionByZero k₀ l (s ≫ t)).mapDerivedCategory
  let Rp := (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor
  let Rq := (ProEtaleWeilSheaf.lowerStar k₀ l q).rightDerivedFunctor
  let I := (objectProperty k₀ l V).ι
  let L := (objectProperty k₀ l U).lift (I ⋙ Js) (fun K ↦ hs K.obj K.property)
  let first := Functor.isoWhiskerLeft I
    (Functor.isoWhiskerLeft Jz α ≪≫ Functor.isoWhiskerRight β.symm (Rp ⋙ Rq))
  let second := Functor.isoWhiskerRight (Functor.isoWhiskerLeft L γ.symm) Rq
  exact ⟨hs, ⟨first⟩, ⟨second⟩, ⟨first ≪≫ second⟩⟩

end AlgebraicGeometry.WeilComplex
