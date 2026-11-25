/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionUnitCriterion
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionUnitRestriction
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionUnitTree

/-! # Canonical completion units and finite open--closed locality on qcqs schemes

Source: Stacks Project, Tags 099M, 09BL and 09BM; Bhatt--Scholze Lemma 6.5.8
and Remark 6.5.10 (blueprint: lem-fix-qcqs-completion-unit-locality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOnSlice

set_option linter.unusedVariables false in
/-- Canonical-unit completeness, ordinary restriction, and finite open--closed detection.

Source: Stacks Project, proetale.tex, Tags 099M, 09BL and 09BM; Bhatt--Scholze,
Lemma 6.5.8 and Remark 6.5.10 (blueprint: lem-fix-qcqs-completion-unit-locality).

Proof plan:
1. Apply lem-sf-open-quotient-koszul-completeness to the valuation ring, which is
   Noetherian with perfect finite quotients. Its quotient augmentation is precisely
   completionUnit: both come from the strict quotient maps with zero second coordinate.
   prop-weil-pbc-koszul-reconstruction identifies its specified comparison with the
   Koszul completion unit. Thus the Roos triangle condition is equivalent to invertibility
   of this specific unit, rather than of an arbitrary triangulated lift.
2. For a closed immersion, lem-weil-pbc-proetale-immersion-limit-preservation gives
   exact inverse image and all-limit preservation. For a weakly etale object use
   lem-weil-proetale-weakly-etale-localization, exact slice module restriction from
   lem-pur-site-restriction-module-adjunction-exact, and restriction-preserves-limits.
   Module limits are sectionwise. prop-weil-pbc-proetale-constant-ring-map identifies
   every finite coefficient ring by its constant sections. These maps commute with
   quotient transitions by sheafification. Their limit is the specified coefficient
   map, whose finite projections determine it uniquely. It is a ring isomorphism.
   Hence ordinary pullback is exact and preserves countable products.
3. Apply lem-weil-pbc-reduction-pullback-derived-tower. It identifies the strict
   reduction towers, including restriction of scalars, all transitions and augmentation
   maps. Its evaluations are the finite derived tensor comparisons.
4. Countable products are exact by lem-weil-proetale-countable-products-exact.
   Apply lem-cbc-exact-product-functor-strict-limit to the product-preserving exact
   restriction and compose with the strict-tower comparison of step 3. This is a natural
   comparison of the completions carrying the pulled-back canonical unit to the unit.
   Both product coordinates use the product comparison, so (c,0) maps to (Fc,0).
   Step 1 now proves preservation of completeness under ordinary restriction.
5. At an internal vertex use lem-weil-pbc-proetale-ringed-open-closed with the
   arbitrary completed ring sheaf. Its exact open--closed sequence and adjunctions
   satisfy lem-sfb-exact-open-closed-unbounded-calculus. Therefore the two child
   restrictions jointly reflect derived isomorphisms, without separatedness.
6. On a nonempty leaf exact restriction commutes with every cohomology sheaf by
   lem-weil-pbc-exact-functor-complex-cohomology. Use the unbounded cohomology
   isomorphism criterion and lem-sfb-sheaf-cover-local-isomorphism. Base changes of
   the chosen pro-etale cover cover every test object. An inverse to an underlying
   abelian-sheaf module map is linear, so this detects module isomorphisms too.
7. Induct up the finite tree. Use step 6 at nonempty leaves and step 5 at vertices.
   On an empty leaf every module sheaf is zero since the empty family covers the
   terminal object. Step 4 identifies all branch units with the restricted root unit.
   Step 1 gives the equivalent detection of derived completeness. Height zero, empty
   children, the zero object and arbitrary unbounded complexes are all included. -/
theorem qcqsCompletionUnitLocality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{t}) [CompactSpace T] [QuasiSeparatedSpace T]
    (_hl : IsUnit (l : Γ(T, ⊤))) :
    (∀ H : D l E T none,
      IsIso ((completionUnit l E T none).app H) ↔ IsComplete l E T none H) ∧
    (∀ (S : Scheme.{t}) [CompactSpace S] [QuasiSeparatedSpace S] (r : S ⟶ T),
      (WeaklyEtale r ∨ (IsClosedImmersion r ∧ IsCompact ((Set.range r.base)ᶜ))) →
      PreservesFiniteLimits (ordinaryPull l E r) ∧
      PreservesFiniteColimits (ordinaryPull l E r) ∧
      IsIso (ordinaryCoefficientMap l E r) ∧
      (∀ n : ℕ, ordinaryCoefficientMap l E r ≫
          limit.π (integralCoefficientSheafSystem l E S) (op n) =
        (ordinaryRingInverse.{t, u} r).map
            (limit.π (integralCoefficientSheafSystem l E T) (op n)) ≫
          ((Adjunction.ofIsRightAdjoint (ordinaryRingPush.{t, u} r)).homEquiv _ _).symm
              (ordinaryFiniteRingMap l E r n)) ∧
      (∃ (τ : tower l E T none ⋙
          (Functor.whiskeringRight ℕᵒᵖ (Cx l E T none) (Cx l E S none)).obj
            (ordinaryComplexPull l E r) ≅
          ordinaryComplexPull l E r ⋙ tower l E S none)
        (χ : roos l E T none ⋙ ordinaryComplexPull l E r ≅
          ordinaryComplexPull l E r ⋙ roos l E S none)
        (hgood : ∀ P : (Good l E T none).FullSubcategory,
          Good l E S none ((ordinaryComplexPull l E r).obj P.obj))
        (α : completion l E T none ⋙ ordinaryDerivedPull l E r ≅
          ordinaryDerivedPull l E r ⋙ completion l E S none),
        (∀ (P : Cx l E T none) (n : ℕ),
          (ordinaryComplexPull l E r).map (((augmentation l E T none).app P).app (op n)) ≫
              (τ.hom.app P).app (op n) =
            ((augmentation l E S none).app ((ordinaryComplexPull l E r).obj P)).app (op n)) ∧
        (∀ P : Cx l E T none,
          χ.hom.app P ≫ CochainComplex.mappingCocone.fst
              (ordinaryRoosEndomorphism l E ((ordinaryComplexPull l E r).obj P)) =
            (ordinaryComplexPull l E r).map
                (CochainComplex.mappingCocone.fst (ordinaryRoosEndomorphism l E P)) ≫
              piComparison (ordinaryComplexPull l E r)
                (fun n : ℕ ↦ ((tower l E T none).obj P).obj (op n)) ≫
              Limits.Pi.map (fun n : ℕ ↦ (τ.hom.app P).app (op n))) ∧
        (∀ (P : Cx l E T none) (i : ℤ),
          (χ.hom.app P).f i ≫
              (CochainComplex.mappingCocone.snd
                (ordinaryRoosEndomorphism l E ((ordinaryComplexPull l E r).obj P))).v
                  i (i + -1) rfl =
            (ordinaryPull l E r).map
                ((CochainComplex.mappingCocone.snd (ordinaryRoosEndomorphism l E P)).v
                  i (i + -1) rfl) ≫
              (piComparison (ordinaryComplexPull l E r)
                (fun n : ℕ ↦ ((tower l E T none).obj P).obj (op n))).f (i + -1) ≫
              (Limits.Pi.map (fun n : ℕ ↦ (τ.hom.app P).app (op n))).f (i + -1)) ∧
        (∀ P : (Good l E T none).FullSubcategory,
          (ordinaryDerivedPull l E r).map ((completionComparison l E T none).hom.app P) ≫
              ordinaryComplexCounit l E r ((roos l E T none).obj P.obj) ≫
              DerivedCategory.Q.map (χ.hom.app P.obj) =
            α.hom.app ((qGood l E T none).obj P) ≫
              (completion l E S none).map (ordinaryComplexCounit l E r P.obj) ≫
              (completionComparison l E S none).hom.app
                ⟨(ordinaryComplexPull l E r).obj P.obj, hgood P⟩) ∧
        (∀ H : D l E T none,
          (ordinaryDerivedPull l E r).map ((completionUnit l E T none).app H) ≫
              α.hom.app H =
            (completionUnit l E S none).app ((ordinaryDerivedPull l E r).obj H))) ∧
      (∀ H : D l E T none, IsComplete l E T none H →
        IsComplete l E S none ((ordinaryDerivedPull l E r).obj H))) ∧
    (∀ (d : ℕ) (V : Fin d → Scheme.{t}) (toT : ∀ v : Fin d, V v ⟶ T)
      (root : Fin d) (parent left right : Fin d → Fin d)
      (leftEdge : ∀ v : Fin d, V (left v) ⟶ V v)
      (rightEdge : ∀ v : Fin d, V (right v) ⟶ V v) (leaf : Fin d → Prop),
      (∃ e : V root ≅ T, e.hom = toT root) → parent root = root →
      (∀ v, v ≠ root → (parent v).val < v.val) →
      (∀ v, CompactSpace (V v)) → (∀ v, QuasiSeparatedSpace (V v)) →
      (∀ v, IsImmersion (toT v)) →
      (∀ v, v ≠ root → left (parent v) = v ∨ right (parent v) = v) →
      (∀ v, leaf v ↔ ∀ z, z ≠ root → parent z ≠ v) →
      (∀ v, ¬ leaf v →
        left v ≠ right v ∧ v.val < (left v).val ∧ v.val < (right v).val ∧
        parent (left v) = v ∧ parent (right v) = v ∧
        leftEdge v ≫ toT v = toT (left v) ∧ rightEdge v ≫ toT v = toT (right v) ∧
        IsOpenImmersion (leftEdge v) ∧ QuasiCompact (leftEdge v) ∧
        IsClosedImmersion (rightEdge v) ∧
        Set.range (leftEdge v).base ∪ Set.range (rightEdge v).base = Set.univ ∧
        Disjoint (Set.range (leftEdge v).base) (Set.range (rightEdge v).base)) →
      ∀ (I : ∀ v : Fin d, Type w) (W : ∀ v : Fin d, I v → (V v).ProEt),
      (∀ (v : Fin d) (a : I v), leaf v → Nonempty (V v) → CompactSpace (W v a).left) →
      (∀ (v : Fin d) (a : I v), leaf v → Nonempty (V v) →
        QuasiSeparatedSpace (W v a).left) →
      (∀ v, leaf v → Nonempty (V v) →
        Presieve.ofArrows (fun a : I v ↦ W v a)
          (fun a ↦ (MorphismProperty.Over.homMk (W v a).hom (Category.comp_id _) :
            W v a ⟶ ProEt.mk (𝟙 (V v)))) ∈
          ProEt.precoverage (V v) (ProEt.mk (𝟙 (V v)))) →
      ∀ H : D l E T none,
        (IsIso ((completionUnit l E T none).app H) ↔
          ∀ v, leaf v → Nonempty (V v) → ∀ a : I v,
            IsIso ((ordinaryDerivedPull l E ((W v a).hom ≫ toT v)).map
              ((completionUnit l E T none).app H))) ∧
        (IsComplete l E T none H ↔
          ∀ v, leaf v → Nonempty (V v) → ∀ a : I v,
            IsComplete l E (W v a).left none
              ((ordinaryDerivedPull l E ((W v a).hom ≫ toT v)).obj H)))
:= by
  exact ⟨canonicalCompletionUnitCriterion l E T,
    qcqsCompletionUnitRestriction l E T _hl, qcqsCompletionUnitTree l E T _hl⟩

end WeilConjectures.IntegralOnSlice
