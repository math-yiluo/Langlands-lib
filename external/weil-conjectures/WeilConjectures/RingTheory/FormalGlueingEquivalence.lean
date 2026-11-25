/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormalGlueingData
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.AlgebraicGeometry.FormalGlueingCanonicalMaps
import WeilConjectures.RingTheory.FormalGlueingComplexExact
import WeilConjectures.RingTheory.FormalGlueingCanonicalFunctor
import WeilConjectures.RingTheory.FormalGlueingMorphismLifting
import WeilConjectures.RingTheory.FormalGlueingEssentialSurjectivity

/-!
# The canonical functor for formal glueing

Source: Stacks Project, More on Algebra, Remark 05EL and Proposition 05ER
(blueprint: prop-weil-pbc-formal-glueing-equivalence).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace FormalGlueing

/-- The canonical comparison and interchange maps are isomorphisms, and the prescribed
objects and maps form a functor. Under flatness and the quotient isomorphism this functor
is fully faithful and essentially surjective. Heterogeneous equalities identify structural
maps after the preceding equalities of their bundled source and target modules; they
specify the actual canonical maps, not merely isomorphic choices of those maps.
Source: Stacks Project, More on Algebra, Remark 05EL and Proposition 05ER
(blueprint: prop-weil-pbc-formal-glueing-equivalence).

Proof (the node's eleven steps):
1. The interchange map has inverse the reverse interchange; comparison commutes with
   extension of scalars [lem-weil-pbc-formal-glueing-canonical-maps]. The square for the
   canonical object takes each double fraction of a pure tensor to the same fraction
   of that tensor. The cocycle takes each triple fraction to the fraction in reverse
   order on both sides. Additivity extends the square from pure tensors to all elements.
2. Naturality of comparison and interchange follows on fractions from the formulas for
   localization and base change [def-weil-pbc-module-localization,
   def-weil-module-base-change]. Their compatibility with identities and composition
   gives the functor laws [lem-weil-pbc-formal-glueing-canonical-maps].
3. Under the additional hypotheses the exact glueing complex identifies an R-module N
   with compatible families in its scalar extension and localizations
   [lem-weil-pbc-formal-glueing-complex-exact].
4. Equality of two elements after iterated localization implies equality in N localized
   at the product: clear each denominator successively
   [def-weil-pbc-module-localization-away].
5. If two maps have the same canonical components, apply injectivity of the initial map
   in the exact complex to their values on each element. This proves faithfulness.
6. For a morphism between canonical objects, its components on m give a compatible
   family by naturality and step 4. Exactness gives a unique preimage u(m). Injectivity
   proves linearity; agreement on pure tensors and fractions identifies all components
   with the base change and localizations of u. Thus the functor is full.
7. For a glueing datum form H^0, the module of compatible families. Its chart projections
   extend to bijections from its localizations [lem-weil-pbc-formal-glueing-H0-localization].
   Its prime projection extends by tensoring to Psi'. The fraction formulas verify that
   Psi is a morphism from the canonical datum of H^0 to the given datum.
8. Every localization of Psi' is bijective by its compatibility with the chart maps.
   Exact localization [lem-weil-pbc-localization-module-exact] makes its kernel and
   cokernel vanish locally. Finitely many annihilating powers of the generators imply
   that both are I-power torsion.
9. Torsion base change [lem-weil-pbc-torsion-submodule-flat-base-change-iso] writes an
   element of the kernel as h tensor 1 with h torsion in H^0. Its prime projection and
   all chart projections vanish; hence h = 0 and Psi' is injective.
10. The cokernel Q identifies with its base change
    [lem-weil-pbc-torsion-module-flat-base-change-iso]. Descend the resulting extension
    of Q tensor S by H^0 tensor S to an extension E of Q by H^0
    [lem-weil-pbc-torsion-extension-flat-descent], with E tensor S isomorphic to M'.
11. Q vanishes in each localization, so H^0 -> E is locally bijective. Combine its
    localized inverses with the chart maps of Psi and the prime isomorphism to obtain
    Can(E) -> M. Precompose the compatibility equations with these local bijections
    to check them. Componentwise inverses satisfy the same equations and give an inverse
    morphism. This proves essential surjectivity, and step 6 gives the equivalence. -/
theorem exists_canonical_equivalence {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (t : ℕ) (f : Fin t → R) :
    (∀ (P : ModuleCat.{max u v w} R) (a b : R),
      Function.Bijective (compare φ a P) ∧ Function.Bijective (swap a b P)) ∧
    ∃ Can : ModuleCat.{max u v w} R ⥤ Data.{u, v, max u v w} φ f,
      (∀ M : ModuleCat.{max u v w} R,
        (Can.obj M).M' = extend φ M ∧
        (∀ i : Fin t, (Can.obj M).M i =
          ModuleCat.of (Localization.Away (f i)) (LocalizedModule.Away (f i) M)) ∧
        (∀ i : Fin t, HEq ((Can.obj M).alpha i).toLinearMap (compare φ (f i) M)) ∧
        (∀ i j : Fin t,
          HEq ((Can.obj M).alpha_overlap i j).toLinearMap (swap (f i) (f j) M))) ∧
      (∀ (M N : ModuleCat.{max u v w} R) (h : M ⟶ N),
        HEq (Can.map h).prime (extendMap φ h.hom) ∧
        ∀ i : Fin t, HEq ((Can.map h).chart i) (localMap (f i) h.hom)) ∧
      (φ.Flat →
        Function.Bijective
          (Ideal.quotientMap ((Ideal.span (Set.range f)).map φ) φ Ideal.le_comap_map) →
        (∀ M N : ModuleCat.{max u v w} R,
          Function.Bijective (Can.map : (M ⟶ N) → (Can.obj M ⟶ Can.obj N))) ∧
        (∀ X : Data.{u, v, max u v w} φ f,
          ∃ M : ModuleCat.{max u v w} R, Nonempty (Can.obj M ≅ X))) := by
  classical
  refine ⟨?_, ?_⟩
  · intro P a b
    refine ⟨(compare_properties φ P a).2.2.2.2, ?_⟩
    have hs := (swap_properties P a b).2.2.2.2
    constructor
    · intro x y h
      have hx := congrArg (fun k => k x) hs.1
      have hy := congrArg (fun k => k y) hs.1
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
        hx.symm.trans ((congrArg (swap b a P) h).trans hy)
    · intro y
      refine ⟨swap b a P y, ?_⟩
      exact congrArg (fun k => k y) hs.2
  · obtain ⟨Can, hobj, hmap⟩ := exists_canonical_functor φ t f
    refine ⟨Can, hobj, hmap, ?_⟩
    intro hflat hquot
    refine ⟨?_, canonical_essentially_surjective φ t f Can hobj hflat hquot⟩
    intro M N
    refine ⟨?_, canonical_map_surjective φ t f Can hobj hmap hflat hquot M N⟩
    intro a b hab
    have hprime : extendMap φ a.hom = extendMap φ b.hom :=
      eq_of_heq ((hmap M N a).1.symm.trans
        ((heq_of_eq (congrArg (fun z => z.prime) hab)).trans (hmap M N b).1))
    have hchart (i : Fin t) : localMap (f i) a.hom = localMap (f i) b.hom :=
      eq_of_heq (((hmap M N a).2 i).symm.trans
        ((heq_of_eq (congrArg (fun z => z.chart i) hab)).trans ((hmap M N b).2 i)))
    let : Algebra R S := φ.toAlgebra
    have hinj := (RingTheory.formalGlueingComplexExact φ hflat t f hquot N).1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    apply hinj
    apply Prod.ext
    · have hp := congrArg (fun k => k (TensorProduct.tmul R (1 : S) m)) hprime
      simpa [extendMap, LinearMap.baseChange_tmul] using hp
    · funext i
      have hc := congrArg (fun k => k (LocalizedModule.mk m 1)) (hchart i)
      simpa [localMap, IsLocalizedModule.map_LocalizedModules] using hc

end FormalGlueing
