/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SupportCohomology

/-!
# The natural triangle of cohomology with support

Let `i : Z ⟶ X` be a closed immersion with open complement `j : U ⟶ X`. On the small étale site
and on the small pro-étale site of `X`, the open `U` is a subobject of the terminal object `X`,
so for an injective sheaf `I` the restriction `Γ(X, I) ⟶ I(U)` is a split epimorphism
(`CategoryTheory.Sheaf.isSplitEpi_ΓRes_of_injective`). Hence, by the site-generic construction
`CategoryTheory.Sheaf.ΓSupportRightDerivedTriangle`, for a bounded below complex `K` there is a
distinguished triangle

`RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K) ⟶ RΓ_Z(X, K)[1]`

which is a functor of `K`, and taking cohomology gives the long exact sequence

`⋯ ⟶ H^q_Z(X, K) ⟶ H^q(X, K) ⟶ H^q(U, K) ⟶ H^{q+1}_Z(X, K) ⟶ ⋯`,

natural in `K`. The triangle is also functorial in the pair: for an étale (resp. weakly étale)
`X`-scheme `V`, the restriction to the pair `(V, V ×_X U)` gives a morphism of triangles
(`AlgebraicGeometry.Etale.sectionsWithSupportTriangleToPair`), and morphisms of pairs inside the
site induce morphisms of triangles (`CategoryTheory.Sheaf.pairRightDerivedTriangleMap`). For an
arbitrary morphism of pairs `e : (X', X' ∖ Z') ⟶ (X, X ∖ Z)` of schemes, the pullback maps form a
morphism of triangles compatible with composition
(`AlgebraicGeometry.Etale.sectionsWithSupportTrianglePullback` in
`WeilConjectures.SixFunctors.Etale.SupportCohomologyTrianglePullback`).

## Main definitions

- `AlgebraicGeometry.Etale.sectionsWithSupportTriangle`,
  `AlgebraicGeometry.ProEtale.sectionsWithSupportTriangle`: the triangles as functors of `K`.
- `AlgebraicGeometry.Etale.sectionsWithSupportδ`, `AlgebraicGeometry.ProEtale.sectionsWithSupportδ`:
  the natural connecting maps `RΓ(U, -) ⟶ RΓ_Z(X, -)[1]`.
- `AlgebraicGeometry.Etale.sectionsWithSupportTriangleToPair`,
  `AlgebraicGeometry.ProEtale.sectionsWithSupportTriangleToPair`: functoriality in the pair.

## Main statements

- `AlgebraicGeometry.Etale.sectionsWithSupportTriangle_obj_distinguished`,
  `AlgebraicGeometry.Etale.exact_derivedSupportCohomology_sectionsWithSupportTriangle` and their
  pro-étale versions.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite Pretriangulated DerivedCategory

namespace AlgebraicGeometry

open Scheme

lemma MorphismProperty.Over.subsingleton_hom_of_mono {P Q : MorphismProperty Scheme.{u}}
    [Q.IsMultiplicative] {X : Scheme.{u}} (W Y : P.Over Q X) [Mono Y.hom] :
    Subsingleton (W ⟶ Y) :=
  ⟨fun f g ↦ CategoryTheory.MorphismProperty.Over.Hom.ext ((cancel_mono Y.hom).1
    ((CategoryTheory.MorphismProperty.Over.w f).trans
      (CategoryTheory.MorphismProperty.Over.w g).symm))⟩

instance Scheme.Etale.subsingleton_hom_mk {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (W : X.Etale) : Subsingleton (W ⟶ Scheme.Etale.mk j) :=
  have : Mono (Scheme.Etale.mk j).hom := inferInstanceAs (Mono j)
  MorphismProperty.Over.subsingleton_hom_of_mono (P := @Etale) (Q := ⊤) W (Scheme.Etale.mk j)

instance Scheme.ProEt.subsingleton_hom_mk {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (W : X.ProEt) : Subsingleton (W ⟶ Scheme.ProEt.mk j) :=
  have : Mono (Scheme.ProEt.mk j).hom := inferInstanceAs (Mono j)
  MorphismProperty.Over.subsingleton_hom_of_mono (P := @WeaklyEtale) (Q := ⊤) W
    (Scheme.ProEt.mk j)

/-- In a category with binary products, the first projection `V ⨯ U ⟶ V` is a monomorphism if
every `Hom(W, U)` is a subsingleton. -/
instance mono_prod_fst_of_subsingleton {𝒞 : Type*} [Category 𝒞] (V U : 𝒞) [HasBinaryProduct V U]
    [∀ W, Subsingleton (W ⟶ U)] : Mono (prod.fst : V ⨯ U ⟶ V) :=
  ⟨fun _ _ h ↦ prod.hom_ext h (Subsingleton.elim _ _)⟩

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

namespace Etale

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- Blueprint `thm-pur-with-support-exactness`: Long exact sequence for cohomology with support

The distinguished triangle `RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K) ⟶ RΓ_Z(X, K)[1]` of a closed
immersion `i : Z ⟶ X` with open complement `U`, as a functor of the bounded below complex `K`
of étale sheaves on `X`. Its first two maps are induced by the inclusion of the sections with
support and the restriction to `U`; on a bounded below complex of injectives `I` the
connecting map is that of the short exact sequence `0 ⟶ Γ_Z(X, I) ⟶ Γ(X, I) ⟶ Γ(U, I) ⟶ 0`. -/
noncomputable def sectionsWithSupportTriangle :
    Plus (Sheaf X.smallEtaleTopology A) ⥤ Triangle (DerivedCategory A) :=
  Sheaf.ΓSupportRightDerivedTriangle X.smallEtaleTopology A (Scheme.Etale.mk i.openComplement.ι)

/-- The natural connecting map `δ : RΓ(U, K) ⟶ RΓ_Z(X, K)[1]`, natural in the bounded below
complex `K`. -/
noncomputable def sectionsWithSupportδ :
    Plus.ι ⋙ ((sheafSections X.smallEtaleTopology A).obj
        (op (Scheme.Etale.mk i.openComplement.ι))).rightDerivedFunctor ⟶
      Plus.ι ⋙ rightDerivedSectionsWithSupport A i ⋙ shiftFunctor _ (1 : ℤ) :=
  ShortComplex.rightDerivedδ (S := Sheaf.ΓSupportShortComplex X.smallEtaleTopology A
    (op (Scheme.Etale.mk i.openComplement.ι)))
    (Sheaf.shortExactOnInjectives_ΓSupportShortComplex _ A _)

lemma sectionsWithSupportTriangle_obj (K : Plus (Sheaf X.smallEtaleTopology A)) :
    (sectionsWithSupportTriangle A i).obj K = Triangle.mk
      ((Functor.rightDerivedFunctorNatTrans (Sheaf.ΓSupportι X.smallEtaleTopology A
        (op (Scheme.Etale.mk i.openComplement.ι)))).app K.obj)
      ((Functor.rightDerivedFunctorNatTrans (Sheaf.natTransΓRes X.smallEtaleTopology A
        (op (Scheme.Etale.mk i.openComplement.ι)))).app K.obj)
      ((sectionsWithSupportδ A i).app K) :=
  rfl

/-- Blueprint `thm-pur-with-support-exactness`: Long exact sequence for cohomology with support

The triangle `RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K) ⟶ RΓ_Z(X, K)[1]` is distinguished. -/
theorem sectionsWithSupportTriangle_obj_distinguished
    (K : Plus (Sheaf X.smallEtaleTopology A)) :
    (sectionsWithSupportTriangle A i).obj K ∈ distTriang _ :=
  Sheaf.ΓSupportRightDerivedTriangle_obj_distinguished _ _ _ K

/-- Blueprint `thm-pur-with-support-exactness`: Long exact sequence for cohomology with support

**The long exact sequence, natural in `K`.** For a bounded below complex `K` of étale sheaves
on `X` (e.g. a sheaf in degree `0`), the sequence

`⋯ ⟶ H^q_Z(X, K) ⟶ H^q(X, K) ⟶ H^q(U, K) ⟶ H^{q+1}_Z(X, K) ⟶ H^{q+1}(X, K) ⟶ ⋯`

obtained by taking cohomology of the triangle `sectionsWithSupportTriangle` is exact. All maps
are natural in `K`, since `sectionsWithSupportTriangle` is a functor. -/
theorem exact_derivedSupportCohomology_sectionsWithSupportTriangle
    (K : Plus (Sheaf X.smallEtaleTopology A)) (q₀ q₁ : ℤ) (h : q₀ + 1 = q₁) :
    (ShortComplex.mk _ _ (HomologySequence.comp_δ _
        (sectionsWithSupportTriangle_obj_distinguished A i K) q₀ q₁ h)).Exact ∧
      (ShortComplex.mk _ _ (HomologySequence.δ_comp _
        (sectionsWithSupportTriangle_obj_distinguished A i K) q₀ q₁ h)).Exact ∧
      (ShortComplex.mk ((homologyFunctor A q₀).map
          ((sectionsWithSupportTriangle A i).obj K).mor₁)
        ((homologyFunctor A q₀).map ((sectionsWithSupportTriangle A i).obj K).mor₂)
        (by simp only [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _
          (sectionsWithSupportTriangle_obj_distinguished A i K), Functor.map_zero])).Exact :=
  ShortComplex.exact_homology_rightDerivedTriangle _ K q₀ q₁ h

/-- Blueprint `thm-pur-with-support-exactness`: Long exact sequence for cohomology with support

**Functoriality in the pair.** For an étale `X`-scheme `V`, the restriction from the pair
`(X, U)` to the pair `(V, V ×_X U)` (whose closed complement is the preimage of `Z`) is a
morphism from `sectionsWithSupportTriangle` to the triangle
`RΓ_{V ∖ V ×_X U}(V, K) ⟶ RΓ(V, K) ⟶ RΓ(V ×_X U, K) ⟶ ⋯` of the pair, natural in `K`. -/
noncomputable def sectionsWithSupportTriangleToPair (V : X.Etale) :
    sectionsWithSupportTriangle A i ⟶ Sheaf.pairRightDerivedTriangle X.smallEtaleTopology A
      (Arrow.mk (prod.fst : V ⨯ Scheme.Etale.mk i.openComplement.ι ⟶ V)) :=
  Sheaf.ΓSupportRightDerivedTriangleToPair _ _ _
    (Arrow.mk (prod.fst : V ⨯ Scheme.Etale.mk i.openComplement.ι ⟶ V))
    (prod.snd : V ⨯ Scheme.Etale.mk i.openComplement.ι ⟶ _)

end Etale

namespace ProEtale

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- Blueprint `thm-pur-with-support-exactness`: Long exact sequence for cohomology with support

The distinguished triangle `RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K) ⟶ RΓ_Z(X, K)[1]` on the small
pro-étale site of `X`, as a functor of the bounded below complex `K` of pro-étale sheaves. The
argument is the same as on the étale site: the open `U` is a subobject of the terminal object
of the site. -/
noncomputable def sectionsWithSupportTriangle :
    Plus (Sheaf (Scheme.ProEt.topology X) A) ⥤ Triangle (DerivedCategory A) :=
  Sheaf.ΓSupportRightDerivedTriangle (Scheme.ProEt.topology X) A
    (Scheme.ProEt.mk i.openComplement.ι)

/-- The natural connecting map `δ : RΓ(U, K) ⟶ RΓ_Z(X, K)[1]` on the pro-étale site. -/
noncomputable def sectionsWithSupportδ :
    Plus.ι ⋙ ((sheafSections (Scheme.ProEt.topology X) A).obj
        (op (Scheme.ProEt.mk i.openComplement.ι))).rightDerivedFunctor ⟶
      Plus.ι ⋙ rightDerivedSectionsWithSupport A i ⋙ shiftFunctor _ (1 : ℤ) :=
  ShortComplex.rightDerivedδ (S := Sheaf.ΓSupportShortComplex (Scheme.ProEt.topology X) A
    (op (Scheme.ProEt.mk i.openComplement.ι)))
    (Sheaf.shortExactOnInjectives_ΓSupportShortComplex _ A _)

lemma sectionsWithSupportTriangle_obj (K : Plus (Sheaf (Scheme.ProEt.topology X) A)) :
    (sectionsWithSupportTriangle A i).obj K = Triangle.mk
      ((Functor.rightDerivedFunctorNatTrans (Sheaf.ΓSupportι (Scheme.ProEt.topology X) A
        (op (Scheme.ProEt.mk i.openComplement.ι)))).app K.obj)
      ((Functor.rightDerivedFunctorNatTrans (Sheaf.natTransΓRes (Scheme.ProEt.topology X) A
        (op (Scheme.ProEt.mk i.openComplement.ι)))).app K.obj)
      ((sectionsWithSupportδ A i).app K) :=
  rfl

/-- Blueprint `thm-pur-with-support-exactness`: Long exact sequence for cohomology with support

The pro-étale triangle `RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K) ⟶ RΓ_Z(X, K)[1]` is distinguished. -/
theorem sectionsWithSupportTriangle_obj_distinguished
    (K : Plus (Sheaf (Scheme.ProEt.topology X) A)) :
    (sectionsWithSupportTriangle A i).obj K ∈ distTriang _ :=
  Sheaf.ΓSupportRightDerivedTriangle_obj_distinguished _ _ _ K

/-- Blueprint `thm-pur-with-support-exactness`: Long exact sequence for cohomology with support

**The long exact sequence on the pro-étale site, natural in `K`.** For a bounded below complex
`K` of pro-étale sheaves on `X`, the sequence

`⋯ ⟶ H^q_Z(X, K) ⟶ H^q(X, K) ⟶ H^q(U, K) ⟶ H^{q+1}_Z(X, K) ⟶ H^{q+1}(X, K) ⟶ ⋯`

is exact, with all maps natural in `K`. -/
theorem exact_derivedSupportCohomology_sectionsWithSupportTriangle
    (K : Plus (Sheaf (Scheme.ProEt.topology X) A)) (q₀ q₁ : ℤ) (h : q₀ + 1 = q₁) :
    (ShortComplex.mk _ _ (HomologySequence.comp_δ _
        (sectionsWithSupportTriangle_obj_distinguished A i K) q₀ q₁ h)).Exact ∧
      (ShortComplex.mk _ _ (HomologySequence.δ_comp _
        (sectionsWithSupportTriangle_obj_distinguished A i K) q₀ q₁ h)).Exact ∧
      (ShortComplex.mk ((homologyFunctor A q₀).map
          ((sectionsWithSupportTriangle A i).obj K).mor₁)
        ((homologyFunctor A q₀).map ((sectionsWithSupportTriangle A i).obj K).mor₂)
        (by simp only [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _
          (sectionsWithSupportTriangle_obj_distinguished A i K), Functor.map_zero])).Exact :=
  ShortComplex.exact_homology_rightDerivedTriangle _ K q₀ q₁ h

/-- Blueprint `thm-pur-with-support-exactness`: Long exact sequence for cohomology with support

**Functoriality in the pair on the pro-étale site.** For a weakly étale `X`-scheme `V`, the
restriction from the pair `(X, U)` to the pair `(V, V ×_X U)` is a morphism of triangles,
natural in `K`. -/
noncomputable def sectionsWithSupportTriangleToPair (V : X.ProEt) :
    sectionsWithSupportTriangle A i ⟶ Sheaf.pairRightDerivedTriangle (Scheme.ProEt.topology X) A
      (Arrow.mk (prod.fst : V ⨯ Scheme.ProEt.mk i.openComplement.ι ⟶ V)) :=
  Sheaf.ΓSupportRightDerivedTriangleToPair _ _ _
    (Arrow.mk (prod.fst : V ⨯ Scheme.ProEt.mk i.openComplement.ι ⟶ V))
    (prod.snd : V ⨯ Scheme.ProEt.mk i.openComplement.ι ⟶ _)

end ProEtale

end AlgebraicGeometry
