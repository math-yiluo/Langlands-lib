/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Resolution extensionality for derived bifunctors -/

@[expose] public section
set_option autoImplicit false
universe u v w z
open CategoryTheory

/-- Two natural transformations between derived bifunctors are equal when they agree on
all pairs of resolving K-flat complexes.

Source: Stacks Tags 04VK, 06YS and 06YU; the two-variable localization step in
`new-sf-normalized-pro-scalar-tensor-geometric-square-from-flat`.
Proof: choose a complex representing each derived object and resolve each by a complex
satisfying P. The augmentation quasi-isomorphisms become isomorphisms after localization.
Their product gives an isomorphism from a pair where the components agree to the chosen
derived pair. Apply naturality of both transformations and cancel its image under U.
(blueprint: new-sf-bifunctor-kflat-localization-extensionality). -/
theorem bifunctor_kflat_localization_extensionality
    {C : Type u} [Category.{v, u} C] [Abelian C] [HasDerivedCategory C]
    (P : ObjectProperty (CochainComplex C ℤ))
    (resolve : ∀ K : CochainComplex C ℤ,
      ∃ (L : CochainComplex C ℤ) (p : L ⟶ K), P L ∧ QuasiIso p)
    {E : Type w} [Category.{z, w} E]
    (U V : DerivedCategory C × DerivedCategory C ⥤ E)
    (s t : U ⟶ V)
    (h : ∀ (K L : CochainComplex C ℤ), P K → P L →
      s.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) =
        t.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) :
    s = t := by
  classical
  ext X
  obtain ⟨K, p, hK, hp⟩ := resolve (DerivedCategory.Q.objPreimage X.1)
  obtain ⟨L, q, hL, hq⟩ := resolve (DerivedCategory.Q.objPreimage X.2)
  let : QuasiIso p := hp
  let : QuasiIso q := hq
  let eK := asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso X.1
  let eL := asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso X.2
  let e : (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅ X := eK.prod eL
  rw [← cancel_epi (U.map e.hom), s.naturality, t.naturality, h K L hK hL]

end
