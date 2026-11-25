/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence

/-!
# The derived base change maps of a cube

Consider a commutative cube of schemes, whose top face is a square `W' ⟶ W`, `Z' ⟶ Z` over the
bottom face `X' ⟶ X`, `Y' ⟶ Y`:

```
  W' --h--> W          Z' --gb--> Z
  |         |          |         |
  b'        b          p'        p
  ↓         ↓          ↓         ↓
  X' --g'-> X          Y' --g--> Y
```

with `a : W ⟶ Z`, `a' : W' ⟶ Z'`, `e : X ⟶ Y`, `e' : X' ⟶ Y'`. The derived base change maps
`Ex_*` of the four vertical faces paste in two ways to a map
`Lg'^* Le^* Rp_* ⟶ Rb'_* La'^* Lgb^*`, and the two composites agree
(`AlgebraicGeometry.Etale.derivedBaseChangeMap_cube`). The proof transposes along
`Lb'^* ⊣ Rb'_*` and reduces to the coherence of the composition isomorphisms of the derived
pullbacks (`AlgebraicGeometry.Etale.derivedSquareUpperStarIso_cube`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {W W' X X' Y Y' Z Z' : Scheme.{u}} {a : W ⟶ Z} {b : W ⟶ X} {p : Z ⟶ Y} {e : X ⟶ Y}
  {gb : Z' ⟶ Z} {p' : Z' ⟶ Y'} {g : Y' ⟶ Y} {h : W' ⟶ W} {b' : W' ⟶ X'} {g' : X' ⟶ X}
  {a' : W' ⟶ Z'} {e' : X' ⟶ Y'}

-- a long chain of rewritings with the associativity of the composition isomorphisms
/-- **Coherence of the square isomorphisms of a cube**: the two composites
`Lb'^* Lg'^* Le^* ≅ La'^* Lgb^* Lp^*` of square isomorphisms of the derived pullbacks along the
faces of a commutative cube agree. Both are identified with the composite of the composition
isomorphisms along the diagonal `W' ⟶ Y`. -/
lemma derivedSquareUpperStarIso_cube (S1 : CommSq a b p e) (S2 : CommSq gb p' p g)
    (S3 : CommSq h b' b g') (S4 : CommSq a' b' p' e') (S0 : CommSq g' e' e g)
    (S5 : CommSq h a' a gb) (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (derivedSquareUpperStarIso A S3).hom.app (L((e)^*[A]).obj K) ≫
        L((h)^*[A]).map ((derivedSquareUpperStarIso A S1).hom.app K) ≫
        (derivedSquareUpperStarIso A S5).inv.app (L((p)^*[A]).obj K) =
      L((b')^*[A]).map ((derivedSquareUpperStarIso A S0).inv.app K) ≫
        (derivedSquareUpperStarIso A S4).hom.app (L((g)^*[A]).obj K) ≫
        L((a')^*[A]).map ((derivedSquareUpperStarIso A S2).hom.app K) := by
  have hm : h ≫ b = b' ≫ g' := S3.w
  have hn : a ≫ p = b ≫ e := S1.w
  have hr : h ≫ a = a' ≫ gb := S5.w
  have hs : g' ≫ e = e' ≫ g := S0.w
  have hv : a' ≫ p' = b' ≫ e' := S4.w
  have hw : gb ≫ p = p' ≫ g := S2.w
  -- the canonical isomorphism `L(t)^* ≅ Lb'^* Lg'^* Le^*` along the diagonal `t`
  rw [← cancel_epi ((leftDerivedUpperStarComp A b' (g' ≫ e) (b' ≫ g' ≫ e) rfl).hom.app K ≫
    L((b')^*[A]).map ((leftDerivedUpperStarComp A g' e (g' ≫ e) rfl).hom.app K))]
  simp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  have ht₁ : b' ≫ g' ≫ e = (h ≫ b) ≫ e := by rw [hm, Category.assoc]
  have ht₂ : b' ≫ g' ≫ e = (a' ≫ p') ≫ g := by rw [hs, hv, Category.assoc]
  have ht₃ : b' ≫ g' ≫ e = (h ≫ a) ≫ p := by rw [Category.assoc, hn, reassoc_of% hm]
  -- the left hand side
  rw [leftDerivedUpperStarComp_assoc'_app_assoc A b' g' e (h ≫ b) (g' ≫ e) (b' ≫ g' ≫ e)
      hm rfl ht₁, Iso.hom_inv_id_app_assoc,
    ← leftDerivedUpperStarComp_assoc'_app_assoc A h b e (h ≫ b) (a ≫ p) (b' ≫ g' ≫ e)
      rfl hn ht₁, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [leftDerivedUpperStarComp_assoc'_app_assoc A h a p (h ≫ a) (a ≫ p) (b' ≫ g' ≫ e)
      rfl rfl ht₃, Iso.hom_inv_id_app_assoc]
  -- the right hand side
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [leftDerivedUpperStarComp_assoc'_app_assoc A b' e' g (a' ≫ p') (g' ≫ e) (b' ≫ g' ≫ e)
      hv hs ht₂, Iso.hom_inv_id_app_assoc,
    ← leftDerivedUpperStarComp_assoc'_app_assoc A a' p' g (a' ≫ p') (gb ≫ p) (b' ≫ g' ≫ e)
      rfl hw ht₂, ← Functor.map_comp_assoc (L((a')^*[A])), Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [leftDerivedUpperStarComp_assoc'_app A a' gb p (h ≫ a) (gb ≫ p) (b' ≫ g' ≫ e)
      hr rfl ht₃]

-- the derived functors involved are large terms
/-- **The derived base change maps of a cube paste coherently**: for a commutative cube as in the
module docstring, the two composites `Lg'^* Le^* Rp_* ⟶ Rb'_* La'^* Lgb^*` of derived base
change maps `Ex_*` of its vertical faces and square isomorphisms of its horizontal faces agree. -/
theorem derivedBaseChangeMap_cube (S1 : CommSq a b p e) (S2 : CommSq gb p' p g)
    (S3 : CommSq h b' b g') (S4 : CommSq a' b' p' e') (S0 : CommSq g' e' e g)
    (S5 : CommSq h a' a gb) (M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    L((g')^*[A]).map ((derivedBaseChangeMap A S1).app M) ≫
        (derivedBaseChangeMap A S3).app (L((a)^*[A]).obj M) ≫
        R((b')_*[A]).map ((derivedSquareUpperStarIso A S5).inv.app M) =
      (derivedSquareUpperStarIso A S0).inv.app (R((p)_*[A]).obj M) ≫
        L((e')^*[A]).map ((derivedBaseChangeMap A S2).app M) ≫
        (derivedBaseChangeMap A S4).app (L((gb)^*[A]).obj M) := by
  apply ((derivedUpperStarLowerStarAdjunction A b').homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [Adjunction.counit_naturality, derivedUpperStar_map_derivedBaseChangeMap_app_counit_assoc]
  erw [derivedUpperStar_map_derivedBaseChangeMap_app_counit]
  have n₃ := (derivedSquareUpperStarIso A S3).hom.naturality ((derivedBaseChangeMap A S1).app M)
  have n₅ := (derivedSquareUpperStarIso A S5).inv.naturality
    ((derivedUpperStarLowerStarAdjunction A p).counit.app M)
  have n₄ := (derivedSquareUpperStarIso A S4).hom.naturality ((derivedBaseChangeMap A S2).app M)
  dsimp at n₃ n₅ n₄ ⊢
  rw [reassoc_of% n₃, ← Functor.map_comp_assoc (L((h)^*[A])),
    derivedUpperStar_map_derivedBaseChangeMap_app_counit, Functor.map_comp_assoc, n₅,
    reassoc_of% n₄, ← Functor.map_comp (L((a')^*[A]))]
  rw [derivedUpperStar_map_derivedBaseChangeMap_app_counit A S2 M, Functor.map_comp]
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc]
  exact derivedSquareUpperStarIso_cube A S1 S2 S3 S4 S0 S5 _

section Paste

variable {W₀ X₀ : Scheme.{u}} {h₀ : W₀ ⟶ W} {b₀ : W₀ ⟶ X₀} {v : X₀ ⟶ X} {a₀ : W₀ ⟶ Z}
  {e₀ : X₀ ⟶ Y}

/-- **Coherence of the square isomorphisms of two stacked squares**: the square isomorphism of
the composite of two squares is the composite of their square isomorphisms and of the
composition isomorphisms. -/
lemma derivedSquareUpperStarIso_paste (S1 : CommSq a b p e) (S3 : CommSq h₀ b₀ b v)
    (S13 : CommSq a₀ b₀ p e₀) (ha : a₀ = h₀ ≫ a) (he : e₀ = v ≫ e)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((b₀)^*[A]).map ((leftDerivedUpperStarComp A v e e₀ he).hom.app K) ≫
        (derivedSquareUpperStarIso A S3).hom.app (L((e)^*[A]).obj K) ≫
        L((h₀)^*[A]).map ((derivedSquareUpperStarIso A S1).hom.app K) ≫
        (leftDerivedUpperStarComp A h₀ a a₀ ha).inv.app (L((p)^*[A]).obj K) =
      (derivedSquareUpperStarIso A S13).hom.app K := by
  have hm : h₀ ≫ b = b₀ ≫ v := S3.w
  have hn : a ≫ p = b ≫ e := S1.w
  have ht₁ : a₀ ≫ p = (b₀ ≫ v) ≫ e := by rw [S13.w, he, Category.assoc]
  have ht₂ : a₀ ≫ p = (h₀ ≫ b) ≫ e := by rw [ht₁, hm]
  have ht₃ : a₀ ≫ p = h₀ ≫ (a ≫ p) := by rw [ha, Category.assoc]
  rw [← cancel_epi ((leftDerivedUpperStarComp A b₀ e₀ (a₀ ≫ p) S13.w).hom.app K)]
  simp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [leftDerivedUpperStarComp_assoc'_app_assoc A b₀ v e (h₀ ≫ b) e₀ (a₀ ≫ p) hm he ht₂,
    Iso.hom_inv_id_app_assoc,
    ← leftDerivedUpperStarComp_assoc'_app_assoc A h₀ b e (h₀ ≫ b) (a ≫ p) (a₀ ≫ p) rfl hn ht₂,
    ← Functor.map_comp_assoc (L((h₀)^*[A])), Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [leftDerivedUpperStarComp_assoc'_app_assoc A h₀ a p a₀ (a ≫ p) (a₀ ≫ p) ha rfl rfl,
    Iso.hom_inv_id_app]
  erw [Category.comp_id]

-- the derived functors involved are large terms
/-- **The derived base change maps of two stacked squares paste**: the derived base change map
`Ex_*` of the composite of two squares `W₀ ⟶ W ⟶ Z` over `X₀ ⟶ X ⟶ Y` is `Lv^*` of the one of
the right square followed by the one of the left square, up to composition isomorphisms. -/
theorem derivedBaseChangeMap_paste (S1 : CommSq a b p e) (S3 : CommSq h₀ b₀ b v)
    (S13 : CommSq a₀ b₀ p e₀) (ha : a₀ = h₀ ≫ a) (he : e₀ = v ≫ e)
    (M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A v e e₀ he).hom.app (R((p)_*[A]).obj M) ≫
        L((v)^*[A]).map ((derivedBaseChangeMap A S1).app M) ≫
        (derivedBaseChangeMap A S3).app (L((a)^*[A]).obj M) ≫
        R((b₀)_*[A]).map ((leftDerivedUpperStarComp A h₀ a a₀ ha).inv.app M) =
      (derivedBaseChangeMap A S13).app M := by
  apply ((derivedUpperStarLowerStarAdjunction A b₀).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [Adjunction.counit_naturality, derivedUpperStar_map_derivedBaseChangeMap_app_counit_assoc,
    derivedUpperStar_map_derivedBaseChangeMap_app_counit]
  have n₃ := (derivedSquareUpperStarIso A S3).hom.naturality ((derivedBaseChangeMap A S1).app M)
  have n₅ := (leftDerivedUpperStarComp A h₀ a a₀ ha).inv.naturality
    ((derivedUpperStarLowerStarAdjunction A p).counit.app M)
  dsimp at n₃ n₅ ⊢
  rw [reassoc_of% n₃, ← Functor.map_comp_assoc (L((h₀)^*[A])),
    derivedUpperStar_map_derivedBaseChangeMap_app_counit, Functor.map_comp_assoc, n₅]
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc]
  exact derivedSquareUpperStarIso_paste A S1 S3 S13 ha he _

end Paste

end Etale

end AlgebraicGeometry
