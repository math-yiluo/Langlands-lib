/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal

/-!

# The pullback `g^*` is symmetric monoidal, and `g^* ⊣ g_*` is a monoidal adjunction

For a morphism of schemes `g : Z ⟶ Y` and a closed symmetric monoidal coefficient category
`A`, the pushforward `g_*` on `A`-valued pro-étale sheaves is lax symmetric monoidal
(`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal`). This file
records the structure on the other half of the adjunction `g^* ⊣ g_*`, which is what the
module-object six functors need in order to transport ring objects and module objects along
`g^*`:

* `ProEtale.oplaxMonoidal_upperStar`: `g^*` is oplax monoidal, being the left adjoint of the
  lax monoidal `g_*` (`Adjunction.leftAdjointOplaxMonoidal`). This is formal.
* `ProEtale.isIso_η_upperStar` and `ProEtale.isIso_δ_upperStar`: the oplax structure maps
  `g^* 𝟙 ⟶ 𝟙` and `g^* (F ⊗ G) ⟶ g^* F ⊗ g^* G` are isomorphisms, i.e. `g^*` is *strong*
  monoidal (`ProEtale.isIso_upperStar_η` and `ProEtale.isIso_upperStar_δ`).
* `ProEtale.monoidal_upperStar`: the resulting strong monoidal structure on `g^*`, and
  `ProEtale.isMonoidal_upperStarLowerStarAdjunction`: the adjunction `g^* ⊣ g_*` is a monoidal
  adjunction in the sense of mathlib (`Adjunction.IsMonoidal`), the lax structure of `g_*` and
  the oplax structure of `g^*` being mates.
* `ProEtale.laxBraided_upperStar`: `g^*` is moreover (lax) braided, which is deduced from the
  lax braidedness of `g_*` by the mate correspondence. In particular `g^*` sends commutative
  ring objects to commutative ring objects (`Functor.isCommMonObj_obj`).
* `ProEtale.isMonoidal_lowerStarComp`: the composition isomorphism `f_* ⋙ g_* ≅ (f ≫ g)_*` of
  `ProEtale.lowerStarComp` is monoidal. It is the composition isomorphism of pushforwards along
  the base change functors of the sites, which is monoidal for any continuous functors
  (`Functor.isMonoidal_sheafPushforwardContinuousComp'_hom`). It is the input making the
  composition isomorphism of pushforwards of module objects
  (`ProEtale.CondensedRing.lowerStarComp`) available.
* `ProEtale.isMonoidal_lowerStarId`: the identity isomorphism `(𝟙 X)_* ≅ 𝟭` of
  `ProEtale.lowerStarId` is monoidal. It is induced by the identification of the base change
  along `𝟙 X` with the identity of the site, which is compatible with the objectwise tensor
  products. It is the input making the identity isomorphism of pushforwards of module objects
  (`ProEtale.CondensedRing.lowerStarId`) available.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry

open Scheme ProEtale

/-! ### The strong monoidal structure on the pullback -/

section UpperStar

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The oplax unit `g^* 𝟙 ⟶ 𝟙` of the pullback on pro-étale sheaves is an isomorphism: the
pullback of the unit sheaf is the unit sheaf. See the module docstring. -/
instance ProEtale.isIso_η_upperStar : IsIso (η (g)^*[A]) := inferInstance

/-- The oplax structure maps `g^* (F ⊗ G) ⟶ g^* F ⊗ g^* G` of the pullback on pro-étale sheaves
are isomorphisms: the pullback commutes with the tensor product of sheaves. See the module
docstring. -/
instance ProEtale.isIso_δ_upperStar (F G : Sheaf (Scheme.ProEt.topology Y) A) :
    IsIso (δ (g)^*[A] F G) := inferInstance

/-- The pullback `g^*` on pro-étale sheaves is lax braided (hence braided, being strong
monoidal): the compatibility with the braiding is the mate of the one of `g_*`. When `A` is
symmetric, this says that `g^*` is symmetric monoidal. In particular `g^*` sends commutative
ring objects to commutative ring objects. -/
noncomputable instance ProEtale.laxBraided_upperStar : (g)^*[A].LaxBraided where
  braided F G := by
    have h : δ (g)^*[A] F G ≫ (β_ ((g)^*[A].obj F) ((g)^*[A].obj G)).hom =
        (g)^*[A].map (β_ F G).hom ≫ δ (g)^*[A] G F := by
      change ((ProEtale.upperStarLowerStarAdjunction A g).homEquiv _ _).symm
          (((ProEtale.upperStarLowerStarAdjunction A g).unit.app F ⊗ₘ
            (ProEtale.upperStarLowerStarAdjunction A g).unit.app G) ≫ μ (g)_*[A] _ _) ≫ _ =
        _ ≫ ((ProEtale.upperStarLowerStarAdjunction A g).homEquiv _ _).symm
          (((ProEtale.upperStarLowerStarAdjunction A g).unit.app G ⊗ₘ
            (ProEtale.upperStarLowerStarAdjunction A g).unit.app F) ≫ μ (g)_*[A] _ _)
      rw [← Adjunction.homEquiv_naturality_right_symm]
      erw [← Adjunction.homEquiv_naturality_left_symm]
      rw [Category.assoc, Functor.LaxBraided.braided]
      erw [BraidedCategory.braiding_naturality_assoc]
      rfl
    rw [← cancel_epi (δ (g)^*[A] F G), Functor.Monoidal.δ_μ_assoc, reassoc_of% h,
      Functor.Monoidal.δ_μ, Category.comp_id]

end UpperStar

/-! ### The composition isomorphism of pushforwards is monoidal -/

section LowerStarComp

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The composition isomorphism `f_* ⋙ g_* ≅ (f ≫ g)_*` of pushforwards on pro-étale sheaves is
a monoidal natural isomorphism, for the composite lax monoidal structure on `f_* ⋙ g_*`. See
the module docstring. -/
instance ProEtale.isMonoidal_lowerStarComp :
    NatTrans.IsMonoidal (ProEtale.lowerStarComp A f g).hom := by
  unfold ProEtale.lowerStarComp
  have := Scheme.ProEt.isContinuous_overPullback g
  have := Scheme.ProEt.isContinuous_overPullback f
  have := Scheme.ProEt.isContinuous_overPullback (f ≫ g)
  exact Functor.isMonoidal_sheafPushforwardContinuousComp'_hom (A := A)
    (J := Scheme.ProEt.topology Z) (K := Scheme.ProEt.topology Y) (L := Scheme.ProEt.topology X)
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).symm

end LowerStarComp

/-! ### The identity isomorphism of pushforwards is monoidal -/

section LowerStarId

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]

/-- The identity isomorphism `(𝟙 X)_* ≅ 𝟭` of pushforwards on pro-étale sheaves is a monoidal
natural isomorphism. See the module docstring. -/
instance ProEtale.isMonoidal_lowerStarId (X : Scheme.{u}) :
    NatTrans.IsMonoidal (ProEtale.lowerStarId A X).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (Functor.sheafPushforwardContinuousId'
    (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X) A (Scheme.ProEt.topology X)).hom)

end LowerStarId

end AlgebraicGeometry
