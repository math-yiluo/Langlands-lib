/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TateTwist.RootsOfUnity
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleRootsOfUnity
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# Pullback of the sheaves of roots of unity along weakly étale maps

The presheaf `U ↦ μ_N(Γ(U, 𝒪_U))` on the small pro-étale site is already a sheaf: it is
isomorphic to the underlying presheaf of `AlgebraicGeometry.Scheme.ProEt.rootsOfUnitySheaf`,
the kernel of `N` on `𝔾ₘ`. Hence `μ_N = AlgebraicGeometry.ProEtale.rootsOfUnitySheaf X N` is
the sheaf `U ↦ μ_N(Γ(U, 𝒪_U))` itself. For a weakly étale `g : U ⟶ X` the pullback `g^*` is
computed by restriction along the localization functor, under which `U ↦ μ_N(Γ(U, 𝒪_U))`
restricts to the same presheaf on `U_proét`. This gives `g^* μ_N ≅ μ_N`, compatibly with the
power maps.

## Main definitions

- `AlgebraicGeometry.ProEtale.rootsOfUnitySheafIso`: `μ_N` is isomorphic to the sheaf
  `U ↦ μ_N(Γ(U, 𝒪_U))` (no sheafification needed).
- `AlgebraicGeometry.ProEtale.upperStarRootsOfUnitySheafIso`: `g^* μ_N ≅ μ_N` for `g` weakly
  étale.

## Main statements

- `AlgebraicGeometry.ProEtale.upperStar_map_rootsOfUnitySheafPow_comp`: this isomorphism is
  compatible with the power maps `μ_{m N} ⟶ μ_N`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- Restriction of a section of `μ_N` along `h : W ⟶ V` is pullback of functions along `h`. -/
lemma rootsOfUnitySheafSectionsEquiv_map_val (X : Scheme.{u}) (N : ℕ) {V W : X.ProEt}
    (h : W ⟶ V) (y : (Scheme.ProEt.rootsOfUnitySheaf X N).obj.obj (op V)) :
    (((Additive.toMul (Scheme.ProEt.rootsOfUnitySheafSectionsEquiv X N W
      ((Scheme.ProEt.rootsOfUnitySheaf X N).obj.map h.op y)) : rootsOfUnity N Γ(W.left, ⊤)) :
        Γ(W.left, ⊤)ˣ) : Γ(W.left, ⊤)) =
      h.left.appTop (((Additive.toMul (Scheme.ProEt.rootsOfUnitySheafSectionsEquiv X N V y) :
        rootsOfUnity N Γ(V.left, ⊤)) : Γ(V.left, ⊤)ˣ) : Γ(V.left, ⊤)) := by
  rw [Scheme.ProEt.rootsOfUnitySheafSectionsEquiv_apply,
    Scheme.ProEt.rootsOfUnitySheafSectionsEquiv_apply]
  exact (congrArg (fun z ↦ ((Additive.toMul z.down : Γ(W.left, ⊤)ˣ) : Γ(W.left, ⊤)))
    (NatTrans.naturality_apply (kernel.ι (N • 𝟙 (Scheme.ProEt.gmSheaf X))).hom h.op y)).trans
      (Scheme.ProEt.gmPresheaf_map_apply X h _)

/-- The presheaf `U ↦ μ_N(Γ(U, 𝒪_U))` is isomorphic to the underlying presheaf of the kernel
of `N` on `𝔾ₘ`, by `AlgebraicGeometry.Scheme.ProEt.rootsOfUnitySheafSectionsEquiv`. -/
noncomputable def rootsOfUnityPresheafIsoKernel (X : Scheme.{u}) (N : ℕ) :
    rootsOfUnityPresheaf X N ≅ (Scheme.ProEt.rootsOfUnitySheaf X N).obj :=
  NatIso.ofComponents (fun V ↦ (AddEquiv.ulift.trans
      (Scheme.ProEt.rootsOfUnitySheafSectionsEquiv X N V.unop).symm).toAddCommGrpIso) (by
    intro V W h
    ext x
    apply (Scheme.ProEt.rootsOfUnitySheafSectionsEquiv X N W.unop).injective
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    refine Eq.trans ?_ (rootsOfUnitySheafSectionsEquiv_map_val X N h.unop _).symm
    simp only [AddEquiv.toAddCommGrpIso_hom, AddCommGrpCat.hom_ofHom, AddEquiv.coe_toAddMonoidHom,
      AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
    rfl)

/-- The presheaf `U ↦ μ_N(Γ(U, 𝒪_U))` is a sheaf for the pro-étale topology. -/
lemma isSheaf_rootsOfUnityPresheaf (X : Scheme.{u}) (N : ℕ) :
    Presheaf.IsSheaf (ProEt.topology X) (rootsOfUnityPresheaf X N) :=
  (Presheaf.isSheaf_of_iso_iff (rootsOfUnityPresheafIsoKernel X N)).2
    (Scheme.ProEt.rootsOfUnitySheaf X N).property

/-- The `m`-th power map `μ_{m N} ⟶ μ_N` between the sheaves `U ↦ μ_N(Γ(U, 𝒪_U))`, before
sheafification. -/
noncomputable def rootsOfUnityPresheafPow (X : Scheme.{u}) (N m : ℕ) :
    rootsOfUnityPresheaf X (m * N) ⟶ rootsOfUnityPresheaf X N :=
  Functor.whiskerLeft ((ProEt.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ)
    (CommRingCat.rootsOfUnityPow N m)

/-- `AlgebraicGeometry.ProEtale.rootsOfUnitySheafPow` is the sheafification of
`AlgebraicGeometry.ProEtale.rootsOfUnityPresheafPow`. -/
lemma rootsOfUnitySheafPow_eq (X : Scheme.{u}) (N m : ℕ) :
    rootsOfUnitySheafPow X N m =
      (presheafToSheaf (ProEt.topology X) Ab.{u + 1}).map (rootsOfUnityPresheafPow X N m) :=
  rfl

/-- `μ_N` is the sheaf `U ↦ μ_N(Γ(U, 𝒪_U))`: sheafification does not change it. -/
noncomputable def rootsOfUnitySheafIso (X : Scheme.{u}) (N : ℕ) :
    rootsOfUnitySheaf X N ≅ ⟨rootsOfUnityPresheaf X N, isSheaf_rootsOfUnityPresheaf X N⟩ :=
  (sheafificationIso ⟨rootsOfUnityPresheaf X N, isSheaf_rootsOfUnityPresheaf X N⟩).symm

/-- The power maps on `μ_N` correspond to the power maps on `U ↦ μ_N(Γ(U, 𝒪_U))` under
`AlgebraicGeometry.ProEtale.rootsOfUnitySheafIso`. -/
@[reassoc]
lemma rootsOfUnitySheafIso_inv_comp_rootsOfUnitySheafPow (X : Scheme.{u}) (N m : ℕ) :
    (rootsOfUnitySheafIso X (m * N)).inv ≫ rootsOfUnitySheafPow X N m =
      ObjectProperty.homMk (rootsOfUnityPresheafPow X N m) ≫ (rootsOfUnitySheafIso X N).inv :=
  Sheaf.hom_ext (toSheafify_naturality _ _).symm

/-- The power maps on `μ_N` correspond to the power maps on `U ↦ μ_N(Γ(U, 𝒪_U))` under
`AlgebraicGeometry.ProEtale.rootsOfUnitySheafIso`. -/
@[reassoc]
lemma rootsOfUnitySheafPow_comp_rootsOfUnitySheafIso_hom (X : Scheme.{u}) (N m : ℕ) :
    rootsOfUnitySheafPow X N m ≫ (rootsOfUnitySheafIso X N).hom =
      (rootsOfUnitySheafIso X (m * N)).hom ≫
        ObjectProperty.homMk (rootsOfUnityPresheafPow X N m) := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv,
    rootsOfUnitySheafIso_inv_comp_rootsOfUnitySheafPow]

/-- For a weakly étale `g : U ⟶ X`, the restriction of `U ↦ μ_N(Γ(U, 𝒪_U))` along the
localization functor `U_proét ⥤ X_proét` is `U ↦ μ_N(Γ(U, 𝒪_U))` on `U_proét`. -/
noncomputable def localizationRestrictionRootsOfUnityIso {U X : Scheme.{u}} (g : U ⟶ X)
    [WeaklyEtale g] (N : ℕ) :
    (localizationRestriction Ab.{u + 1} g inferInstance).obj
        ⟨rootsOfUnityPresheaf X N, isSheaf_rootsOfUnityPresheaf X N⟩ ≅
      ⟨rootsOfUnityPresheaf U N, isSheaf_rootsOfUnityPresheaf U N⟩ :=
  ObjectProperty.isoMk _ (Iso.refl _)

/-- `AlgebraicGeometry.ProEtale.localizationRestrictionRootsOfUnityIso` is compatible with the
power maps. -/
@[reassoc]
lemma localizationRestriction_map_rootsOfUnityPresheafPow {U X : Scheme.{u}} (g : U ⟶ X)
    [WeaklyEtale g] (N m : ℕ) :
    (localizationRestriction Ab.{u + 1} g inferInstance).map
        (ObjectProperty.homMk (rootsOfUnityPresheafPow X N m)) ≫
      (localizationRestrictionRootsOfUnityIso g N).hom =
      (localizationRestrictionRootsOfUnityIso g (m * N)).hom ≫
        ObjectProperty.homMk (rootsOfUnityPresheafPow U N m) :=
  rfl

/-- For a weakly étale `g : U ⟶ X`, the pullback of `μ_N` on `X_proét` is `μ_N` on `U_proét`:
`g^*` is restriction along the localization functor
(`AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction`), and `μ_N` is the sheaf
`U ↦ μ_N(Γ(U, 𝒪_U))` (`AlgebraicGeometry.ProEtale.rootsOfUnitySheafIso`). -/
noncomputable def upperStarRootsOfUnitySheafIso {U X : Scheme.{u}} (g : U ⟶ X) [WeaklyEtale g]
    (N : ℕ) : (g)^*[Ab.{u + 1}].obj (rootsOfUnitySheaf X N) ≅ rootsOfUnitySheaf U N :=
  (g)^*[Ab.{u + 1}].mapIso (rootsOfUnitySheafIso X N) ≪≫
    (upperStarIsoLocalizationRestriction Ab.{u + 1} g inferInstance).app _ ≪≫
      localizationRestrictionRootsOfUnityIso g N ≪≫ (rootsOfUnitySheafIso U N).symm

/-- The isomorphism `g^* μ_N ≅ μ_N` is compatible with the power maps `μ_{m N} ⟶ μ_N`. -/
lemma upperStar_map_rootsOfUnitySheafPow_comp {U X : Scheme.{u}} (g : U ⟶ X) [WeaklyEtale g]
    (N m : ℕ) :
    (g)^*[Ab.{u + 1}].map (rootsOfUnitySheafPow X N m) ≫ (upperStarRootsOfUnitySheafIso g N).hom =
      (upperStarRootsOfUnitySheafIso g (m * N)).hom ≫ rootsOfUnitySheafPow U N m := by
  simp only [upperStarRootsOfUnitySheafIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, rootsOfUnitySheafPow_comp_rootsOfUnitySheafIso_hom,
    Functor.map_comp_assoc, NatTrans.naturality_assoc,
    localizationRestriction_map_rootsOfUnityPresheafPow_assoc,
    rootsOfUnitySheafIso_inv_comp_rootsOfUnitySheafPow]

end AlgebraicGeometry.ProEtale
