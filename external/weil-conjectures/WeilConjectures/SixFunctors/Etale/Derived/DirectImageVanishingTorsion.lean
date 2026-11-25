/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologicalDimension
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.TStructure
public import
  WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomPresheaf
public import WeilConjectures.SixFunctors.Etale.Derived.HigherDirectImageAffine

/-!
# Vanishing of the higher direct images above twice the dimension, torsion coefficients

Let `k` be a separably closed field, `f : X ⟶ Y` a quasi-compact morphism locally of finite type
between `k`-schemes locally of finite type, with `dim X ≤ d`, and `Λ` a ring which is torsion as
an additive group. Then `R^q f_* M = 0` for every `q > 2d` and every étale sheaf `M` of
`Λ`-modules on `X` (`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_two_mul_lt`).

This generalises `AlgebraicGeometry.Etale.hasUniformDirectImageVanishingLE_two_mul` of
`WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing`, which is stated for a finite
ring `Λ`. Unlike that file, this file does not depend on the proper base change theorem, so that
it can be used in the proof of its unbounded version.

The argument of `WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing` is run for an
arbitrary coefficient ring whose injective sheaves have acyclic underlying abelian sheaves
(`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_two_mul_lt_of_acyclic`). This holds for
`ULift ℤ`, whose sheaves of modules are just abelian sheaves
(`AlgebraicGeometry.Etale.subsingleton_H_forget₂_uliftInt_of_injective`). A general torsion
ring `Λ` is reduced to `ULift ℤ` by restriction of scalars, which commutes with the derived direct
images (`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarRestrictScalars`).

## Main statements

- `AlgebraicGeometry.Etale.subsingleton_ext_freeSheaf_of_subsingleton_H_of_acyclic`: the
  cohomology of a sheaf of `Λ`-modules over an étale `X`-scheme `V` vanishes in a degree where
  the abelian cohomology of its underlying abelian sheaf restricted to `V` does, provided that
  injective sheaves of `Λ`-modules on `V` have acyclic underlying abelian sheaves.
- `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_forall_isAffine` (in
  `WeilConjectures.SixFunctors.Etale.Derived.HigherDirectImageAffine`):
  `R^q h_* K = 0` as soon as `H^q(W ×_X Y, K|) = 0` for every affine `W` étale over `X`.
- `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_two_mul_lt`: the vanishing of `R^q f_*`
  above twice the dimension, for a torsion coefficient ring.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **Cohomology of sheaves of `Λ`-modules versus abelian sheaf cohomology.** Let `V` be an étale
`X`-scheme such that the underlying abelian sheaves of injective sheaves of `Λ`-modules on `V`
are acyclic, and `F` an étale sheaf of `Λ`-modules on `X`. If the underlying abelian sheaf of the
restriction of `F` to `V` has no cohomology in degree `n + 1`, then `Ext^{n + 1}(Λ[V], F) = 0`,
that is `H^{n + 1}(V, F|) = 0` computed with sheaves of `Λ`-modules.

This generalises `AlgebraicGeometry.Etale.subsingleton_ext_freeSheaf_of_subsingleton_H`, which
assumes `Λ` finite, the acyclicity then being
`CategoryTheory.Sheaf.subsingleton_H_forget₂_of_injective`. The proof is dimension shifting
(`CategoryTheory.Abelian.Ext.subsingleton_of_subsingleton_map`); in degree one both groups
measure the failure of sections over `V` to lift. -/
theorem Etale.subsingleton_ext_freeSheaf_of_subsingleton_H_of_acyclic {X : Scheme.{u}}
    (V : X.Etale) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ)
    (hI : ∀ (I : Sheaf V.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective I] (m : ℕ),
      Subsingleton (Sheaf.H ((sheafCompose V.left.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj I) (m + 1)))
    (hF : Subsingleton (Sheaf.H ((sheafCompose V.left.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((V.hom)^*[ModuleCat.{u + 1} Λ].obj F)) (n + 1))) :
    Subsingleton (Abelian.Ext.{u + 1} ((Etale.freeSheaf Λ X).obj V) F (n + 1)) := by
  have hV : AlgebraicGeometry.Etale V.hom := V.prop
  let Φ := (V.hom)^*[ModuleCat.{u + 1} Λ] ⋙ sheafCompose V.left.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  refine Abelian.Ext.subsingleton_of_subsingleton_map Φ
    (fun S hS ↦ Etale.shortExact_map_forget₂ Λ
      (hS.map_of_exact ((V.hom)^*[ModuleCat.{u + 1} Λ]))) _
    ((constantSheaf _ AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))) ?_ ?_ n F hF
  · intro I _ n
    have := Etale.injective_upperStar_obj_of_etale Λ V.hom I
    exact hI _ n
  · intro S hS _ h₁
    change Subsingleton (Sheaf.H ((sheafCompose V.left.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((V.hom)^*[ModuleCat.{u + 1} Λ].obj S.X₁)) 1) at h₁
    have : Subsingleton (Sheaf.H ((V.hom)^*[AddCommGrpCat.{u + 1}].obj
        (S.map (sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))).X₁) 1) :=
      @Function.Injective.subsingleton _ _ _
        (Etale.injective_sheafHMap_of_isIso (Etale.upperStarForget₂Iso V S.X₁).hom 1) h₁
    have hsurj := Etale.surjective_app_of_subsingleton_H_one (X := X)
      (S := S.map (sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})))
      (Etale.shortExact_map_forget₂ Λ hS) V
    intro g
    obtain ⟨x, hx⟩ := hsurj (Etale.freeSheafHomEquiv Λ V S.X₃ g)
    refine ⟨(Etale.freeSheafHomEquiv Λ V S.X₂).symm x, ?_⟩
    apply (Etale.freeSheafHomEquiv Λ V S.X₃).injective
    rw [Etale.freeSheafHomEquiv_comp, Equiv.apply_symm_apply]
    exact hx

/-- **Vanishing of the higher direct images above twice the dimension, arbitrary target.** Let
`k` be a separably closed field, `X` a `k`-scheme locally of finite type with `dim X ≤ d`, and
`f : X ⟶ Y` a quasi-compact morphism to an arbitrary scheme `Y`. Let `Λ` be a coefficient ring
such that, for every étale `X`-scheme `V`, the underlying abelian sheaves of injective sheaves of
`Λ`-modules on `V` are acyclic. Then `R^q f_* M = 0` for every `q > 2d` and every étale sheaf `M`
of `Λ`-modules on `X` whose restrictions to étale `X`-schemes are torsion.

For an affine étale `W ⟶ Y`, the scheme `W ×_Y X` is quasi-compact, of finite type over `k` and
étale over `X`, hence of dimension at most `d`, so its torsion cohomology vanishes above `2d`
(`AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_lt_of_isSepClosed`); and `R^q f_* M` is the
sheafification of these groups. -/
theorem Etale.isZero_higherDirectImage_of_two_mul_lt_of_acyclic_of_quasiCompact {k : Type u}
    [Field k] [IsSepClosed k] {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] (d : ℕ)
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (hI : ∀ (V : X.Etale) (I : Sheaf V.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      [Injective I] (m : ℕ), Subsingleton (Sheaf.H ((sheafCompose V.left.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj I) (m + 1)))
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hM : ∀ V : X.Etale, ((sheafCompose V.left.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((V.hom)^*[ModuleCat.{u + 1} Λ].obj M)).IsTorsion)
    (q : ℤ) (hq : (2 * d : ℤ) < q) :
    IsZero (Etale.higherDirectImage Λ f q M) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = ((n + 1 : ℕ) : ℤ) := ⟨(q - 1).toNat, by omega⟩
  refine Etale.isZero_higherDirectImage_of_forall_isAffine f _ M fun W hW ↦ ?_
  let V := (MorphismProperty.Over.pullback @Etale ⊤ f).obj W
  have hV : AlgebraicGeometry.Etale V.hom := V.prop
  -- the cohomology of the restriction of `M` to `V = W ×_Y X` vanishes above `2d`
  have hcd : Subsingleton (Sheaf.H ((sheafCompose V.left.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((V.hom)^*[ModuleCat.{u + 1} Λ].obj M)) (n + 1)) := by
    have : CompactSpace ((𝟭 Scheme.{u}).obj W.left) := by
      change CompactSpace W.left
      infer_instance
    have : CompactSpace ((𝟭 Scheme.{u}).obj V.left) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.fst W.hom f)
    have : QuasiCompact (V.hom ≫ aX) :=
      (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).2 inferInstance
    exact Scheme.subsingleton_H_of_two_mul_lt_of_isSepClosed d (V.hom ≫ aX)
      ((V.hom.topologicalKrullDim_le_of_etale).trans hX) _ (hM V) (n + 1) (by omega)
  have : Subsingleton (Abelian.Ext.{u + 1} ((Etale.freeSheaf Λ X).obj V) M (n + 1)) :=
    Etale.subsingleton_ext_freeSheaf_of_subsingleton_H_of_acyclic V M n (hI V) hcd
  exact ((DerivedCategory.Plus.singleFunctorHomEquivExt.{u + 1}
    ((f)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ Y).obj W)) M (n + 1)).trans
    (Abelian.Ext.precompAddEquiv (Etale.upperStarFreeSheafIso Λ f W) M (n + 1)).symm.toEquiv
    ).subsingleton

/-- **Vanishing of the higher direct images above twice the dimension.** Let `k` be a separably
closed field, `f : X ⟶ Y` a quasi-compact morphism locally of finite type between `k`-schemes
locally of finite type with `dim X ≤ d`, and `Λ` a coefficient ring such that, for every étale
`X`-scheme `V`, the underlying abelian sheaves of injective sheaves of `Λ`-modules on `V` are
acyclic. Then `R^q f_* M = 0` for every `q > 2d` and every étale sheaf `M` of `Λ`-modules on `X`
whose restrictions to étale `X`-schemes are torsion.

This is `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_two_mul_lt_of_acyclic_of_quasiCompact`,
as `X` is locally of finite type over `k`. -/
theorem Etale.isZero_higherDirectImage_of_two_mul_lt_of_acyclic {k : Type u}
    [Field k] [IsSepClosed k] {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [QuasiCompact f] (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY]
    (hf : f ≫ aY = aX) (d : ℕ) (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (hI : ∀ (V : X.Etale) (I : Sheaf V.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      [Injective I] (m : ℕ), Subsingleton (Sheaf.H ((sheafCompose V.left.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj I) (m + 1)))
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hM : ∀ V : X.Etale, ((sheafCompose V.left.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((V.hom)^*[ModuleCat.{u + 1} Λ].obj M)).IsTorsion)
    (q : ℤ) (hq : (2 * d : ℤ) < q) :
    IsZero (Etale.higherDirectImage Λ f q M) := by
  have : LocallyOfFiniteType aX := hf ▸ inferInstance
  exact Etale.isZero_higherDirectImage_of_two_mul_lt_of_acyclic_of_quasiCompact f aX d hX hI M hM q
    hq

/-- **Injective sheaves of `ULift ℤ`-modules are acyclic.** The underlying abelian sheaf of an
injective étale sheaf of `ULift ℤ`-modules is injective, taking underlying abelian sheaves being
an equivalence (`AlgebraicGeometry.Etale.isEquivalence_sheafCompose_forget₂_uliftInt`), hence it
has no cohomology in positive degrees. -/
theorem Etale.subsingleton_H_forget₂_uliftInt_of_injective {X : Scheme.{u}}
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) [Injective I]
    (n : ℕ) :
    Subsingleton (Sheaf.H ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj I) (n + 1)) := by
  have : Injective ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj I) :=
    Functor.PreservesInjectiveObjects.injective_obj inferInstance
  exact ⟨fun a b ↦ (Abelian.Ext.eq_zero_of_injective a).trans
    (Abelian.Ext.eq_zero_of_injective b).symm⟩

/-- Being torsion is invariant under isomorphisms of abelian sheaves. -/
lemma _root_.CategoryTheory.Sheaf.IsTorsion.of_iso {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G)
    (hF : F.IsTorsion) : G.IsTorsion := by
  intro U s
  obtain ⟨S, hS, h⟩ := hF (e.inv.hom.app U s)
  refine ⟨S, hS, fun V g hg ↦ ?_⟩
  have h₁ := AddMonoidHom.isOfFinAddOrder (e.hom.hom.app (op V)).hom (h hg)
  have h₂ := ConcreteCategory.congr_hom (e.hom.hom.naturality g.op) (e.inv.hom.app U s)
  have h₃ : e.hom.hom.app U (e.inv.hom.app U s) = s :=
    ConcreteCategory.congr_hom (congr_app (congrArg (fun a ↦ a.hom) e.inv_hom_id) U) s
  simp only [ConcreteCategory.comp_apply, h₃] at h₂
  rw [← h₂]
  exact h₁

/-- The ring homomorphism `ULift ℤ →+* Λ`. -/
noncomputable def Etale.uliftIntRingHom (Λ : Type (u + 1)) [CommRing Λ] :
    ULift.{u + 1} ℤ →+* Λ :=
  (Int.castRingHom Λ).comp ULift.ringEquiv.toRingHom

/-- Restriction of scalars along `ULift ℤ →+* Λ` commutes with the higher direct images. -/
noncomputable def Etale.restrictScalarsHigherDirectImageIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (q : ℤ) (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Sheaf.restrictScalars Y.smallEtaleTopology (Etale.uliftIntRingHom Λ)).obj
        (Etale.higherDirectImage Λ f q M) ≅
      Etale.higherDirectImage (ULift.{u + 1} ℤ) f q
        ((Sheaf.restrictScalars X.smallEtaleTopology (Etale.uliftIntRingHom Λ)).obj M) :=
  ((Sheaf.restrictScalars Y.smallEtaleTopology
      (Etale.uliftIntRingHom Λ)).mapDerivedCategoryPlusHomologyFunctorIso q).app
      ((f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M)) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (asIso ((Etale.rightDerivedLowerStarRestrictScalars (Etale.uliftIntRingHom Λ) f).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M))) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} ℤ)].rightDerivedFunctorPlus.mapIso
        (((Sheaf.restrictScalars X.smallEtaleTopology
          (Etale.uliftIntRingHom Λ)).mapDerivedCategoryPlusSingleFunctor 0).app M))

/-- **Vanishing of the higher direct images above twice the dimension, torsion coefficients.**
Let `k` be a separably closed field, `X` a `k`-scheme locally of finite type with `dim X ≤ d`,
`f : X ⟶ Y` a quasi-compact morphism to an arbitrary scheme `Y`, and `Λ` a ring which is torsion
as an additive group. Then `R^q f_* M = 0` for every `q > 2d` and every étale sheaf `M` of
`Λ`-modules on `X`.

This generalises `AlgebraicGeometry.Etale.hasUniformDirectImageVanishingLE_two_mul`, which
assumes `Λ` finite. By restriction of scalars to `ULift ℤ`
(`AlgebraicGeometry.Etale.restrictScalarsHigherDirectImageIso`), which is faithful, this follows
from the case of `ULift ℤ`-coefficients
(`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_two_mul_lt_of_acyclic_of_quasiCompact`), in
which injective sheaves are acyclic
(`AlgebraicGeometry.Etale.subsingleton_H_forget₂_uliftInt_of_injective`)
and the sheaves considered are killed by the additive order of `1 : Λ`. -/
theorem Etale.isZero_higherDirectImage_of_quasiCompact_of_two_mul_lt (hΛ : IsAddTorsion Λ)
    {k : Type u} [Field k] [IsSepClosed k] {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] (d : ℕ)
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (hq : (2 * d : ℤ) < q) :
    IsZero (Etale.higherDirectImage Λ f q M) := by
  let φ := Etale.uliftIntRingHom Λ
  obtain ⟨m, hm, hm1⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (hΛ (1 : Λ))
  have hz := Etale.isZero_higherDirectImage_of_two_mul_lt_of_acyclic_of_quasiCompact f aX d hX
    (fun V I _ n ↦ Etale.subsingleton_H_forget₂_uliftInt_of_injective I n)
    ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M) (fun V ↦ ?_) q hq
  · have hz' := IsZero.of_iso hz (Etale.restrictScalarsHigherDirectImageIso f q M)
    rw [IsZero.iff_id_eq_zero] at hz' ⊢
    refine (Sheaf.restrictScalars Y.smallEtaleTopology φ).map_injective ?_
    rw [CategoryTheory.Functor.map_id, Functor.map_zero]
    exact hz'
  · refine Sheaf.IsTorsion.of_iso ((sheafCompose V.left.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).mapIso
        (asIso ((Etale.upperStarRestrictScalars φ V.hom).app M)).symm) ?_
    refine Sheaf.IsTorsion.of_forall_isAddTorsion fun U x ↦ ?_
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨m, hm, ?_⟩
    let y : ((V.hom)^*[ModuleCat.{u + 1} Λ].obj M).obj.obj U := x
    change m • y = 0
    rw [← one_smul Λ y, ← smul_assoc, hm1, zero_smul]

/-- **Vanishing of the higher direct images above twice the dimension, torsion coefficients.**
Let `k` be a separably closed field, `f : X ⟶ Y` a quasi-compact morphism locally of finite type
between `k`-schemes locally of finite type with `dim X ≤ d`, and `Λ` a ring which is torsion as
an additive group. Then `R^q f_* M = 0` for every `q > 2d` and every étale sheaf `M` of
`Λ`-modules on `X`.

This is `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_quasiCompact_of_two_mul_lt`, as `X`
is locally of finite type over `k`. -/
theorem Etale.isZero_higherDirectImage_of_two_mul_lt (hΛ : IsAddTorsion Λ) {k : Type u}
    [Field k] [IsSepClosed k] {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [QuasiCompact f] (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY]
    (hf : f ≫ aY = aX) (d : ℕ) (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (hq : (2 * d : ℤ) < q) :
    IsZero (Etale.higherDirectImage Λ f q M) := by
  have : LocallyOfFiniteType aX := hf ▸ inferInstance
  exact Etale.isZero_higherDirectImage_of_quasiCompact_of_two_mul_lt hΛ f aX d hX M q hq

end AlgebraicGeometry
