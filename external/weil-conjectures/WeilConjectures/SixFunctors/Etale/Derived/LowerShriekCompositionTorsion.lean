/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Completion
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.CoextendScalars
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek

/-!
# Proper base change modulo objects on which `ϖ` acts invertibly

Let `Λ` be a commutative ring and `ϖ ∈ Λ` a nonzerodivisor with `Λ ⧸ (ϖ)` finite (for instance
`Λ = 𝒪_E` and `ϖ` a uniformizer). Proper base change fails on `D(-_ét, Λ)`, but it holds up to
objects on which `ϖ` acts invertibly: for a cartesian square with `f` proper and `N` with
`Lg'^* N = 0`, the multiplication by `ϖ` on `Lg^* Rf_* N` is invertible
(`AlgebraicGeometry.Etale.isIso_smul_id_leftDerivedUpperStar_rightDerivedLowerStar`). The proof
passes to the finite ring `Λ ⧸ (ϖ)` through the derived coextension of scalars
`RHom_Λ(Λ ⧸ (ϖ), -)`, which commutes with `Rf_*` and detects the invertibility of `ϖ`.

Consequently the exchange map `Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*` of an extension by zero with a
proper direct image has cones on which `ϖ` acts invertibly
(`AlgebraicGeometry.Etale.isIso_smul_id_of_openImmersionLowerShriekLowerStarExchange`), so it
induces bijections on morphisms into objects killed by a power of `ϖ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

section Coextension

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Restriction of scalars of étale sheaves along a ring morphism reflects the vanishing of
objects of the derived categories. -/
lemma isZero_of_isZero_derivedRestrictScalars {Λ' : Type (u + 1)} [CommRing Λ']
    (φ : Λ →+* Λ') {X : Scheme.{u}} {Z : 𝐃(X, Λ')}
    (hZ : IsZero ((Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj Z)) : IsZero Z :=
  (_root_.DerivedCategory.isZero_iff _).2 fun n ↦
    (Sheaf.restrictScalars X.smallEtaleTopology
      φ).isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      (((_root_.DerivedCategory.homologyFunctor _ n).map_isZero hZ))

/-- Pullback commutes with restriction of scalars on the derived categories. -/
noncomputable def mapDerivedCategoryUpperStarDerivedRestrictScalarsIso {Λ' : Type (u + 1)}
    [CommRing Λ'] (φ : Λ →+* Λ') {X Y : Scheme.{u}} (g : X ⟶ Y) (Z : 𝐃(Y, Λ')) :
    D((g)^*[ModuleCat.{u + 1} Λ]).obj
        ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).obj Z) ≅
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj
        (D((g)^*[ModuleCat.{u + 1} Λ']).obj Z) :=
  (Functor.mapDerivedCategoryCompIso (Sheaf.restrictScalars Y.smallEtaleTopology φ)
      (g)^*[ModuleCat.{u + 1} Λ]).app Z ≪≫
    (Functor.mapDerivedCategoryNatIso (asIso (upperStarRestrictScalars φ g))).app Z ≪≫
    ((Functor.mapDerivedCategoryCompIso (g)^*[ModuleCat.{u + 1} Λ']
      (Sheaf.restrictScalars X.smallEtaleTopology φ)).app Z).symm

variable {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
include hϖ

/-- **The coextension triangle.** For a nonzerodivisor `ϖ` and `Y ∈ D(X_ét, Λ)` there is a
distinguished triangle `Res RHom_Λ(Λ ⧸ (ϖ), Y) ⟶ Y ⟶ Y ⟶ ...` whose second map is the
multiplication by `ϖ`. -/
theorem exists_distTriang_derivedRestrictScalars_rightDerivedCoextendScalars {X : Scheme.{u}}
    (Y : 𝐃(X, Λ)) :
    ∃ (a : (Sheaf.derivedRestrictScalars X.smallEtaleTopology
        (Ideal.Quotient.mk (Ideal.span {ϖ}))).obj
        ((coextendScalars (Ideal.Quotient.mk (Ideal.span {ϖ})) X).rightDerivedFunctor.obj Y) ⟶
          Y) (b : Y ⟶ ((Sheaf.derivedRestrictScalars X.smallEtaleTopology
        (Ideal.Quotient.mk (Ideal.span {ϖ}))).obj
        ((coextendScalars (Ideal.Quotient.mk (Ideal.span {ϖ})) X).rightDerivedFunctor.obj
          Y))⟦(1 : ℤ)⟧), Triangle.mk a (ϖ • 𝟙 Y) b ∈ distTriang _ := by
  let A := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let coext := coextendScalars (Ideal.Quotient.mk (Ideal.span {ϖ})) X
  let res := Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk (Ideal.span {ϖ}))
  let K := _root_.DerivedCategory.Q.objPreimage Y
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u + 1} A).obj K
  have hi := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1} A K).2
  have : QuasiIso ((CochainComplex.toKInjectiveResolution.{u + 1} A).app K) := hi
  let eC : Y ≅ _root_.DerivedCategory.Q.obj I :=
    (_root_.DerivedCategory.Q.objObjPreimageIso Y).symm ≪≫
      asIso (_root_.DerivedCategory.Q.map ((CochainComplex.toKInjectiveResolution.{u + 1} A).app K))
  have hu : IsIso (coext.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I)) :=
    inferInstance
  let ε : res.mapDerivedCategory.obj (coext.rightDerivedFunctor.obj Y) ≅
      _root_.DerivedCategory.Q.obj (coextendQuotientComplexShortComplex (ϖ := ϖ) I).X₁ :=
    res.mapDerivedCategory.mapIso (coext.rightDerivedFunctor.mapIso
        (eC ≪≫ ((_root_.DerivedCategory.quotientCompQhIso A).app I).symm) ≪≫
      (asIso (coext.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I))).symm ≪≫
      (_root_.DerivedCategory.quotientCompQhIso _).app _) ≪≫
    (res.mapDerivedCategoryFactors).app _
  let T := _root_.DerivedCategory.triangleOfSES
    (shortExact_coextendQuotientComplexShortComplex ϖ hϖ I)
  have hT : T ∈ distTriang _ := _root_.DerivedCategory.triangleOfSES_distinguished _
  have e : T.mor₂ = ϖ • 𝟙 (_root_.DerivedCategory.Q.obj I) := by
    change _root_.DerivedCategory.Q.map (ϖ • 𝟙 I) = _
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  refine ⟨ε.hom ≫ T.mor₁ ≫ eC.inv, eC.hom ≫ T.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map ε.inv,
    isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ ε eC eC ?_ ?_ ?_)⟩
  · simp
  · change (ϖ • 𝟙 Y) ≫ eC.hom = eC.hom ≫ T.mor₂
    rw [e, Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
  · simp only [Triangle.mk_mor₃, Category.assoc,
      ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]

/-- An exact `Λ`-linear functor kills `RHom_Λ(Λ ⧸ (ϖ), Y)` after restriction of scalars as
soon as it kills `Y`. -/
lemma isZero_map_derivedRestrictScalars_rightDerivedCoextendScalars {X X' : Scheme.{u}}
    (G : 𝐃(X, Λ) ⥤ 𝐃(X', Λ)) [G.CommShift ℤ] [G.IsTriangulated] (Y : 𝐃(X, Λ))
    (hY : IsZero (G.obj Y)) :
    IsZero (G.obj ((Sheaf.derivedRestrictScalars X.smallEtaleTopology
        (Ideal.Quotient.mk (Ideal.span {ϖ}))).obj
        ((coextendScalars (Ideal.Quotient.mk (Ideal.span {ϖ})) X).rightDerivedFunctor.obj Y))) := by
  obtain ⟨a, b, hT⟩ := exists_distTriang_derivedRestrictScalars_rightDerivedCoextendScalars hϖ Y
  exact (Triangle.isZero₁_iff_isIso₂ _ (G.map_distinguished _ hT)).2
    ⟨⟨hY.to_ _, hY.eq_of_src _ _, hY.eq_of_src _ _⟩⟩

variable [Finite (Λ ⧸ Ideal.span {ϖ})]

/-- **Proper base change up to `ϖ`-invertible objects.** For a cartesian square
`g' ≫ f = f' ≫ g` with `f` proper and `N ∈ D(X_ét, Λ)` with `g'^* N = 0`, the multiplication by
`ϖ` on `g^* Rf_* N` is invertible. With coefficients `Λ ⧸ (ϖ)` the object `g^* Rf_* N` itself
vanishes by proper base change, and the derived coextension `RHom_Λ(Λ ⧸ (ϖ), -)` commutes with
`Rf_*` (`AlgebraicGeometry.Etale.rightDerivedLowerStarCompCoextendScalarsIso`) and detects the
invertibility of `ϖ` through the coextension triangle. -/
theorem isIso_smul_id_mapDerivedCategoryUpperStar_rightDerivedLowerStar {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} [IsProper f]
    (sq : IsPullback g' f' f g) (N : 𝐃(X, Λ))
    (hN : IsZero (D((g')^*[ModuleCat.{u + 1} Λ]).obj N)) :
    IsIso (ϖ • 𝟙 (D((g)^*[ModuleCat.{u + 1} Λ]).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj N))) := by
  let φ := Ideal.Quotient.mk (Ideal.span {ϖ})
  let 𝔸 := ModuleCat.{u + 1} (Λ ⧸ Ideal.span {ϖ})
  -- the coextension of `N` dies after `g'^*`
  have h₁ : IsZero ((L((g')^*[𝔸])).obj ((coextendScalars φ X).rightDerivedFunctor.obj N)) := by
    refine IsZero.of_iso ?_ ((leftDerivedUpperStarIsoMapDerivedCategory _ g').app _)
    apply isZero_of_isZero_derivedRestrictScalars φ
    exact (isZero_map_derivedRestrictScalars_rightDerivedCoextendScalars hϖ _ N hN).of_iso
      (mapDerivedCategoryUpperStarDerivedRestrictScalarsIso φ g' _).symm
  -- hence the coextension of `Rf_* N` dies after `g^*`
  have hΛ : IsAddTorsion (Λ ⧸ Ideal.span {ϖ}) := isAddTorsion_of_finite
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring _ hΛ sq
  have h₂ : IsZero (D((g)^*[ModuleCat.{u + 1} Λ]).obj
      ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).obj
      ((coextendScalars φ Y).rightDerivedFunctor.obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj N)))) :=
    (((Sheaf.derivedRestrictScalars Y'.smallEtaleTopology φ).map_isZero
      ((R((f')_*[𝔸])).map_isZero h₁)).of_iso
        ((Sheaf.derivedRestrictScalars Y'.smallEtaleTopology φ).mapIso
          (asIso ((derivedBaseChangeMap 𝔸 sq.toCommSq).app _)))).of_iso
      (mapDerivedCategoryUpperStarDerivedRestrictScalarsIso φ g _ ≪≫
        (Sheaf.derivedRestrictScalars Y'.smallEtaleTopology φ).mapIso
          ((leftDerivedUpperStarIsoMapDerivedCategory _ g).app _).symm ≪≫
        (Sheaf.derivedRestrictScalars Y'.smallEtaleTopology φ).mapIso ((L((g)^*[𝔸])).mapIso
          ((rightDerivedLowerStarCompCoextendScalarsIso φ f).app N)))
  obtain ⟨a, b, hT⟩ := exists_distTriang_derivedRestrictScalars_rightDerivedCoextendScalars hϖ
    ((R((f)_*[ModuleCat.{u + 1} Λ])).obj N)
  have h₃ := (Triangle.isZero₁_iff_isIso₂ _
    (D((g)^*[ModuleCat.{u + 1} Λ]).map_distinguished _ hT)).1 h₂
  change IsIso (D((g)^*[ModuleCat.{u + 1} Λ]).map (ϖ • 𝟙 _)) at h₃
  rw [Functor.map_smul] at h₃
  erw [CategoryTheory.Functor.map_id] at h₃
  exact h₃

end Coextension

section Cones

variable {Λ : Type (u + 1)} [CommRing Λ] (ϖ : Λ)

/-- A natural transformation `α : F ⟶ G` of functors with values in `D(T_ét, Λ)` *has
`ϖ`-invertible cones* if every component `α_K` sits in a distinguished triangle
`F K ⟶ G K ⟶ C ⟶ F K[1]` with `ϖ` acting invertibly on `C`. Such a transformation induces
bijections on morphisms into objects receiving no nonzero map from `ϖ`-invertible objects, for
instance objects killed by a power of `ϖ`. -/
def HasSmulInvertibleCones {𝒞 : Type*} [Category 𝒞] {T : Scheme.{u}}
    {F G : 𝒞 ⥤ 𝐃(T, Λ)} (α : F ⟶ G) : Prop :=
  ∀ K, ∃ (C : 𝐃(T, Λ)) (b : G.obj K ⟶ C) (c : C ⟶ (F.obj K)⟦(1 : ℤ)⟧),
    Triangle.mk (α.app K) b c ∈ distTriang _ ∧ IsIso (ϖ • 𝟙 C)

variable {ϖ}

lemma HasSmulInvertibleCones.whiskerLeft {𝒞 𝒞' : Type*} [Category 𝒞] [Category 𝒞']
    {T : Scheme.{u}} {F G : 𝒞 ⥤ 𝐃(T, Λ)} {α : F ⟶ G} (hα : HasSmulInvertibleCones ϖ α)
    (Q : 𝒞' ⥤ 𝒞) : HasSmulInvertibleCones ϖ (Functor.whiskerLeft Q α) :=
  fun K ↦ hα (Q.obj K)

lemma HasSmulInvertibleCones.whiskerRight {𝒞 : Type*} [Category 𝒞] {T T' : Scheme.{u}}
    {F G : 𝒞 ⥤ 𝐃(T, Λ)} {α : F ⟶ G} (hα : HasSmulInvertibleCones ϖ α)
    (H : 𝐃(T, Λ) ⥤ 𝐃(T', Λ)) [H.CommShift ℤ] [H.IsTriangulated] [H.Linear Λ] :
    HasSmulInvertibleCones ϖ (Functor.whiskerRight α H) := fun K ↦ by
  obtain ⟨C, b, c, hT, hC⟩ := hα K
  refine ⟨H.obj C, H.map b, H.map c ≫ (H.commShiftIso (1 : ℤ)).hom.app _,
    H.map_distinguished _ hT, ?_⟩
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul]
  infer_instance

lemma HasSmulInvertibleCones.of_isIso {𝒞 : Type*} [Category 𝒞] {T : Scheme.{u}}
    {F G : 𝒞 ⥤ 𝐃(T, Λ)} (α : F ⟶ G) [IsIso α] : HasSmulInvertibleCones ϖ α := fun K ↦ by
  obtain ⟨C, b, c, hT⟩ := distinguished_cocone_triangle (α.app K)
  have hC : IsZero C := (Triangle.isZero₃_iff_isIso₁ _ hT).2
    (by change IsIso (α.app K); infer_instance)
  exact ⟨C, b, c, hT, ⟨⟨hC.to_ _, hC.eq_of_src _ _, hC.eq_of_src _ _⟩⟩⟩

/-- The functor `j ↦ Hom(F -, P j)` from `J` to presheaves on `D(X_ét, Λ)`. -/
noncomputable abbrev homFunctor {J : Type*} [Category J] {X T : Scheme.{u}}
    (P : J ⥤ 𝐃(T, Λ)) (F : 𝐃(X, Λ) ⥤ 𝐃(T, Λ)) :
    J ⥤ (𝐃(X, Λ)ᵒᵖ ⥤ Type (u + 1)) :=
  P ⋙ yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj F.op

/-- A natural transformation with `ϖ`-invertible cones induces an isomorphism of the functors
`Hom(G -, P j) ≅ Hom(F -, P j)` when every `P j` receives no nonzero map from a `ϖ`-invertible
object. -/
noncomputable def HasSmulInvertibleCones.homFunctorIso {J : Type*} [Category J]
    {X T : Scheme.{u}} {P : J ⥤ 𝐃(T, Λ)}
    (hP : ∀ j, (_root_.DerivedCategory.smulInvertible T.smallEtaleTopology ϖ).rightOrthogonal
      (P.obj j))
    {F G : 𝐃(X, Λ) ⥤ 𝐃(T, Λ)} {α : F ⟶ G} (hα : HasSmulInvertibleCones ϖ α) :
    homFunctor P G ≅ homFunctor P F :=
  have : IsIso (Functor.whiskerLeft (P ⋙ yoneda)
      ((Functor.whiskeringLeft _ _ (Type (u + 1))).map (NatTrans.op α))) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun j ↦
      @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun K ↦ ?_
    rw [isIso_iff_bijective]
    obtain ⟨C, b, c, hT, hC⟩ := hα K.unop
    exact ObjectProperty.bijective_comp_of_distinguished hT hC (hP j)
  asIso (Functor.whiskerLeft (P ⋙ yoneda)
    ((Functor.whiskeringLeft _ _ (Type (u + 1))).map (NatTrans.op α)))

/-- An isomorphism `F ≅ G` induces an isomorphism `Hom(G -, P j) ≅ Hom(F -, P j)`. -/
noncomputable def homFunctorIsoOfIso {J : Type*} [Category J] {X T : Scheme.{u}}
    (P : J ⥤ 𝐃(T, Λ)) {F G : 𝐃(X, Λ) ⥤ 𝐃(T, Λ)} (e : F ≅ G) :
    homFunctor P G ≅ homFunctor P F :=
  Functor.isoWhiskerLeft (P ⋙ yoneda) ((Functor.whiskeringLeft _ _ _).mapIso (NatIso.op e))

/-- Functors with isomorphic functors `Hom(F -, P j)` have isomorphic right adjoints on `P`. -/
noncomputable def rightAdjointIsoOfHomFunctorIso {J : Type*} [Category J] {X T : Scheme.{u}}
    (P : J ⥤ 𝐃(T, Λ)) {F G : 𝐃(X, Λ) ⥤ 𝐃(T, Λ)} {F' G' : 𝐃(T, Λ) ⥤ 𝐃(X, Λ)}
    (adjF : F ⊣ F') (adjG : G ⊣ G') (e : homFunctor P G ≅ homFunctor P F) :
    P ⋙ F' ≅ P ⋙ G' :=
  ((Yoneda.fullyFaithful.whiskeringRight J).preimageIso
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft P (adjF.compYonedaIso) ≪≫ e.symm ≪≫
      (Functor.isoWhiskerLeft P (adjG.compYonedaIso)).symm ≪≫ (Functor.associator _ _ _).symm))

end Cones

section Exchange

variable {Λ : Type (u + 1)} [CommRing Λ] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
  [Finite (Λ ⧸ Ideal.span {ϖ})]
include hϖ

/-- **The exchange of an extension by zero with a proper direct image has `ϖ`-invertible
cones.** For a cartesian square `g' ≫ j = j' ≫ g''` with `j`, `j'` open immersions and `g''`
proper, the exchange map `Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*` on `D(-_ét, Λ)` is an isomorphism over
the open `j` and, over its closed complement, its target is `ϖ`-invertible by proper base
change up to `ϖ`-invertible objects
(`AlgebraicGeometry.Etale.isIso_smul_id_mapDerivedCategoryUpperStar_rightDerivedLowerStar`). -/
theorem hasSmulInvertibleCones_openImmersionLowerShriekLowerStarExchange
    {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsProper g''] (hsq : IsPullback g' j' j g'') :
    HasSmulInvertibleCones ϖ (openImmersionLowerShriekLowerStarExchange
      (ModuleCat.{u + 1} Λ) hsq) := fun K ↦ by
  have hdisj : Disjoint (Set.range j.closedComplement.base) (Set.range j.base) := by
    rw [j.range_closedComplement]
    exact disjoint_compl_left
  let sq := IsPullback.of_hasPullback g'' j.closedComplement
  have hdisj' : Disjoint (Set.range (pullback.fst g'' j.closedComplement).base)
      (Set.range j'.base) := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, rfl⟩ ⟨u, hu⟩
    refine Set.disjoint_left.1 hdisj
      ⟨(pullback.snd g'' j.closedComplement).base p, rfl⟩ ⟨g'.base u, ?_⟩
    rw [← Scheme.Hom.comp_apply, hsq.w, Scheme.Hom.comp_apply, hu, ← Scheme.Hom.comp_apply,
      pullback.condition, Scheme.Hom.comp_apply]
  obtain ⟨C, b, c, hT⟩ := distinguished_cocone_triangle
    ((openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} Λ) hsq).app K)
  refine ⟨C, b, c, hT, isIso_of_isIso_mapDerivedCategoryUpperStar_map _ j j.closedComplement
    j.range_closedComplement _ ?_ ?_⟩
  · -- over `U` the exchange map is invertible, so the cone vanishes
    have := isIso_map_mateEquiv_app_of_isIso (mapDerivedUpperStarLowerStarAdjunction _ g')
      (mapDerivedUpperStarLowerStarAdjunction _ g'')
      (derivedOpenImmersionLowerShriekUpperStarAdjunction _ j)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction _ j')
      (TwoSquare.mk _ _ _ _ (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso _ hsq).inv) K
    have hC : IsZero (D((j)^*[ModuleCat.{u + 1} Λ]).obj C) :=
      (Triangle.isZero₃_iff_isIso₁ _ (D((j)^*[ModuleCat.{u + 1} Λ]).map_distinguished _ hT)).2
        this
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    exact ⟨⟨hC.to_ _, hC.eq_of_src _ _, hC.eq_of_src _ _⟩⟩
  · -- over the closed complement the source vanishes and the target is `ϖ`-invertible
    let i := j.closedComplement
    have h₁ : IsZero (D((i)^*[ModuleCat.{u + 1} Λ]).obj (D((j)_!open[ModuleCat.{u + 1} Λ]).obj
        (R((g')_*[ModuleCat.{u + 1} Λ]).obj K))) :=
      isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range _ j i
        hdisj _
    have hT' := D((i)^*[ModuleCat.{u + 1} Λ]).map_distinguished _ hT
    have h₂ := (Triangle.isZero₁_iff_isIso₂ _ hT').1 h₁
    have : IsIso (D((i)^*[ModuleCat.{u + 1} Λ]).map b) := h₂
    let e := asIso (D((i)^*[ModuleCat.{u + 1} Λ]).map b)
    have h₃ := isIso_smul_id_mapDerivedCategoryUpperStar_rightDerivedLowerStar hϖ sq
      (D((j')_!open[ModuleCat.{u + 1} Λ]).obj K)
      (isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range _ j' _
        hdisj' K)
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    have : ϖ • 𝟙 (D((i)^*[ModuleCat.{u + 1} Λ]).obj C) =
        e.inv ≫ (ϖ • 𝟙 _) ≫ e.hom := by
      rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, Iso.inv_hom_id]
    rw [this]
    have : IsIso (ϖ • 𝟙 (D((i)^*[ModuleCat.{u + 1} Λ]).obj
        ((D((j')_!open[ModuleCat.{u + 1} Λ]) ⋙ R((g'')_*[ModuleCat.{u + 1} Λ])).obj K))) := h₃
    infer_instance

end Exchange

section Composition

variable {Λ : Type (u + 1)} [CommRing Λ] {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
  [Finite (Λ ⧸ Ideal.span {ϖ})] {J : Type*} [Category J] {S : Scheme.{u}}
  {P : J ⥤ 𝐃(S, Λ)}
  (hP : ∀ j, (_root_.DerivedCategory.smulInvertible S.smallEtaleTopology ϖ).rightOrthogonal
    (P.obj j))
include hϖ hP

/-- The exchange map of
`AlgebraicGeometry.Etale.hasSmulInvertibleCones_openImmersionLowerShriekLowerStarExchange`,
whiskered on both sides, induces an isomorphism of the functors `Hom(-, P j)`. -/
noncomputable def homFunctorIsoExchange {U' U Z' Z X : Scheme.{u}} {g' : U' ⟶ U}
    {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z} [IsOpenImmersion j] [IsOpenImmersion j']
    [IsProper g''] (hsq : IsPullback g' j' j g'') (Q : 𝐃(X, Λ) ⥤ 𝐃(U', Λ))
    (K : 𝐃(Z, Λ) ⥤ 𝐃(S, Λ)) [K.CommShift ℤ] [K.IsTriangulated] [K.Linear Λ] :
    homFunctor P
        (Q ⋙ (R((g')_*[ModuleCat.{u + 1} Λ]) ⋙ D((j)_!open[ModuleCat.{u + 1} Λ])) ⋙ K) ≅
      homFunctor P
        (Q ⋙ (D((j')_!open[ModuleCat.{u + 1} Λ]) ⋙ R((g'')_*[ModuleCat.{u + 1} Λ])) ⋙ K) :=
  (((hasSmulInvertibleCones_openImmersionLowerShriekLowerStarExchange hϖ hsq).whiskerRight
    K).whiskerLeft Q).homFunctorIso hP |>.symm

/-- **`Rf_!` through a proper map with a locally closed factorisation, up to `ϖ`-invertible
cones.** The integral analogue of
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriekOfCompactification`: with the
notation there, the functors `Hom(Rf_!(c) -, ·)` and `Hom(Rh_* De_! Rπ_* -, ·)`, post-composed
with any triangulated `Λ`-linear `H`, agree on objects receiving no nonzero map from
`ϖ`-invertible objects. The proof is the same, with each exchange isomorphism replaced by the
exchange map, whose cones are `ϖ`-invertible. -/
theorem nonempty_homFunctorIso_rightDerivedLowerShriekOfCompactification {X Y P' U : Scheme.{u}}
    {f : X ⟶ Y} (c : Compactification f) (π : P' ⟶ Y) [IsProper π] (e : U ⟶ P')
    [IsOpenImmersion e] (h : X ⟶ U) [IsProper h] (fac : h ≫ e ≫ π = f)
    (H : 𝐃(Y, Λ) ⥤ 𝐃(S, Λ)) [H.CommShift ℤ] [H.IsTriangulated] [H.Linear Λ] :
    Nonempty (homFunctor P (Rf_!(c)[ModuleCat.{u + 1} Λ] ⋙ H) ≅
      homFunctor P ((R((h)_*[ModuleCat.{u + 1} Λ]) ⋙ D((e)_!open[ModuleCat.{u + 1} Λ]) ⋙
        R((π)_*[ModuleCat.{u + 1} Λ])) ⋙ H)) := by
  let 𝔸 := ModuleCat.{u + 1} Λ
  let ι {F G : 𝐃(X, Λ) ⥤ 𝐃(S, Λ)} (i : F ≅ G) : homFunctor P F ≅ homFunctor P G :=
    (homFunctorIsoOfIso P i).symm
  let p₁ := pullback.fst π c.g
  let p₂ := pullback.snd π c.g
  have : IsProper p₁ := MorphismProperty.pullback_fst _ _ c.isProper
  have : IsProper p₂ := MorphismProperty.pullback_snd _ _ ‹IsProper π›
  let ιX : X ⟶ pullback π c.g := pullback.lift (h ≫ e) c.i (by
    rw [Category.assoc, fac]; exact c.comm)
  -- the graph of `X` in `P ×_Y X`, open in `P ×_Y Z`
  let a₁ := pullback.fst p₂ c.i
  let s₁ := pullback.snd p₂ c.i
  have : IsSeparated s₁ := MorphismProperty.pullback_snd _ _ inferInstance
  let Γ₁ : X ⟶ pullback p₂ c.i := pullback.lift ιX (𝟙 X) (by simp [ιX, p₂])
  have : IsProper (Γ₁ ≫ s₁) := by rw [show Γ₁ ≫ s₁ = 𝟙 X from pullback.lift_snd _ _ _]
                                  infer_instance
  have : IsProper Γ₁ := IsProper.of_comp Γ₁ s₁
  -- `X` in `U ×_Y Z`, open in `P ×_Y Z`
  let a₂ := pullback.fst p₁ e
  let s₂ := pullback.snd p₁ e
  have : IsSeparated s₂ := MorphismProperty.pullback_snd _ _ inferInstance
  let h₂ : X ⟶ pullback p₁ e := pullback.lift ιX h (by simp [ιX, p₁])
  have : IsProper (h₂ ≫ s₂) := by rw [show h₂ ≫ s₂ = h from pullback.lift_snd _ _ _]
                                  infer_instance
  have : IsProper h₂ := IsProper.of_comp h₂ s₂
  -- the intersection of the two opens
  let b₁ := pullback.fst a₁ a₂
  let b₂ := pullback.snd a₁ a₂
  let γ : X ⟶ pullback a₁ a₂ := pullback.lift Γ₁ h₂ (by simp [Γ₁, h₂, a₁, a₂])
  have sqΓ : IsPullback γ (𝟙 X) b₁ Γ₁ :=
    IsPullback.of_vert_isIso_mono (snd := 𝟙 X) ⟨by simp [γ, b₁]⟩
  have sqh : IsPullback γ (𝟙 X) b₂ h₂ :=
    IsPullback.of_vert_isIso_mono (snd := 𝟙 X) ⟨by simp [γ, b₂]⟩
  let idX : R((𝟙 X)_*[𝔸]) ≅ 𝟭 _ :=
    (Etale.lowerStar 𝔸 (𝟙 X)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
      Functor.mapDerivedCategoryNatIso (Etale.lowerStarId 𝔸 X) ≪≫
      Functor.mapDerivedCategoryIdIso _
  let K'' := R((p₁ ≫ π)_*[𝔸]) ⋙ H
  -- the side of `c`
  let iA₁ : Rf_!(c)[𝔸] ⋙ H ≅
      R((Γ₁)_*[𝔸]) ⋙ (R((s₁)_*[𝔸]) ⋙ D((c.i)_!open[𝔸])) ⋙ (R((c.g)_*[𝔸]) ⋙ H) :=
    (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight (idX.symm ≪≫
      (rightDerivedLowerStarCompOfEq 𝔸 Γ₁ s₁ (𝟙 X) (pullback.lift_snd _ _ _)).symm) _ ≪≫
      Functor.associator _ _ _
  let wA := homFunctorIsoExchange hϖ hP (IsPullback.of_hasPullback p₂ c.i).flip
    (R((Γ₁)_*[𝔸])) (R((c.g)_*[𝔸]) ⋙ H)
  let iA₂ : R((Γ₁)_*[𝔸]) ⋙ (D((a₁)_!open[𝔸]) ⋙ R((p₂)_*[𝔸])) ⋙ (R((c.g)_*[𝔸]) ⋙ H) ≅
      R((Γ₁)_*[𝔸]) ⋙ D((a₁)_!open[𝔸]) ⋙ K'' :=
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (rightDerivedLowerStarCompOfEq 𝔸 p₂ c.g (p₁ ≫ π)
        pullback.condition.symm) H))
  -- the two extensions by zero agree
  let iC₁ : 𝟭 _ ⋙ (D((𝟙 X)_!open[𝔸]) ⋙ R((Γ₁)_*[𝔸])) ⋙ (D((a₁)_!open[𝔸]) ⋙ K'') ≅
      R((Γ₁)_*[𝔸]) ⋙ D((a₁)_!open[𝔸]) ⋙ K'' :=
    Functor.leftUnitor _ ≪≫ Functor.isoWhiskerRight (Functor.isoWhiskerRight
      (mapDerivedCategoryOpenImmersionLowerShriekId 𝔸 X) _ ≪≫ Functor.leftUnitor _) _
  let wC₁ := homFunctorIsoExchange hϖ hP sqΓ (𝟭 _) (D((a₁)_!open[𝔸]) ⋙ K'')
  let iC₂ : 𝟭 _ ⋙ (R((γ)_*[𝔸]) ⋙ D((b₁)_!open[𝔸])) ⋙ (D((a₁)_!open[𝔸]) ⋙ K'') ≅
      𝟭 _ ⋙ (R((γ)_*[𝔸]) ⋙ D((b₂)_!open[𝔸])) ⋙ (D((a₂)_!open[𝔸]) ⋙ K'') :=
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft (R((γ)_*[𝔸]))
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
        ((mapDerivedCategoryOpenImmersionLowerShriekComp 𝔸 b₁ a₁).symm ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekCongr 𝔸 pullback.condition ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekComp 𝔸 b₂ a₂) K'' ≪≫
        Functor.associator _ _ _))
  let wC₂ := homFunctorIsoExchange hϖ hP sqh (𝟭 _) (D((a₂)_!open[𝔸]) ⋙ K'')
  let iC₃ : 𝟭 _ ⋙ (D((𝟙 X)_!open[𝔸]) ⋙ R((h₂)_*[𝔸])) ⋙ (D((a₂)_!open[𝔸]) ⋙ K'') ≅
      R((h₂)_*[𝔸]) ⋙ D((a₂)_!open[𝔸]) ⋙ K'' :=
    Functor.leftUnitor _ ≪≫ Functor.isoWhiskerRight (Functor.isoWhiskerRight
      (mapDerivedCategoryOpenImmersionLowerShriekId 𝔸 X) _ ≪≫ Functor.leftUnitor _) _
  -- the side of `π`
  let iB₁ : (R((h)_*[𝔸]) ⋙ D((e)_!open[𝔸]) ⋙ R((π)_*[𝔸])) ⋙ H ≅
      R((h₂)_*[𝔸]) ⋙ (R((s₂)_*[𝔸]) ⋙ D((e)_!open[𝔸])) ⋙ (R((π)_*[𝔸]) ⋙ H) :=
    Functor.isoWhiskerRight (Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOfEq 𝔸 h₂ s₂ h (pullback.lift_snd _ _ _)).symm _) H
  let wB := homFunctorIsoExchange hϖ hP (IsPullback.of_hasPullback p₁ e).flip
    (R((h₂)_*[𝔸])) (R((π)_*[𝔸]) ⋙ H)
  let iB₂ : R((h₂)_*[𝔸]) ⋙ (D((a₂)_!open[𝔸]) ⋙ R((p₁)_*[𝔸])) ⋙ (R((π)_*[𝔸]) ⋙ H) ≅
      R((h₂)_*[𝔸]) ⋙ D((a₂)_!open[𝔸]) ⋙ K'' :=
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (rightDerivedLowerStarCompOfEq 𝔸 p₁ π (p₁ ≫ π) rfl) H))
  exact ⟨ι iA₁ ≪≫ wA ≪≫ ι iA₂ ≪≫ (ι iC₁).symm ≪≫ wC₁.symm ≪≫ ι iC₂ ≪≫ wC₂ ≪≫ ι iC₃ ≪≫
    (ι iB₂).symm ≪≫ wB.symm ≪≫ (ι iB₁).symm⟩

/-- **The composition law for `Rf_!` up to `ϖ`-invertible cones.** For composable `f : X ⟶ Y`
and `g : Y ⟶ T` admitting compactifications, the functors `Hom(R(f ≫ g)_! -, ·)` and
`Hom(Rg_! Rf_! -, ·)` agree on objects receiving no nonzero map from `ϖ`-invertible objects.
This is the proof of `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`, with
each exchange isomorphism replaced by the exchange map, whose cones are `ϖ`-invertible. -/
theorem nonempty_homFunctorIso_rightDerivedLowerShriek_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ S) [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    Nonempty (homFunctor P (R(f ≫ g)_![ModuleCat.{u + 1} Λ]) ≅
      homFunctor P (R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ])) := by
  let 𝔸 := ModuleCat.{u + 1} Λ
  let ι {F G : 𝐃(X, Λ) ⥤ 𝐃(S, Λ)} (i : F ≅ G) : homFunctor P F ≅ homFunctor P G :=
    (homFunctorIsoOfIso P i).symm
  let cf := HasCompactification.compactification f
  let cg := HasCompactification.compactification g
  let cfg := HasCompactification.compactification (f ≫ g)
  -- `P = V ×_T W`
  let φ := pullback.fst cfg.g cg.g
  let ψ := pullback.snd cfg.g cg.g
  have : IsProper φ := MorphismProperty.pullback_fst _ _ cg.isProper
  have : IsProper ψ := MorphismProperty.pullback_snd _ _ cfg.isProper
  -- `X` in the open `P ×_V X` of `P`
  let e := pullback.fst φ cfg.i
  let σ := pullback.snd φ cfg.i
  have : IsSeparated σ := MorphismProperty.pullback_snd _ _ inferInstance
  have w₁ : cfg.i ≫ cfg.g = (f ≫ cg.i) ≫ cg.g := by
    rw [← cfg.comm, Category.assoc, ← cg.comm]
  let h : X ⟶ pullback φ cfg.i :=
    pullback.lift (pullback.lift cfg.i (f ≫ cg.i) w₁) (𝟙 X) (by simp [φ])
  have : IsProper (h ≫ σ) := by rw [show h ≫ σ = 𝟙 X from pullback.lift_snd _ _ _]
                                infer_instance
  have : IsProper h := IsProper.of_comp h σ
  have he : h ≫ e = pullback.lift cfg.i (f ≫ cg.i) w₁ := pullback.lift_fst _ _ _
  obtain ⟨e₁⟩ := nonempty_homFunctorIso_rightDerivedLowerShriekOfCompactification hϖ hP cfg
    (ψ ≫ cg.g) e h
    (by rw [reassoc_of% he, pullback.lift_snd_assoc, Category.assoc, ← cg.comm]) (𝟭 _)
  -- `P ×_W Y`, open in `P` and proper over `Y`
  let eY := pullback.fst ψ cg.i
  let πY := pullback.snd ψ cg.i
  have : IsProper πY := MorphismProperty.pullback_snd _ _ inferInstance
  let uY := pullback.fst e eY
  let e' := pullback.snd e eY
  let ρ : X ⟶ pullback ψ cg.i := pullback.lift (h ≫ e) f (by rw [he]; simp [ψ])
  let h' : X ⟶ pullback e eY := pullback.lift h ρ (by simp [ρ, eY])
  have : IsProper (h' ≫ uY) := by rw [show h' ≫ uY = h from pullback.lift_fst _ _ _]
                                  infer_instance
  have : IsProper h' := IsProper.of_comp h' uY
  obtain ⟨e₂⟩ := nonempty_homFunctorIso_rightDerivedLowerShriekOfCompactification hϖ hP cf πY e'
    h' (by simp [h', e', ρ, πY]) (D((cg.i)_!open[𝔸]) ⋙ R((cg.g)_*[𝔸]))
  have sqh : IsPullback h' (𝟙 X) uY h :=
    IsPullback.of_vert_isIso_mono (snd := 𝟙 X) ⟨by simp [h', uY]⟩
  let i₁ : 𝟭 _ ⋙ (D((𝟙 X)_!open[𝔸]) ⋙ R((h)_*[𝔸])) ⋙
        (D((e)_!open[𝔸]) ⋙ R((ψ ≫ cg.g)_*[𝔸])) ≅
      R((h)_*[𝔸]) ⋙ D((e)_!open[𝔸]) ⋙ R((ψ ≫ cg.g)_*[𝔸]) :=
    Functor.leftUnitor _ ≪≫ Functor.isoWhiskerRight (Functor.isoWhiskerRight
      (mapDerivedCategoryOpenImmersionLowerShriekId 𝔸 X) _ ≪≫ Functor.leftUnitor _) _
  let w₁ := homFunctorIsoExchange hϖ hP sqh (𝟭 _) (D((e)_!open[𝔸]) ⋙ R((ψ ≫ cg.g)_*[𝔸]))
  let i₂ : 𝟭 _ ⋙ (R((h')_*[𝔸]) ⋙ D((uY)_!open[𝔸])) ⋙
        (D((e)_!open[𝔸]) ⋙ R((ψ ≫ cg.g)_*[𝔸])) ≅
      (R((h')_*[𝔸]) ⋙ D((e')_!open[𝔸])) ⋙ (D((eY)_!open[𝔸]) ⋙ R((ψ)_*[𝔸])) ⋙
        R((cg.g)_*[𝔸]) :=
    Functor.leftUnitor _ ≪≫ Functor.isoWhiskerLeft (R((h')_*[𝔸]))
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
        ((mapDerivedCategoryOpenImmersionLowerShriekComp 𝔸 uY e).symm ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekCongr 𝔸 pullback.condition ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekComp 𝔸 e' eY) _ ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (D((e')_!open[𝔸]))
          (Functor.isoWhiskerLeft (D((eY)_!open[𝔸]))
            (rightDerivedLowerStarCompOfEq 𝔸 ψ cg.g _ rfl).symm ≪≫
          (Functor.associator _ _ _).symm))
  let w₂ := homFunctorIsoExchange hϖ hP (IsPullback.of_hasPullback ψ cg.i).flip
    (R((h')_*[𝔸]) ⋙ D((e')_!open[𝔸])) (R((cg.g)_*[𝔸]))
  let i₃ : (R((h')_*[𝔸]) ⋙ D((e')_!open[𝔸])) ⋙ (R((πY)_*[𝔸]) ⋙ D((cg.i)_!open[𝔸])) ⋙
        R((cg.g)_*[𝔸]) ≅
      (R((h')_*[𝔸]) ⋙ D((e')_!open[𝔸]) ⋙ R((πY)_*[𝔸])) ⋙
        (D((cg.i)_!open[𝔸]) ⋙ R((cg.g)_*[𝔸])) :=
    Iso.refl _
  exact ⟨ι (Functor.rightUnitor _).symm ≪≫ e₁ ≪≫ ι (Functor.rightUnitor _) ≪≫ (ι i₁).symm ≪≫
    w₁.symm ≪≫ ι i₂ ≪≫ w₂.symm ≪≫ ι i₃ ≪≫ e₂.symm⟩

/-- **The composition law for `Rf^!` on objects killed by powers of `ϖ`.** For composable
`f : X ⟶ Y` and `g : Y ⟶ S` admitting compactifications, with `Rf_!` left adjoints, and a
functor `P : J ⥤ D(S_ét, Λ)` whose values receive no nonzero map from `ϖ`-invertible objects
(for instance the tower `n ↦ Λ ⧸ (ϖ)ⁿ`), the exceptional inverse images satisfy
`P ⋙ R(f ≫ g)^! ≅ P ⋙ Rg^! ⋙ Rf^!` for the chosen right adjoints `Rf^!` of `Rf_!`: by the
Yoneda lemma, from
`AlgebraicGeometry.Etale.nonempty_homFunctorIso_rightDerivedLowerShriek_comp`. -/
theorem nonempty_iso_comp_rightDerivedUpperShriek_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ S) [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] [(R(g)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    [(R(f ≫ g)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] :
    Nonempty (P ⋙ (R(f ≫ g)_![ModuleCat.{u + 1} Λ]).rightAdjoint ≅
      P ⋙ (R(g)_![ModuleCat.{u + 1} Λ]).rightAdjoint ⋙
        (R(f)_![ModuleCat.{u + 1} Λ]).rightAdjoint) := by
  obtain ⟨e⟩ := nonempty_homFunctorIso_rightDerivedLowerShriek_comp hϖ hP f g
  exact ⟨rightAdjointIsoOfHomFunctorIso P (Adjunction.ofIsLeftAdjoint _)
    ((Adjunction.ofIsLeftAdjoint _).comp (Adjunction.ofIsLeftAdjoint _))
    e.symm⟩

end Composition

end Etale

end AlgebraicGeometry
