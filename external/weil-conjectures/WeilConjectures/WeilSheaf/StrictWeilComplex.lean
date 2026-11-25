/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FrobeniusDerived

/-!
# From Weil complexes to strict Weil complexes

Blueprint `definition-weil-structure` and `definition-weil-structure` (paragraph "Strict Weil
complexes"): a *strict Weil complex* on a `k₀`-scheme `X` is a pair `(K, θ)` of a complex `K` of
`ℓ`-adic pro-étale sheaves on the geometric fiber `X̄` and an isomorphism
`θ : Lg_X^* K ≅ K`, where `g_X = Fr_X` is the geometric Frobenius of `X̄`. A Weil complex `K`
gives the strict Weil complex `(For(K), θ_K)`, where `θ_K` is its derived Frobenius
(`AlgebraicGeometry.WeilComplex.frobeniusIso`).

This file constructs the functor `AlgebraicGeometry.WeilComplex.toStrictWeilComplex` and shows
that it is an equivalence on the hearts: on Weil sheaves (Weil complexes concentrated in degree
zero) it is fully faithful, and its essential image consists of the pairs `(F[0], θ)` with `F`
a constructible sheaf. It is not faithful (see
`WeilConjectures.WeilSheaf.StrictWeilComplexNotFaithful`).

## Design

The category of strict Weil complexes is `AlgebraicGeometry.StrictWeilComplex k₀ l X`, the
category `IsoAlgebra (D(Fr_X^*))` of pairs `(K, θ : D(Fr_X^*) K ≅ K)` with `K` in the whole
derived category of `ℓ`-adic pro-étale sheaves on `X̄`; the Frobenius pullback `Fr_X^*` is exact,
so `D(Fr_X^*)` is its derived functor `Lg_X^*`. A pro-étale Weil sheaf `(F, φ)` gives the strict
Weil complex `(F[0], φ[0])` (`AlgebraicGeometry.ProEtaleWeilSheaf.toStrictWeilComplex`), the
transport of `IsoAlgebra` along the fully faithful functor `F ↦ F[0]`, which is fully faithful
with essential image the pairs whose underlying complex is concentrated in degree `0`
(`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso`). The key compatibility
`AlgebraicGeometry.WeilSheaf.toStrictWeilComplexIso` identifies the derived
Frobenius of `F[0]` with `φ[0]`; it rests on the compatibility of the isomorphisms
`D(U) ∘ D(G) ≅ D(U ∘ G)` and `D(U) ≅ D(V)` with the single functors
(`CategoryTheory.Functor.mapDerivedCategoryCompIso_inv_app_singleFunctor`).

## Main definitions and results

- `CategoryTheory.Endofunctor.IsoAlgebra.lift`: the functor to `IsoAlgebra F` given by a functor
  `Φ` with an isomorphism `Φ ⋙ F ≅ Φ`.
- `AlgebraicGeometry.StrictWeilComplex`: strict Weil complexes.
- `AlgebraicGeometry.WeilComplex.toStrictWeilComplex`: `K ↦ (For(K), θ_K)`, with
  `AlgebraicGeometry.WeilComplex.toStrictWeilComplexCompForgetIso`.
- `AlgebraicGeometry.WeilSheaf.toStrictWeilComplex`: its restriction to the heart, fully
  faithful, with essential image `AlgebraicGeometry.StrictWeilComplex.heart`
  (`AlgebraicGeometry.WeilSheaf.essImage_toStrictWeilComplex`), and the resulting equivalence
  `AlgebraicGeometry.WeilSheaf.strictWeilComplexHeartEquivalence`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {A C D : Type*} [Category A] [Category C] [Category D]

section Lift

variable {F : C ⥤ C} (Φ : A ⥤ C) (e : Φ ⋙ F ≅ Φ)

/-- The functor `A ⥤ IsoAlgebra F` given by a functor `Φ : A ⥤ C` and an isomorphism
`e : Φ ⋙ F ≅ Φ`: an object `K` is sent to `Φ K` with structure isomorphism `e_K`. -/
noncomputable def lift : A ⥤ IsoAlgebra F where
  obj K := mk (Φ.obj K) (e.app K)
  map {_ _} f := ObjectProperty.homMk
    { f := Φ.map f
      h := e.hom.naturality f }
  map_id K := ObjectProperty.hom_ext _ (Algebra.Hom.ext (Φ.map_id K))
  map_comp f g := ObjectProperty.hom_ext _ (Algebra.Hom.ext (Φ.map_comp f g))

@[simp]
lemma lift_obj_carrier (K : A) : ((lift Φ e).obj K).carrier = Φ.obj K :=
  rfl

@[simp]
lemma lift_obj_str (K : A) : ((lift Φ e).obj K).str = e.app K :=
  mk_str _ _

@[simp]
lemma lift_map_hom_f {K K' : A} (f : K ⟶ K') : ((lift Φ e).map f).hom.f = Φ.map f :=
  rfl

/-- The underlying object of `lift Φ e` is given by `Φ`. -/
noncomputable def liftCompForgetIso : lift Φ e ⋙ forget F ≅ Φ :=
  Iso.refl _

end Lift

section Map

variable {F : C ⥤ C} {G : D ⥤ D} {L : C ⥤ D} (e : L ⋙ G ≅ F ⋙ L)

/-- The transport of algebras along a faithful functor is faithful. -/
instance faithful_mapOfNatIso [L.Faithful] : (mapOfNatIso e).Faithful where
  map_injective {_ _} _ _ h := ObjectProperty.hom_ext _ (Algebra.Hom.ext
    (L.map_injective (congrArg (fun φ ↦ φ.hom.f) h)))

/-- The transport of algebras along a fully faithful functor is full: a morphism
`L a ⟶ L b` compatible with the transported structure isomorphisms comes from a morphism
`a ⟶ b`, which is compatible with the structure isomorphisms since `L` is faithful. -/
instance full_mapOfNatIso [L.Full] [L.Faithful] : (mapOfNatIso e).Full where
  map_surjective {K K'} g := by
    refine ⟨ObjectProperty.homMk
      { f := L.preimage g.hom.f
        h := L.map_injective ?_ }, ObjectProperty.hom_ext _ (Algebra.Hom.ext (L.map_preimage _))⟩
    have hg : G.map g.hom.f ≫ e.hom.app K'.carrier ≫ L.map K'.str.hom =
        (e.hom.app K.carrier ≫ L.map K.str.hom) ≫ g.hom.f := g.hom.h
    have hn : G.map g.hom.f ≫ e.hom.app K'.carrier =
        e.hom.app K.carrier ≫ L.map (F.map (L.preimage g.hom.f)) := by
      simpa using e.hom.naturality (L.preimage g.hom.f)
    rw [L.map_comp, L.map_comp, L.map_preimage, ← cancel_epi (e.hom.app K.carrier),
      ← reassoc_of% hn]
    exact hg.trans (Category.assoc _ _ _)

/-- An algebra `K` of `G` together with an isomorphism `i : L c ≅ K` from the image of an object
of `C` under a fully faithful `L`: the algebra of `F` on `c` whose transport is `K`. -/
noncomputable def mapOfNatIsoPreimage [L.Full] [L.Faithful] (K : IsoAlgebra G) (c : C)
    (i : L.obj c ≅ K.carrier) : IsoAlgebra F :=
  mk c (L.preimageIso ((e.app c).symm ≪≫ G.mapIso i ≪≫ K.str ≪≫ i.symm))

@[simp]
lemma mapOfNatIsoPreimage_carrier [L.Full] [L.Faithful] (K : IsoAlgebra G) (c : C)
    (i : L.obj c ≅ K.carrier) : (mapOfNatIsoPreimage e K c i).carrier = c :=
  rfl

/-- The transport of `mapOfNatIsoPreimage e K c i` is isomorphic to `K`, through `i`. -/
noncomputable def mapOfNatIsoObjPreimageIso [L.Full] [L.Faithful] (K : IsoAlgebra G) (c : C)
    (i : L.obj c ≅ K.carrier) : (mapOfNatIso e).obj (mapOfNatIsoPreimage e K c i) ≅ K :=
  ObjectProperty.isoMk _ (Algebra.isoMk i (by
    have h : ((mapOfNatIso e).obj (mapOfNatIsoPreimage e K c i)).str.hom =
        G.map i.hom ≫ K.str.hom ≫ i.inv := by
      rw [mapOfNatIso_obj_str]
      simp [mapOfNatIsoPreimage]
    rw [← str_hom, ← str_hom, h]
    simp))

/-- The essential image of the transport along a fully faithful functor consists of the algebras
whose underlying object is in the essential image of the functor. -/
lemma essImage_mapOfNatIso [L.Full] [L.Faithful] (K : IsoAlgebra G) :
    (mapOfNatIso e).essImage K ↔ L.essImage K.carrier := by
  refine ⟨fun ⟨K₀, ⟨i⟩⟩ ↦ ⟨K₀.carrier, ⟨(forget G).mapIso i⟩⟩, fun ⟨c, ⟨i⟩⟩ ↦ ?_⟩
  exact ⟨_, ⟨mapOfNatIsoObjPreimageIso e K c i⟩⟩

end Map

end CategoryTheory.Endofunctor.IsoAlgebra

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

/-- The single functor `DerivedCategory.singleFunctor _ 0` commutes with the functor induced by
an exact functor through the factorization `Functor.mapDerivedCategoryFactors`. -/
lemma mapDerivedCategorySingleFunctor_hom_app_zero (U : C ⥤ D) [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U] (X : C) :
    (U.mapDerivedCategorySingleFunctor 0).hom.app X =
      U.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj X) ≫
        DerivedCategory.Q.map ((U.mapCochainComplexSingleFunctor 0).hom.app X) := by
  simp [Functor.mapDerivedCategorySingleFunctor, Functor.mapCochainComplexSingleFunctor,
    CochainComplex.singleFunctor,
    DerivedCategory.singleFunctorIsoCompQ]

/-- The isomorphism `D(U) ⋙ D(G) ≅ D(V)` induced by an isomorphism `α : U ⋙ G ≅ V` of exact
functors is, on a single complex `X[0]`, the image of `α_X` under the single functor, up to the
identifications `D(U)(X[0]) ≅ (U X)[0]`, `D(G)((U X)[0]) ≅ (G (U X))[0]` and
`D(V)(X[0]) ≅ (V X)[0]`. -/
lemma mapDerivedCategoryCompIso_inv_app_singleFunctor (U : C ⥤ D) (G : D ⥤ E) (V : C ⥤ E)
    [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (α : U ⋙ G ≅ V) (X : C) :
    (mapDerivedCategoryCompIso U G).hom.app ((DerivedCategory.singleFunctor C 0).obj X) ≫
        (mapDerivedCategoryNatIso α).hom.app ((DerivedCategory.singleFunctor C 0).obj X) ≫
        (V.mapDerivedCategorySingleFunctor 0).hom.app X =
      G.mapDerivedCategory.map ((U.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app (U.obj X) ≫
        (DerivedCategory.singleFunctor E 0).map (α.hom.app X) := by
  rw [mapDerivedCategorySingleFunctor_hom_app_zero V,
    mapDerivedCategorySingleFunctor_hom_app_zero U,
    mapDerivedCategorySingleFunctor_hom_app_zero G, Functor.map_comp, Category.assoc,
    Category.assoc]
  erw [mapDerivedCategoryNatIso_fac_assoc α ((CochainComplex.singleFunctor C 0).obj X),
    ← mapDerivedCategoryCompIso_fac_assoc U G ((CochainComplex.singleFunctor C 0).obj X)]
  erw [Iso.hom_inv_id_app_assoc]
  congr 1
  have hn := G.mapDerivedCategoryFactors.hom.naturality
    ((U.mapCochainComplexSingleFunctor 0).hom.app X)
  erw [reassoc_of% hn]
  congr 1
  have hs : (DerivedCategory.singleFunctor E 0).map (α.hom.app X) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor E 0).map (α.hom.app X)) := rfl
  rw [hs]
  simp only [← Functor.map_comp]
  congr 1
  refine HomologicalComplex.to_single_hom_ext ?_
  simp only [comp_obj, HomologicalComplex.comp_f, mapHomologicalComplexCompIso_hom_app_f,
    Iso.refl_hom, NatTrans.id_app, NatTrans.mapHomologicalComplex_app_f,
    mapHomologicalComplex_map_f, Functor.mapCochainComplexSingleFunctor,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self, CochainComplex.singleFunctor,
    HomologicalComplex.single_map_f_self,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq, eqToIso_refl,
    Iso.refl_inv, Category.id_comp, Functor.map_id]
  erw [Functor.map_id, Category.id_comp, Category.id_comp]

end CategoryTheory.Functor

namespace AlgebraicGeometry

open Endofunctor ProEtale

section

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Blueprint `definition-weil-structure` and `definition-weil-structure` (strict Weil
complexes).

The category of *strict Weil complexes* on `X`: pairs `(K, θ)` of an object `K` of the derived
category of `ℓ`-adic pro-étale sheaves on the geometric fiber `X̄` and an isomorphism
`θ : Lg_X^* K ≅ K`, where `Lg_X^* = D(Fr_X^*)` is the (exact) Frobenius pullback; a morphism is a
morphism of complexes commuting with the `θ`'s. -/
abbrev StrictWeilComplex :=
  IsoAlgebra (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory

/-- The *heart* of the strict Weil complexes: the pairs `(K, θ)` with `K ≅ F[0]` for a
constructible sheaf `F`. -/
def StrictWeilComplex.heart : ObjectProperty (StrictWeilComplex k₀ l X) :=
  fun K ↦ ∃ F : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber,
    IsAdicConstructibleSheaf F ∧
      Nonempty ((DerivedCategory.singleFunctor _ 0).obj F ≅ K.carrier)

end

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace WeilComplex

/-- Blueprint `definition-weil-structure` and `definition-weil-structure` (strict Weil
complexes).

The functor from Weil complexes to strict Weil complexes, `K ↦ (For(K), θ_K)`, where
`For(K)` is the underlying complex of `ℓ`-adic sheaves (`AlgebraicGeometry.WeilComplex.forget`)
and `θ_K : Lg_X^* For(K) ≅ For(K)` its derived Frobenius
(`AlgebraicGeometry.WeilComplex.frobeniusIso`). It is an equivalence on the hearts
(`AlgebraicGeometry.WeilSheaf.toStrictWeilComplex`) but not faithful. -/
noncomputable def toStrictWeilComplex : WeilComplex k₀ l X ⥤ StrictWeilComplex k₀ l X :=
  IsoAlgebra.lift forget (frobeniusIso X)

/-- The underlying complex of the strict Weil complex of `K` is `For(K)`. -/
noncomputable def toStrictWeilComplexCompForgetIso :
    toStrictWeilComplex ⋙ IsoAlgebra.forget _ ≅ forget (k₀ := k₀) (l := l) (X := X) :=
  Iso.refl _

@[simp]
lemma toStrictWeilComplex_obj_carrier (K : WeilComplex k₀ l X) :
    (toStrictWeilComplex.obj K).carrier = forget.obj K :=
  rfl

/-- The structure isomorphism of the strict Weil complex of `K` is the derived Frobenius
`θ_K`. -/
@[simp]
lemma toStrictWeilComplex_obj_str (K : WeilComplex k₀ l X) :
    (toStrictWeilComplex.obj K).str = (frobeniusIso X).app K :=
  IsoAlgebra.lift_obj_str _ _ _

@[simp]
lemma toStrictWeilComplex_map_hom_f {K L : WeilComplex k₀ l X} (f : K ⟶ L) :
    (toStrictWeilComplex.map f).hom.f = forget.map f :=
  rfl

end WeilComplex

namespace ProEtaleWeilSheaf

variable (k₀ l X) in
/-- A pro-étale Weil sheaf `(F, φ)` placed in degree zero, as the strict Weil complex
`(F[0], φ[0])`: the transport along the fully faithful functor `F ↦ F[0]`, which commutes with
the Frobenius pullback. -/
noncomputable def toStrictWeilComplex : ProEtaleWeilSheaf k₀ l X ⥤ StrictWeilComplex k₀ l X :=
  IsoAlgebra.mapOfNatIso ((WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategorySingleFunctor 0)

instance : (toStrictWeilComplex k₀ l X).Full :=
  IsoAlgebra.full_mapOfNatIso _

instance : (toStrictWeilComplex k₀ l X).Faithful :=
  IsoAlgebra.faithful_mapOfNatIso _

end ProEtaleWeilSheaf

namespace WeilSheaf

variable (k₀ l X) in
/-- Blueprint `definition-weil-structure` (strict Weil complexes on the heart).

The functor from Weil sheaves to strict Weil complexes, `F ↦ (F[0], θ_{F[0]})`, the restriction
of `AlgebraicGeometry.WeilComplex.toStrictWeilComplex` to the heart. -/
noncomputable abbrev toStrictWeilComplex : WeilSheaf k₀ l X ⥤ StrictWeilComplex k₀ l X :=
  toComplex ⋙ WeilComplex.toStrictWeilComplex

/-- On the heart, the derived Frobenius of `F[0]` is `φ[0]`: the strict Weil complex of a Weil
sheaf `(F, φ)` is `(F[0], φ[0])`, through the identification `For(F[0]) ≅ F[0]`. -/
noncomputable def toStrictWeilComplexIso :
    toStrictWeilComplex k₀ l X ≅
      (objectProperty k₀ l X).ι ⋙ ProEtaleWeilSheaf.toStrictWeilComplex k₀ l X :=
  NatIso.ofComponents
    (fun F ↦ ObjectProperty.isoMk _ (Algebra.isoMk
      (((IsoAlgebra.forget _).mapDerivedCategorySingleFunctor 0).app F.obj)
      ((Functor.mapDerivedCategoryCompIso_inv_app_singleFunctor (IsoAlgebra.forget _)
        (frobeniusPullback k₀ l X) (IsoAlgebra.forget _) (IsoAlgebra.forgetCompIso _)
          F.obj).symm.trans (Category.assoc _ _ _).symm)))
    (fun f ↦ ObjectProperty.hom_ext _ (Algebra.Hom.ext
      (((IsoAlgebra.forget _).mapDerivedCategorySingleFunctor 0).hom.naturality f.hom)))

variable (k₀ l X) in
/-- Blueprint `definition-weil-structure`: on the hearts, the functor from Weil complexes to
strict Weil complexes is fully faithful, being isomorphic to the composite of the fully
faithful inclusion of Weil sheaves into pro-étale Weil sheaves and the fully faithful
`(F, φ) ↦ (F[0], φ[0])`. -/
noncomputable def fullyFaithfulToStrictWeilComplex :
    (toStrictWeilComplex k₀ l X).FullyFaithful :=
  ((ObjectProperty.fullyFaithfulι _).comp
    (Functor.FullyFaithful.ofFullyFaithful _)).ofIso toStrictWeilComplexIso.symm

instance : (toStrictWeilComplex k₀ l X).Full :=
  (fullyFaithfulToStrictWeilComplex k₀ l X).full

instance : (toStrictWeilComplex k₀ l X).Faithful :=
  (fullyFaithfulToStrictWeilComplex k₀ l X).faithful

variable (k₀ l X) in
/-- Blueprint `definition-weil-structure` (equivalence on the hearts): the essential image of the
functor from Weil sheaves to strict Weil complexes is the heart, the pairs `(K, θ)` with
`K ≅ F[0]` for a constructible sheaf `F`. Given such a pair, `θ` corresponds, `F ↦ F[0]` being
fully faithful, to a unique Weil structure `φ : Fr_X^* F ≅ F` with `θ ≅ φ[0]`. -/
theorem essImage_toStrictWeilComplex :
    (toStrictWeilComplex k₀ l X).essImage = StrictWeilComplex.heart k₀ l X := by
  ext K
  refine ⟨fun ⟨F, ⟨i⟩⟩ ↦ ⟨F.obj.carrier, F.property, ⟨(IsoAlgebra.forget _).mapIso
    ((toStrictWeilComplexIso.app F).symm ≪≫ i)⟩⟩, fun ⟨F, hF, ⟨i⟩⟩ ↦ ?_⟩
  exact ⟨⟨IsoAlgebra.mapOfNatIsoPreimage
      ((WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategorySingleFunctor 0) K F i, hF⟩,
    ⟨toStrictWeilComplexIso.app _ ≪≫ IsoAlgebra.mapOfNatIsoObjPreimageIso _ K F i⟩⟩

variable (k₀ l X) in
/-- The functor from Weil sheaves to the heart of the strict Weil complexes. -/
noncomputable def toStrictWeilComplexHeart :
    WeilSheaf k₀ l X ⥤ (StrictWeilComplex.heart k₀ l X).FullSubcategory :=
  (StrictWeilComplex.heart k₀ l X).lift (toStrictWeilComplex k₀ l X) fun F ↦ by
    rw [← essImage_toStrictWeilComplex]
    exact (toStrictWeilComplex k₀ l X).obj_mem_essImage F

instance : (toStrictWeilComplexHeart k₀ l X).IsEquivalence where
  faithful := by
    dsimp only [toStrictWeilComplexHeart]
    infer_instance
  full := by
    dsimp only [toStrictWeilComplexHeart]
    infer_instance
  essSurj := ⟨fun K ↦ by
    have h : (toStrictWeilComplex k₀ l X).essImage K.obj := by
      rw [essImage_toStrictWeilComplex]
      exact K.property
    obtain ⟨F, ⟨i⟩⟩ := h
    exact ⟨F, ⟨ObjectProperty.isoMk _ i⟩⟩⟩

variable (k₀ l X) in
/-- Blueprint `definition-weil-structure` (equivalence on the hearts): the functor from Weil
complexes to strict Weil complexes induces an equivalence between Weil sheaves and the heart of
the strict Weil complexes, the pairs `(F[0], θ)` with `F` a constructible sheaf. -/
noncomputable def strictWeilComplexHeartEquivalence :
    WeilSheaf k₀ l X ≌ (StrictWeilComplex.heart k₀ l X).FullSubcategory :=
  (toStrictWeilComplexHeart k₀ l X).asEquivalence

end WeilSheaf

end AlgebraicGeometry
