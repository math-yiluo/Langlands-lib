/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.Composition
public import WeilConjectures.Compactification.TriangleOfIsPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek

/-!

# Triangles of compactifications in the exchange formalism of `ℚ̄_ℓ`-sheaves

A triangle of compactifications `T` of `f.left` and `g.left` (`Compactification.Triangle`), for
composable morphisms `f : X ⟶ Y`, `g : Y ⟶ S` of separated `k`-schemes of finite type, is a
triangle of factorizations of the exchange formalism of bounded constructible complexes
(`ProEtale.CondensedRing.triangleShriekTriangle`). Its composition isomorphism
`Rf_!^{T.cf} ⋙ Rg_!^{T.cg} ≅ R(f ≫ g)_!^{T.cfg}` is defined for `ℚ̄_ℓ`-sheaves, and a morphism of
triangles gives a morphism of triangles of factorizations
(`ProEtale.CondensedRing.triangleShriekTriangleHom`).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

/-- The inverse of an isomorphism `(J₁ ⋙ P₁) ⋙ (J₂ ⋙ P₂) ≅ J ⋙ P` assembled from
`ε : P₁ ⋙ J₂ ≅ J_q ⋙ P_r`, `σ : J ≅ J₁ ⋙ J_q` and `π : P ≅ P_r ⋙ P₂`, in the shape of the
composition isomorphism of an exchange formalism. -/
lemma CategoryTheory.Functor.compIso_symm_aux {X Y Z₁ Z₂ W S : Type*} [Category* X] [Category* Y]
    [Category* Z₁] [Category* Z₂] [Category* W] [Category* S] {J₁ : X ⥤ Z₁} {P₁ : Z₁ ⥤ Y}
    {J₂ : Y ⥤ Z₂} {P₂ : Z₂ ⥤ S} {Jq : Z₁ ⥤ W} {Pr : W ⥤ Z₂} {J : X ⥤ W} {P : W ⥤ S}
    (ε : P₁ ⋙ J₂ ≅ Jq ⋙ Pr) (σ : J ≅ J₁ ⋙ Jq) (π : P ≅ Pr ⋙ P₂) :
    Functor.isoWhiskerRight σ P ≪≫ Functor.isoWhiskerLeft (J₁ ⋙ Jq) π ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft J₁ ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight ε.symm P₂ ≪≫ Functor.associator _ _ _) ≪≫
        (Functor.associator _ _ _).symm =
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft J₁ ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight ε P₂ ≪≫ Functor.associator _ _ _) ≪≫
        (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight σ.symm _ ≪≫
        Functor.isoWhiskerLeft _ π.symm).symm := by
  ext K
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.comp_obj, Category.assoc]
  exact π.hom.naturality_assoc _ _

/-- An algebraic identity between isomorphisms used to compare composition isomorphisms through
a common refinement. -/
lemma CategoryTheory.Iso.trans_symm_eq_of_comm {𝒜 : Type*} [Category* 𝒜]
    {P₀ P P'' Q₀ Q Q'' Q₁ : 𝒜} (a₀ : P₀ ≅ Q₀) (a : P ≅ Q) (a'' : P'' ≅ Q'') (x : Q₀ ≅ Q'')
    (y : Q ≅ Q'') (u₀ : P₀ ≅ P'') (u : P ≅ P'') (z : Q₁ ≅ Q₀) (z' : Q₁ ≅ Q) (v : P ≅ P₀)
    (n₁ : a₀.hom ≫ x.hom = u₀.hom ≫ a''.hom) (n₂ : a.hom ≫ y.hom = u.hom ≫ a''.hom)
    (hz : z.hom ≫ x.hom = z'.hom ≫ y.hom) (hv : v.hom ≫ u₀.hom = u.hom) :
    z.hom ≫ a₀.inv = z'.hom ≫ a.inv ≫ v.hom := by
  have e₁ : a₀.inv = x.hom ≫ a''.inv ≫ u₀.inv := by
    rw [← cancel_epi a₀.hom, Iso.hom_inv_id, reassoc_of% n₁]
    simp
  have e₂ : a''.inv = y.inv ≫ a.inv ≫ u.hom := by
    rw [← cancel_epi y.hom, Iso.hom_inv_id_assoc, ← cancel_epi a.hom, reassoc_of% n₂]
    simp
  rw [e₁, reassoc_of% hz, e₂]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← hv]
  simp

namespace AlgebraicGeometry.Compactification.Triangle

variable {k : Type u} [Field k] {X Y S : Over (Spec (.of k))} {f : X ⟶ Y} {g : Y ⟶ S}
  (T : Triangle f.left g.left)

/-- The compactification of the composite of a triangle, as a compactification of
`(f ≫ g).left`. -/
abbrev overCfg : AlgebraicGeometry.Compactification (f ≫ g).left := T.cfg

/-- The open immersion `q` of a triangle of compactifications, as a morphism of `Over S`. -/
noncomputable def overQ : T.cf.overObj ⟶ (overCfg T).overObj :=
  Over.homMk T.q (by
    change T.q ≫ T.cfg.g ≫ S.hom = T.cf.g ≫ Y.hom
    rw [← Category.assoc, T.q_cfg_g, Category.assoc, Over.w g])

/-- The map `p` of a triangle of compactifications, as a morphism of `Over S`. -/
noncomputable def overP : (overCfg T).overObj ⟶ T.cg.overObj :=
  Over.homMk T.p (by
    change T.p ≫ T.cg.g ≫ S.hom = T.cfg.g ≫ S.hom
    rw [← Category.assoc, T.p_g])

@[simp] lemma overQ_left : (overQ T).left = T.q := rfl
@[simp] lemma overP_left : (overP T).left = T.p := rfl

instance : IsOpenImmersion (overQ T).left := inferInstanceAs (IsOpenImmersion T.q)
instance : IsProper (overP T).left := inferInstanceAs (IsProper T.p)

/-- The open immersion of `T.cf` followed by `q` is the open immersion of `T.cfg`. -/
lemma overI_overQ : T.cf.overI ≫ overQ T = (overCfg T).overI :=
  Over.OverMorphism.ext T.i_q

/-- The map `p` followed by the proper map of `T.cg` is the proper map of `T.cfg`. -/
lemma overP_overG : overP T ≫ T.cg.overG = (overCfg T).overG :=
  Over.OverMorphism.ext T.p_g

/-- The square of a triangle of compactifications, as a cartesian square of `Over S`. -/
lemma isPullback_over : IsPullback T.cf.overG (overQ T) T.cg.overI (overP T) :=
  IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext T.isPullback.w) T.isPullback

end AlgebraicGeometry.Compactification.Triangle

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- The formalism `boundedConstructibleExchangeFormalism`, for `ℚ̄_ℓ`-sheaves. -/
local notation "𝔽" => boundedConstructibleExchangeFormalism ℓ k

variable {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom] {f : X ⟶ Y} {g : Y ⟶ S}

open Compactification.Triangle in
/-- A triangle of compactifications of `f.left` and `g.left` as a triangle of factorizations of the
exchange formalism of bounded constructible complexes. -/
noncomputable abbrev triangleShriekTriangle
    (T : AlgebraicGeometry.Compactification.Triangle f.left g.left) :
    ExchangeFormalism.ShriekTriangle SepFinType.openImmersion (SepFinType.mk X)
      (SepFinType.mk Y) (SepFinType.mk S) where
  Z₁ := SepFinType.mk T.cf.overObj
  Z₂ := SepFinType.mk T.cg.overObj
  W := SepFinType.mk (overCfg T).overObj
  i₁ := SepFinType.homMk T.cf.overI
  p₁ := SepFinType.homMk T.cf.overG
  i₂ := SepFinType.homMk T.cg.overI
  p₂ := SepFinType.homMk T.cg.overG
  i := SepFinType.homMk (overCfg T).overI
  p := SepFinType.homMk (overCfg T).overG
  q := SepFinType.homMk (overQ T)
  r := SepFinType.homMk (overP T)
  i_q := SepFinType.homMk_comp_homMk (b := overQ T) (d := 𝟙 _)
    ((overI_overQ T).trans (Category.comp_id _).symm) |>.trans (Category.comp_id _)
  r_p := SepFinType.homMk_comp_homMk (b := T.cg.overG) (c := (overCfg T).overG) (d := 𝟙 _)
    ((overP_overG T).trans (Category.comp_id _).symm) |>.trans (Category.comp_id _)
  w := SepFinType.homMk_comp_homMk (isPullback_over T).w


section Chosen

variable (c : AlgebraicGeometry.Compactification f.left)
  (c' : AlgebraicGeometry.Compactification g.left)
  (d : AlgebraicGeometry.Compactification (c.overG ≫ c'.overI).left)
  (hd : IsPullback c.overG d.overI c'.overI d.overG)

instance : IsOpenImmersion (c.overI ≫ d.overI).left := by
  rw [Over.comp_left]
  infer_instance

/-- The triangle of factorizations `X ⟶[i] Z ⟶[p] Y`, `Y ⟶[j] Z' ⟶[q] S`,
`X ⟶[i ≫ i'] W ⟶[p' ≫ q] S` of compactifications `c = (i, p)`, `c' = (j, q)` and a
compactification `d = (i', p')` of `p ≫ j` with cartesian square. -/
noncomputable abbrev compShriekTriangle :
    ExchangeFormalism.ShriekTriangle SepFinType.openImmersion (SepFinType.mk X)
      (SepFinType.mk Y) (SepFinType.mk S) where
  Z₁ := SepFinType.mk c.overObj
  Z₂ := SepFinType.mk c'.overObj
  W := SepFinType.mk d.overObj
  i₁ := SepFinType.homMk c.overI
  p₁ := SepFinType.homMk c.overG
  i₂ := SepFinType.homMk c'.overI
  p₂ := SepFinType.homMk c'.overG
  i := SepFinType.homMk (c.overI ≫ d.overI)
  p := SepFinType.homMk (d.overG ≫ c'.overG)
  q := SepFinType.homMk d.overI
  r := SepFinType.homMk d.overG
  i_q := ObjectProperty.hom_ext _ rfl
  r_p := ObjectProperty.hom_ext _ rfl
  w := SepFinType.homMk_comp_homMk hd.w

/-- The base change map of the square of the triangle `compShriekTriangle` is an isomorphism. -/
lemma isIso_baseChange_compShriekTriangle :
    IsIso ((𝔽).baseChange (compShriekTriangle c c' d hd).p₁ (compShriekTriangle c c' d hd).q
      (compShriekTriangle c c' d hd).i₂ (compShriekTriangle c c' d hd).r
      (compShriekTriangle c c' d hd).w) :=
  isIso_baseChange_boundedConstructibleExchangeFormalism ℓ hd

/-- The exchange map of the square of the triangle `compShriekTriangle` is an isomorphism when
the exchange of `Rc'.overG_*` with the extension by zero along `d.overI` is. -/
lemma isIso_exchange_compShriekTriangle
    [IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
      ℓ hd)] :
    haveI := isIso_baseChange_compShriekTriangle ℓ c c' d hd
    IsIso ((𝔽).exchange (compShriekTriangle c c' d hd).p₁ (compShriekTriangle c c' d hd).q
      (compShriekTriangle c c' d hd).i₂ (compShriekTriangle c c' d hd).r
      (compShriekTriangle c c' d hd).w) := by
  have h : IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
      ℓ hd) := inferInstance
  rw [boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_eq_exchange] at h
  exact h

/-- The isomorphism `(i ≫ i')_! ⋙ R(p' ≫ q)_* ≅ (i_! ⋙ Rp_*) ⋙ (j_! ⋙ Rq_*)` in the definition of
the composition isomorphism of the lower shriek is the inverse of the composition isomorphism of
the triangle of factorizations. -/
lemma compShriekTriangle_compIso_symm
    [IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
      ℓ hd)] :
    haveI := isIso_baseChange_compShriekTriangle ℓ c c' d hd
    haveI := isIso_exchange_compShriekTriangle ℓ c c' d hd
    Functor.isoWhiskerRight
        (boundedConstructibleOpenImmersionLowerShriekComp _ ℓ c.overI d.overI) _ ≪≫
      Functor.isoWhiskerLeft _
        (boundedConstructibleLowerStarComp ℓ d.overG c'.overG).symm ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (asIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange ℓ hd)).symm _ ≪≫
        Functor.associator _ _ _) ≪≫
      (Functor.associator _ _ _).symm =
    ((𝔽).compIso (compShriekTriangle c c' d hd)).symm := by
  have := isIso_baseChange_compShriekTriangle ℓ c c' d hd
  have := isIso_exchange_compShriekTriangle ℓ c c' d hd
  have hp : (𝔽).pfComp' (SepFinType.homMk d.overG) (SepFinType.homMk c'.overG)
      (SepFinType.homMk (d.overG ≫ c'.overG)) (ObjectProperty.hom_ext _ rfl) =
      (𝔽).pfComp' (SepFinType.homMk d.overG) (SepFinType.homMk c'.overG)
        (SepFinType.homMk d.overG ≫ SepFinType.homMk c'.overG) rfl := rfl
  ext1
  rw [boundedConstructibleOpenImmersionLowerShriekComp_eq_shComp',
    boundedConstructibleLowerStarComp_eq_pfComp']
  simp only [boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_eq_exchange]
  exact congrArg Iso.hom (Functor.compIso_symm_aux _ _ _)

end Chosen



section TriangleOf

variable (c : AlgebraicGeometry.Compactification f.left)
  (c' : AlgebraicGeometry.Compactification g.left)
  (d : AlgebraicGeometry.Compactification (c.overG ≫ c'.overI).left)
  (hd : IsPullback c.overG d.overI c'.overI d.overG)

/-- The triangle of compactifications attached to compactifications `c = (i, p)` of `f`,
`c' = (j, q)` of `g` and a compactification `d = (i', p')` of `p ≫ j` with cartesian square: the
compactification `X ⟶[i ≫ i'] W ⟶[p' ≫ q] S` of `f ≫ g` (`Compactification.overComp`). -/
noncomputable abbrev triangleOfCompactifications :
    AlgebraicGeometry.Compactification.Triangle f.left g.left where
  cf := c
  cg := c'
  cfg := c.overComp c' d
  q := d.i
  p := d.g
  i_q := rfl
  p_g := rfl
  isPullback := hd.map (Over.forget _)

/-- The base change map of the square of a triangle of compactifications is an isomorphism. -/
lemma isIso_baseChange_triangleShriekTriangle
    (T : AlgebraicGeometry.Compactification.Triangle f.left g.left) :
    IsIso ((𝔽).baseChange (triangleShriekTriangle T).p₁ (triangleShriekTriangle T).q
      (triangleShriekTriangle T).i₂ (triangleShriekTriangle T).r
      (triangleShriekTriangle T).w) :=
  isIso_baseChange_boundedConstructibleExchangeFormalism ℓ
    (Compactification.Triangle.isPullback_over T)

/-- The exchange map of the square of a triangle of compactifications is an isomorphism
(proper base change for extension by zero). -/
lemma isIso_exchange_triangleShriekTriangle
    (T : AlgebraicGeometry.Compactification.Triangle f.left g.left) :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ T
    IsIso ((𝔽).exchange (triangleShriekTriangle T).p₁ (triangleShriekTriangle T).q
      (triangleShriekTriangle T).i₂ (triangleShriekTriangle T).r
      (triangleShriekTriangle T).w) := by
  have h := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    (Compactification.Triangle.isPullback_over T)
  rw [boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_eq_exchange] at h
  exact h

end TriangleOf


section OfData

variable (c : AlgebraicGeometry.Compactification f.left)
  (c' : AlgebraicGeometry.Compactification g.left)
  (d : AlgebraicGeometry.Compactification (c.overG ≫ c'.overI).left)
  (hd : IsPullback c.overG d.overI c'.overI d.overG)

/-- The morphism of triangles of factorizations from the triangle of the composite
compactification to the triangle with middle object `d.Z`, along the identification of the
middle objects. -/
noncomputable abbrev triangleShriekTriangleHomCompShriekTriangle :
    ExchangeFormalism.ShriekTriangle.Hom SepFinType.openImmersion
      (triangleShriekTriangle (triangleOfCompactifications c c' d hd))
      (compShriekTriangle c c' d hd) where
  rf := 𝟙 _
  rg := 𝟙 _
  rfg := SepFinType.homMk (AlgebraicGeometry.Compactification.overCompObjIso c c' d).hom
  wf := by simp
  hf := by simp
  wg := by simp
  hg := by simp
  wfg := ObjectProperty.hom_ext _ (by
    simp only [Category.id_comp, ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom]
    exact (AlgebraicGeometry.Compactification.overI_overCompObjIso_hom c c' d).symm)
  hfg := ObjectProperty.hom_ext _ (by
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom]
    exact AlgebraicGeometry.Compactification.overCompObjIso_hom_overG c c' d)
  q_comm := ObjectProperty.hom_ext _ (Over.OverMorphism.ext (by
    simp [AlgebraicGeometry.Compactification.overCompObjIso]))
  p_comm := ObjectProperty.hom_ext _ (Over.OverMorphism.ext (by
    simp [AlgebraicGeometry.Compactification.overCompObjIso]))


/-- The isomorphism `R(f ≫ g)_! ≅ Rf_!^c ⋙ Rg_!^{c'}` of compactifications `c`, `c'` and `d` is
the comparison with the composite compactification followed by the inverse of the composition
isomorphism of the triangle of factorizations. -/
lemma boundedConstructibleLowerShriekCompOfCompactifications_padicAlgCl_hom_eq :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ (triangleOfCompactifications c c' d hd)
    haveI := isIso_exchange_triangleShriekTriangle ℓ (triangleOfCompactifications c c' d hd)
    (boundedConstructibleLowerShriekCompOfCompactifications_padicAlgCl ℓ f g c c' d hd).hom =
      (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ
          (compactificationOverField (f ≫ g)) (c.overComp c' d)).hom ≫
        ((𝔽).compIso (triangleShriekTriangle (triangleOfCompactifications c c' d hd))).inv := by
  have := isIso_baseChange_triangleShriekTriangle ℓ (triangleOfCompactifications c c' d hd)
  have := isIso_exchange_triangleShriekTriangle ℓ (triangleOfCompactifications c c' d hd)
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicAlgCl ℓ hd
  have := isIso_baseChange_compShriekTriangle ℓ c c' d hd
  have := isIso_exchange_compShriekTriangle ℓ c c' d hd
  have e := AlgebraicGeometry.Compactification.overCompObjIso c c' d
  have h1 : IsIso ((𝔽).baseChange (𝟙 (SepFinType.mk X)) (SepFinType.homMk c.overI)
      (SepFinType.homMk c.overI) (𝟙 _)
      (triangleShriekTriangleHomCompShriekTriangle c c' d hd).wf) :=
    isIso_baseChange_boundedConstructibleExchangeFormalism ℓ
      (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback (𝟙 X) c.overI c.overI (𝟙 _))
  have h2 : IsIso ((𝔽).baseChange (𝟙 (SepFinType.mk Y)) (SepFinType.homMk c'.overI)
      (SepFinType.homMk c'.overI) (𝟙 _)
      (triangleShriekTriangleHomCompShriekTriangle c c' d hd).wg) :=
    isIso_baseChange_boundedConstructibleExchangeFormalism ℓ
      (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback (𝟙 Y) c'.overI c'.overI (𝟙 _))
  have h3 : IsIso ((𝔽).baseChange (𝟙 (SepFinType.mk X)) (SepFinType.homMk (c.overComp c' d).overI)
      (SepFinType.homMk (c.overI ≫ d.overI))
      (SepFinType.homMk (AlgebraicGeometry.Compactification.overCompObjIso c c' d).hom)
      (triangleShriekTriangleHomCompShriekTriangle c c' d hd).wfg) :=
    isIso_baseChange_boundedConstructibleExchangeFormalism ℓ
      (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback (𝟙 X) (c.overComp c' d).overI
        (c.overI ≫ d.overI) (AlgebraicGeometry.Compactification.overCompObjIso c c' d).hom)
  have h4 : IsIso ((𝔽).baseChange (𝟙 (SepFinType.mk c.overObj))
      (SepFinType.homMk (Compactification.Triangle.overQ (triangleOfCompactifications c c' d hd)))
      (SepFinType.homMk d.overI)
      (SepFinType.homMk (AlgebraicGeometry.Compactification.overCompObjIso c c' d).hom)
      (triangleShriekTriangleHomCompShriekTriangle c c' d hd).q_comm) :=
    isIso_baseChange_boundedConstructibleExchangeFormalism ℓ
      (IsPullback.of_horiz_isIso ⟨Over.OverMorphism.ext (by
        simp [AlgebraicGeometry.Compactification.overCompObjIso,
          Compactification.Triangle.overQ])⟩ :
        IsPullback (𝟙 c.overObj)
          (Compactification.Triangle.overQ (triangleOfCompactifications c c' d hd)) d.overI
          (AlgebraicGeometry.Compactification.overCompObjIso c c' d).hom)
  have h5 : IsIso ((𝔽).baseChange (SepFinType.homMk c.overG)
      (SepFinType.homMk (Compactification.Triangle.overQ (triangleOfCompactifications c c' d hd)))
      (SepFinType.homMk c'.overI)
      (SepFinType.homMk (Compactification.Triangle.overP (triangleOfCompactifications c c' d hd)) ≫
        𝟙 _)
      (triangleShriekTriangleHomCompShriekTriangle c c' d hd).big_w) :=
    isIso_baseChange_boundedConstructibleExchangeFormalism ℓ
      (by simpa using
        Compactification.Triangle.isPullback_over (triangleOfCompactifications c c' d hd))
  have nat := (𝔽).compIso_naturality (triangleShriekTriangleHomCompShriekTriangle c c' d hd)
  rw [ExchangeFormalism.refinementComparison_id, ExchangeFormalism.refinementComparison_id] at nat
  have hid : ∀ {A B C : Type _} [Category A] [Category B] [Category C] (F₁ : A ⥤ B) (F₂ : B ⥤ C),
      NatTrans.hcomp (𝟙 F₁) (𝟙 F₂) = 𝟙 (F₁ ⋙ F₂) := fun _ _ ↦ by ext; simp
  rw [hid, Category.id_comp] at nat
  have sqe : IsPullback (𝟙 X) (c.overComp c' d).overI (c.overI ≫ d.overI)
      (AlgebraicGeometry.Compactification.overCompObjIso c c' d).hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have : IsProper (AlgebraicGeometry.Compactification.overCompObjIso c c' d).hom.left := by
    simp only [AlgebraicGeometry.Compactification.overCompObjIso, Over.isoMk_hom_left,
      Iso.refl_hom]
    infer_instance
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl ℓ sqe
  have hρ := boundedConstructibleLowerShriekRefinementIso_hom_eq ℓ sqe
      (AlgebraicGeometry.Compactification.overCompObjIso_hom_overG c c' d)
  have key : (𝔽).compIso (triangleShriekTriangle (triangleOfCompactifications c c' d hd)) =
      (𝔽).compIso (compShriekTriangle c c' d hd) ≪≫
        boundedConstructibleLowerShriekRefinementIso ℓ sqe
          (AlgebraicGeometry.Compactification.overCompObjIso_hom_overG c c' d) := by
    ext1
    rw [Iso.trans_hom, hρ]
    exact nat.symm
  unfold boundedConstructibleLowerShriekCompOfCompactifications_padicAlgCl
  dsimp only
  rw [compShriekTriangle_compIso_symm, key]
  simp

end OfData


section HomConv

variable {T' T : AlgebraicGeometry.Compactification.Triangle f.left g.left} (φ : T'.Hom T)

/-- The refinement of the compactifications of `f` of a morphism of triangles, in `Over S`. -/
noncomputable abbrev triangleHomOverRf :
    AlgebraicGeometry.Compactification.OverRefinement T'.cf T.cf :=
  AlgebraicGeometry.Compactification.overRefinementOfRefinement φ.rf φ.isPullback_rf.flip

/-- The refinement of the compactifications of `g` of a morphism of triangles, in `Over S`. -/
noncomputable abbrev triangleHomOverRg :
    AlgebraicGeometry.Compactification.OverRefinement T'.cg T.cg :=
  AlgebraicGeometry.Compactification.overRefinementOfRefinement φ.rg φ.isPullback_rg.flip

/-- The refinement of the compactifications of `f ≫ g` of a morphism of triangles, in
`Over S`. -/
noncomputable abbrev triangleHomOverRfg :
    AlgebraicGeometry.Compactification.OverRefinement (Compactification.Triangle.overCfg T')
      (Compactification.Triangle.overCfg T) :=
  AlgebraicGeometry.Compactification.overRefinementOfRefinement (f := f ≫ g) φ.rfg
    φ.isPullback_rfg.flip

/-- A morphism of triangles of compactifications as a morphism of triangles of factorizations. -/
noncomputable abbrev triangleShriekTriangleHom :
    ExchangeFormalism.ShriekTriangle.Hom SepFinType.openImmersion (triangleShriekTriangle T')
      (triangleShriekTriangle T) where
  rf := SepFinType.homMk (triangleHomOverRf φ).hom
  rg := SepFinType.homMk (triangleHomOverRg φ).hom
  rfg := SepFinType.homMk (triangleHomOverRfg φ).hom
  wf := SepFinType.homMk_comp_homMk (a := 𝟙 X) (triangleHomOverRf φ).isPullback.w
  hf := ObjectProperty.hom_ext _ (triangleHomOverRf φ).hom_overG
  wg := SepFinType.homMk_comp_homMk (a := 𝟙 Y) (triangleHomOverRg φ).isPullback.w
  hg := ObjectProperty.hom_ext _ (triangleHomOverRg φ).hom_overG
  wfg := SepFinType.homMk_comp_homMk (a := 𝟙 X) (triangleHomOverRfg φ).isPullback.w
  hfg := ObjectProperty.hom_ext _ (triangleHomOverRfg φ).hom_overG
  q_comm := ObjectProperty.hom_ext _ (Over.OverMorphism.ext φ.q_comm)
  p_comm := ObjectProperty.hom_ext _ (Over.OverMorphism.ext φ.p_comm)

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom]
  [QuasiCompact S.hom] [IsSeparated S.hom] in
/-- The square of the maps `q` of a morphism of triangles is cartesian, in `Over S`. -/
lemma isPullback_triangleHom_q :
    IsPullback (triangleHomOverRf φ).hom (Compactification.Triangle.overQ T')
      (Compactification.Triangle.overQ T) (triangleHomOverRfg φ).hom :=
  IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext φ.q_comm) φ.isPullback_q

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom]
  [QuasiCompact S.hom] [IsSeparated S.hom] in
/-- For a morphism of triangles `T' ⟶ T`, the square of `T'` with `p` followed by the refinement
of `T.cg` is cartesian, in `Over S`. -/
lemma isPullback_triangleHom_big :
    IsPullback T'.cf.overG (Compactification.Triangle.overQ T') T.cg.overI
      (Compactification.Triangle.overP T' ≫ (triangleHomOverRg φ).hom) :=
  IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext φ.isPullback_big.w) φ.isPullback_big

include φ in
include φ in
/-- **Naturality of the composition isomorphisms of triangles of compactifications**: for a
morphism of triangles `φ : T' ⟶ T`, the composition isomorphisms of `T` and `T'` are intertwined
by the comparison isomorphisms of the compactifications. -/
lemma compIso_triangleShriekTriangle_naturality :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ T
    haveI := isIso_exchange_triangleShriekTriangle ℓ T
    haveI := isIso_baseChange_triangleShriekTriangle ℓ T'
    haveI := isIso_exchange_triangleShriekTriangle ℓ T'
    ((𝔽).compIso (triangleShriekTriangle T)).hom ≫
        (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (Compactification.Triangle.overCfg T) (Compactification.Triangle.overCfg T')).hom =
      NatTrans.hcomp (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          T.cf T'.cf).hom
          (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ T.cg T'.cg).hom ≫
        ((𝔽).compIso (triangleShriekTriangle T')).hom := by
  have := isIso_baseChange_triangleShriekTriangle ℓ T
  have := isIso_exchange_triangleShriekTriangle ℓ T
  have := isIso_baseChange_triangleShriekTriangle ℓ T'
  have := isIso_exchange_triangleShriekTriangle ℓ T'
  have := (triangleHomOverRf φ).isProper
  have := (triangleHomOverRg φ).isProper
  have := (triangleHomOverRfg φ).isProper
  have := isIso_baseChange_boundedConstructibleExchangeFormalism_id
    ℓ (triangleHomOverRf φ).isPullback
  have := isIso_baseChange_boundedConstructibleExchangeFormalism_id
    ℓ (triangleHomOverRg φ).isPullback
  have := isIso_baseChange_boundedConstructibleExchangeFormalism_id
    ℓ (triangleHomOverRfg φ).isPullback
  have := isIso_baseChange_boundedConstructibleExchangeFormalism
    ℓ (isPullback_triangleHom_q φ)
  have : IsIso ((𝔽).baseChange (triangleShriekTriangle T').p₁ (triangleShriekTriangle T').q
      (triangleShriekTriangle T).i₂
      ((triangleShriekTriangle T').r ≫ (triangleShriekTriangleHom φ).rg)
      (triangleShriekTriangleHom φ).big_w) :=
    isIso_baseChange_boundedConstructibleExchangeFormalism
      ℓ (isPullback_triangleHom_big φ)
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    (triangleHomOverRf φ).isPullback
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    (triangleHomOverRg φ).isPullback
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    (triangleHomOverRfg φ).isPullback
  have nat := (𝔽).compIso_naturality (triangleShriekTriangleHom φ)
  rw [boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq ℓ (triangleHomOverRf φ),
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq ℓ (triangleHomOverRg φ),
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq ℓ (triangleHomOverRfg φ),
    boundedConstructibleLowerShriekRefinementIso'_hom_eq,
    boundedConstructibleLowerShriekRefinementIso'_hom_eq,
    boundedConstructibleLowerShriekRefinementIso'_hom_eq]
  exact nat
end HomConv

section ChosenTriangle

variable (f g)

/-- The triangle of compactifications defining the composition isomorphism
`boundedConstructibleLowerShriekComp_padicAlgCl`: the chosen compactifications `c` of `f` and `c'`
of `g`, and the composite compactification of `f ≫ g` attached to the chosen compactification `d`
of `p ≫ j` with cartesian square. -/
noncomputable def chosenTriangle : AlgebraicGeometry.Compactification.Triangle f.left g.left where
  cf := compactificationOverField f
  cg := compactificationOverField g
  cfg := (compactificationOverField f).overComp (compactificationOverField g)
    (AlgebraicGeometry.Compactification.exists_isPullback_overG_overI
      (compactificationOverField f) (compactificationOverField g)).choose
  q := (AlgebraicGeometry.Compactification.exists_isPullback_overG_overI
      (compactificationOverField f) (compactificationOverField g)).choose.i
  p := (AlgebraicGeometry.Compactification.exists_isPullback_overG_overI
      (compactificationOverField f) (compactificationOverField g)).choose.g
  i_q := rfl
  p_g := rfl
  isPullback := (AlgebraicGeometry.Compactification.exists_isPullback_overG_overI
      (compactificationOverField f) (compactificationOverField g)).choose_spec.map (Over.forget _)


end ChosenTriangle


section AnyTriangle

/-- The inverse composition maps of two triangles agree after comparison with a common
compactification. Keeping both triangles arbitrary avoids unfolding chosen compactifications
in the common-refinement argument. -/
private lemma compIso_triangleShriekTriangle_inv_comparison
    [QuasiCompact f.left] [QuasiCompact g.left] [QuasiCompact (f.left ≫ g.left)]
    (c : Compactification (f ≫ g).left)
    (T₀ T : Compactification.Triangle f.left g.left) :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ T₀
    haveI := isIso_exchange_triangleShriekTriangle ℓ T₀
    haveI := isIso_baseChange_triangleShriekTriangle ℓ T
    haveI := isIso_exchange_triangleShriekTriangle ℓ T
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
        c (Compactification.Triangle.overCfg T₀)).hom ≫
        ((𝔽).compIso (triangleShriekTriangle T₀)).inv =
      (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          c (Compactification.Triangle.overCfg T)).hom ≫
        ((𝔽).compIso (triangleShriekTriangle T)).inv ≫
        NatTrans.hcomp (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          T.cf T₀.cf).hom
          (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ T.cg T₀.cg).hom := by
  have := isIso_baseChange_triangleShriekTriangle ℓ T
  have := isIso_exchange_triangleShriekTriangle ℓ T
  obtain ⟨T'', ⟨φ₁⟩, ⟨φ₂⟩⟩ : ∃ T'' : AlgebraicGeometry.Compactification.Triangle f.left g.left,
      Nonempty (T''.Hom T₀) ∧ Nonempty (T''.Hom T) :=
    ⟨T₀.inf T, ⟨T₀.infFst T⟩, ⟨T₀.infSnd T⟩⟩
  have := isIso_baseChange_triangleShriekTriangle ℓ T₀
  have := isIso_exchange_triangleShriekTriangle ℓ T₀
  have := isIso_baseChange_triangleShriekTriangle ℓ T''
  have := isIso_exchange_triangleShriekTriangle ℓ T''
  have n₁ := compIso_triangleShriekTriangle_naturality ℓ φ₁
  have n₂ := compIso_triangleShriekTriangle_naturality ℓ φ₂
  refine Iso.trans_symm_eq_of_comm ((𝔽).compIso (triangleShriekTriangle T₀))
    ((𝔽).compIso (triangleShriekTriangle T)) ((𝔽).compIso (triangleShriekTriangle T''))
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
      (Compactification.Triangle.overCfg T₀) (Compactification.Triangle.overCfg T''))
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
      (Compactification.Triangle.overCfg T) (Compactification.Triangle.overCfg T''))
    (NatIso.hcomp (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ T₀.cf
      T''.cf) (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ T₀.cg
      T''.cg))
    (NatIso.hcomp (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ T.cf
      T''.cf) (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ T.cg
      T''.cg))
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
      c (Compactification.Triangle.overCfg T₀))
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
      c (Compactification.Triangle.overCfg T))
    (NatIso.hcomp (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ T.cf
      T₀.cf) (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ T.cg
      T₀.cg)) n₁ n₂ ?_ ?_
  · exact congrArg Iso.hom
      ((boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_trans ℓ _ _ _).trans
        (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_trans ℓ _ _ _).symm)
  · exact (NatTrans.exchange _ _ _ _).symm.trans (congrArg₂ NatTrans.hcomp
      (congrArg Iso.hom (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_trans ℓ
        _ _ _))
      (congrArg Iso.hom (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_trans ℓ
        _ _ _)))

variable (f g)

/-- **The composition isomorphism of the lower shriek is computed by any triangle of
compactifications** `T` of `f` and `g`: it is the comparison with the compactification
`T.cfg` of `f ≫ g`, followed by the inverse of the composition isomorphism of `T` and the
comparisons of `T.cf` and `T.cg` with the chosen compactifications (blueprint
`proposition-composition-base-change-rf-shriek--1`, independence of the compactifications). -/
theorem boundedConstructibleLowerShriekComp_padicAlgCl_hom_eq_triangle
    (T : AlgebraicGeometry.Compactification.Triangle f.left g.left) :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ T
    haveI := isIso_exchange_triangleShriekTriangle ℓ T
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom =
      (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          (compactificationOverField (f ≫ g)) (Compactification.Triangle.overCfg T)).hom ≫
        ((𝔽).compIso (triangleShriekTriangle T)).inv ≫
        NatTrans.hcomp (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
          T.cf (compactificationOverField f)).hom
          (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
            T.cg (compactificationOverField g)).hom := by
  have : QuasiCompact (f.left ≫ g.left) := by
    have : QuasiCompact ((f ≫ g).left ≫ S.hom) := by
      rw [Over.w]
      infer_instance
    exact .of_comp _ S.hom
  have : QuasiCompact f.left := by
    have : QuasiCompact (f.left ≫ Y.hom) := by
      rw [Over.w]
      infer_instance
    exact .of_comp _ Y.hom
  have : QuasiCompact g.left := by
    have : QuasiCompact (g.left ≫ S.hom) := by
      rw [Over.w]
      infer_instance
    exact .of_comp _ S.hom
  have hd := (AlgebraicGeometry.Compactification.exists_isPullback_overG_overI
    (compactificationOverField f) (compactificationOverField g)).choose_spec
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicAlgCl ℓ hd
  have := isIso_baseChange_triangleShriekTriangle ℓ T
  have := isIso_exchange_triangleShriekTriangle ℓ T
  rw [boundedConstructibleLowerShriekComp_padicAlgCl_eq,
    boundedConstructibleLowerShriekCompOfCompactifications_padicAlgCl_hom_eq,
    boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_eq']
  let T₀ := triangleOfCompactifications (compactificationOverField f) (compactificationOverField g)
    _ hd
  exact compIso_triangleShriekTriangle_inv_comparison ℓ
    (compactificationOverField (f ≫ g)) T₀ T

end AnyTriangle

end AlgebraicGeometry.ProEtale.CondensedRing
