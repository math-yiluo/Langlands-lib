/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.ProjectionFormulaShiftBoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulated
public import WeilConjectures.TraceFormula.TraceClassAdditivity
public import WeilConjectures.TraceFormula.TraceClassDiagonal
public import WeilConjectures.TraceFormula.SourceExchangeKunnethAux

/-!

# Naturality of supported classes and of the evaluation kernel

Let `X, Y` be separated `k`-schemes of finite type. This file records the functoriality of the
external product `M ⊠ N = Lp_X^* M ⊗ Lp_Y^* N` in both variables
(`ProEtale.CondensedRing.externalProductMap`, `ProEtale.CondensedRing.externalProductLeft`), the
naturality of the Künneth–Verdier map `κ_{M,N}` in `N` along the Verdier dual
`D_Y g = RHom(g, ω_Y)` of `g : N' ⟶ N` (`ProEtale.CondensedRing.verdierDualMap`)
(`ProEtale.CondensedRing.kunnethVerdierMap_naturality_right`), and, for an endocorrespondence
`c = (C, c₁, c₂, u)` of `(X, K)`:

* the *supported class* `κ_{K₁,K₂}⁻¹ ∘ [w] : Rc_! ℚ̄_ℓ,C ⟶ K₁ ⊠ D_X K₂` of a coefficient map
  `w : Lc₂^* K₂ ⟶ Rc₁^! K₁` with two coefficient objects
  (`ProEtale.CondensedRing.Correspondence.supportedClassOfCoeff`), natural in `K₁` and `K₂`;
* the dinaturality of the evaluation kernel `e_K : K ⊠ D_X K ⟶ RΔ_* ω_X` in `K`
  (`ProEtale.CondensedRing.externalProductMap_comp_evaluationKernel`);
* the trace class as the image of `e_K ∘ ũ` under an additive map
  `Hom(Rc_! ℚ̄_ℓ,C, RΔ_* ω_X) →+ Hom(ℚ̄_ℓ,Fix(c), ω_Fix(c))`
  (`ProEtale.CondensedRing.Correspondence.FixedLocus.traceClassOfKernel`,
  `ProEtale.CondensedRing.Correspondence.traceClass_eq_traceClassOfKernel`), following blueprint
  `lem-trf-trace-class-diagonal-pairing`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### Functoriality of the external product -/

section ExternalProduct

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The external product `f ⊠ g = Lp_X^* f ⊗ Lp_Y^* g : M ⊠ N ⟶ M' ⊠ N'` of two morphisms. -/
noncomputable def externalProductMap {M M' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {N N' : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (f : M ⟶ M') (g : N ⟶ N') :
    externalProduct ℓ M N ⟶ externalProduct ℓ M' N' :=
  (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).map f ⊗ₘ
    (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).map g

variable {M M' M'' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {N N' N'' : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

@[simp]
lemma externalProductMap_id :
    externalProductMap ℓ (𝟙 M) (𝟙 N) = 𝟙 (externalProduct ℓ M N) := by
  simp [externalProductMap, externalProduct]

@[reassoc]
lemma externalProductMap_comp (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N'') :
    externalProductMap ℓ (f ≫ f') (g ≫ g') =
      externalProductMap ℓ f g ≫ externalProductMap ℓ f' g' := by
  rw [externalProductMap, externalProductMap, externalProductMap, Functor.map_comp,
    Functor.map_comp, tensorHom_comp_tensorHom]

lemma externalProductMap_id_right (f : M ⟶ M') :
    externalProductMap ℓ f (𝟙 N) =
      (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).map f ▷ _ := by
  simp [externalProductMap, externalProduct]

lemma externalProductMap_id_left (g : N ⟶ N') :
    externalProductMap ℓ (𝟙 M) g =
      _ ◁ (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).map g := by
  simp [externalProductMap, externalProduct]

/-- The two variables of the external product commute. -/
@[reassoc]
lemma externalProductMap_exchange (f : M ⟶ M') (g : N ⟶ N') :
    externalProductMap ℓ f (𝟙 N) ≫ externalProductMap ℓ (𝟙 M') g =
      externalProductMap ℓ (𝟙 M) g ≫ externalProductMap ℓ f (𝟙 N') := by
  rw [← externalProductMap_comp, ← externalProductMap_comp]
  simp

@[simp]
lemma externalProductMap_zero_right (f : M ⟶ M') :
    externalProductMap ℓ f (0 : N ⟶ N') = 0 := by
  simp [externalProductMap, externalProduct]

@[simp]
lemma externalProductMap_zero_left (g : N ⟶ N') :
    externalProductMap ℓ (0 : M ⟶ M') g = 0 := by
  simp [externalProductMap, externalProduct]

lemma externalProductMap_add_right (f : M ⟶ M') (g g' : N ⟶ N') :
    externalProductMap ℓ f (g + g') = externalProductMap ℓ f g + externalProductMap ℓ f g' := by
  simp [externalProductMap, externalProduct, MonoidalPreadditive.tensor_add]

lemma externalProductMap_add_left (f f' : M ⟶ M') (g : N ⟶ N') :
    externalProductMap ℓ (f + f') g = externalProductMap ℓ f g + externalProductMap ℓ f' g := by
  simp [externalProductMap, externalProduct, MonoidalPreadditive.add_tensor]

variable (X) in
/-- The external product with a fixed object `N` on `Y`, as a functor
`- ⊠ N = Lp_X^* (-) ⊗ Lp_Y^* N : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(X ⨯ Y)⟦ℚ̲̄_ℓ⟧`. -/
noncomputable def externalProductLeft (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc((X ⨯ Y).left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X) ⋙
    (curriedTensor _).flip.obj ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj N)

noncomputable instance (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (externalProductLeft ℓ X N).CommShift ℤ := by
  delta externalProductLeft
  infer_instance

instance (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (externalProductLeft ℓ X N).IsTriangulated := by
  delta externalProductLeft
  infer_instance

@[simp]
lemma externalProductLeft_obj (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (externalProductLeft ℓ X N).obj M = externalProduct ℓ M N :=
  rfl

@[simp]
lemma externalProductLeft_map (f : M ⟶ M') :
    (externalProductLeft ℓ X N).map f = externalProductMap ℓ f (𝟙 N) := by
  rw [externalProductMap_id_right]
  rfl

end ExternalProduct

/-! ### Functoriality of the Verdier dual -/

section VerdierDual

variable {X : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The Verdier dual `D_X g = RHom(g, ω_X) : D_X N ⟶ D_X N'` of a morphism `g : N' ⟶ N`. -/
noncomputable def verdierDualMap {N N' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (g : N' ⟶ N) : verdierDual ℓ N ⟶ verdierDual ℓ N' :=
  (pre g).app (dualizingComplex ℓ X)

lemma verdierDualMap_eq {N N' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (g : N' ⟶ N) : verdierDualMap ℓ g = (pre g).app (dualizingComplex ℓ X) :=
  rfl

end VerdierDual

/-! ### Naturality of the Künneth–Verdier map in the second variable -/

section KunnethVerdier

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The computation behind `kunnethVerdierPairing_naturality_right`, for abstract objects. -/
private lemma kunnethVerdierPairing_naturality_right_aux {𝒞 : Type*} [Category 𝒞]
    [MonoidalCategory 𝒞] [BraidedCategory 𝒞] (PM : 𝒞) {A A' B B' C₁ C₁' C₀ T : 𝒞}
    (a : A' ⟶ A) (b : B ⟶ B') (m₁ : A ⊗ B ⟶ C₁) (m₂ : C₁ ⟶ C₀) (m₁' : A' ⊗ B' ⟶ C₁')
    (m₂' : C₁' ⟶ C₀) (e : PM ⊗ C₀ ⟶ T) (h : A' ◁ b ≫ m₁' ≫ m₂' = a ▷ B ≫ m₁ ≫ m₂) :
    A' ◁ (PM ◁ b) ≫ ((α_ A' PM B').inv ≫ (β_ A' PM).hom ▷ B' ≫ (α_ PM A' B').hom ≫
        PM ◁ m₁' ≫ PM ◁ m₂' ≫ e) =
      a ▷ (PM ⊗ B) ≫ ((α_ A PM B).inv ≫ (β_ A PM).hom ▷ B ≫ (α_ PM A B).hom ≫
        PM ◁ m₁ ≫ PM ◁ m₂ ≫ e) := by
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc, associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc, BraidedCategory.braiding_naturality_left,
    comp_whiskerRight_assoc, associator_naturality_middle_assoc]
  simp only [← whiskerLeft_comp_assoc, h]

/-- The image under a lax monoidal functor of the dinaturality of the evaluation. -/
private lemma lax_whiskerLeft_map_pre_comp_ev {𝒞 𝒟 : Type*} [Category 𝒞] [MonoidalCategory 𝒞]
    [MonoidalClosed 𝒞] [Category 𝒟] [MonoidalCategory 𝒟] (F : 𝒞 ⥤ 𝒟) [F.LaxMonoidal]
    {N N' : 𝒞} (g : N' ⟶ N) (ω : 𝒞) :
    F.obj N' ◁ F.map ((pre g).app ω) ≫ Functor.LaxMonoidal.μ F N' ((ihom N').obj ω) ≫
        F.map ((ihom.ev N').app ω) =
      F.map g ▷ F.obj ((ihom N).obj ω) ≫ Functor.LaxMonoidal.μ F N ((ihom N).obj ω) ≫
        F.map ((ihom.ev N).app ω) := by
  rw [Functor.LaxMonoidal.μ_natural_right_assoc, Functor.LaxMonoidal.μ_natural_left_assoc,
    ← Functor.map_comp, ← Functor.map_comp, id_tensor_pre_app_comp_ev]

/-- The Künneth–Verdier pairing is natural in `N`. -/
lemma kunnethVerdierPairing_naturality_right (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {N N' : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (g : N' ⟶ N) :
    _ ◁ externalProductMap ℓ (𝟙 M) (verdierDualMap ℓ g) ≫
        kunnethVerdierPairing ℓ M N' =
      (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).map g ▷ _ ≫
        kunnethVerdierPairing ℓ M N := by
  rw [externalProductMap_id_left]
  refine kunnethVerdierPairing_naturality_right_aux _ _ _ _ _ _ _ _ ?_
  exact lax_whiskerLeft_map_pre_comp_ev _ g _

/-- Curried morphisms of pairings related by a dinaturality square are related by a
dinaturality square. -/
private lemma curry_pre_naturality_aux {𝒞 : Type*} [Category 𝒞] [MonoidalCategory 𝒞]
    [MonoidalClosed 𝒞] {A A' B B' T : 𝒞} (a : A' ⟶ A) (x : B ⟶ B') {p : A ⊗ B ⟶ T}
    {p' : A' ⊗ B' ⟶ T} (h : A' ◁ x ≫ p' = a ▷ B ≫ p) :
    x ≫ curry p' = curry p ≫ (pre a).app T := by
  rw [← curry_natural_left, curry_pre_app, h]

/-- The Künneth–Verdier map `κ_{M,N}` is natural in `N`: for `g : N' ⟶ N`,
`κ_{M,N'} ∘ (1 ⊠ D_Y g) = RHom(Lp_Y^* g, 1) ∘ κ_{M,N}`. -/
@[reassoc]
lemma kunnethVerdierMap_naturality_right (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {N N' : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (g : N' ⟶ N) :
    externalProductMap ℓ (𝟙 M) (verdierDualMap ℓ g) ≫
        kunnethVerdierMap ℓ M N' =
      kunnethVerdierMap ℓ M N ≫
        (pre ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).map g)).app _ := by
  exact curry_pre_naturality_aux _ _ (kunnethVerdierPairing_naturality_right ℓ M g)

/-- The Künneth–Verdier map `κ_{M,N}` is natural in `M`, in terms of `externalProductMap`. -/
@[reassoc]
lemma kunnethVerdierMap_naturality_left' {M M' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (f : M ⟶ M') (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    externalProductMap ℓ f (𝟙 _) ≫ kunnethVerdierMap ℓ M' N =
      kunnethVerdierMap ℓ M N ≫
        (ihom _).map ((boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).map f) := by
  rw [externalProductMap_id_right, kunnethVerdierMap_naturality_left]

/-- The inverse Künneth–Verdier map is natural in `M`. -/
@[reassoc]
lemma inv_kunnethVerdierMap_naturality_left' {M M' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (f : M ⟶ M') (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (ihom _).map ((boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).map f) ≫
        inv (kunnethVerdierMap ℓ M' N) =
      inv (kunnethVerdierMap ℓ M N) ≫ externalProductMap ℓ f (𝟙 _) := by
  rw [IsIso.eq_inv_comp, ← kunnethVerdierMap_naturality_left'_assoc, IsIso.hom_inv_id,
    Category.comp_id]

/-- The inverse Künneth–Verdier map is natural in `N`. -/
@[reassoc]
lemma inv_kunnethVerdierMap_naturality_right (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {N N' : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (g : N' ⟶ N) :
    (pre ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).map g)).app _ ≫
        inv (kunnethVerdierMap ℓ M N') =
      inv (kunnethVerdierMap ℓ M N) ≫
        externalProductMap ℓ (𝟙 M) (verdierDualMap ℓ g) := by
  rw [IsIso.eq_inv_comp, ← kunnethVerdierMap_naturality_right_assoc, IsIso.hom_inv_id,
    Category.comp_id]

end KunnethVerdier

/-! ### Dinaturality of the evaluation kernel -/

section Evaluation

variable {X C : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]

/-- The exceptional pullback along equal morphisms commutes with the identification
`eqToHom`. -/
@[reassoc]
lemma boundedConstructibleUpperShriek_map_comp_eqToHom {a b : C ⟶ X} (h : a = b)
    {K K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (f : K ⟶ K') :
    (boundedConstructibleUpperShriek ℓ a).map f ≫ eqToHom (by rw [h]) =
      eqToHom (by rw [h]) ≫ (boundedConstructibleUpperShriek ℓ b).map f := by
  subst h
  simp

/-- The identification `LΔ^* Lp^* ≅ 𝟭` for a projection `p` with `Δ ≫ p = 𝟙` is natural. -/
private lemma diag_upperStar_upperStar_naturality (p : X ⨯ X ⟶ X) (h : diag X ≫ p = 𝟙 X)
    {K K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (f : K ⟶ K') :
    (boundedConstructibleUpperStar _ ℓ (diag X)).map ((boundedConstructibleUpperStar _ ℓ p).map f) ≫
        (((boundedConstructibleUpperStarComp _ ℓ (diag X) p).app K').symm ≪≫
          eqToIso (by rw [h]) ≪≫ (boundedConstructibleUpperStarId _ ℓ X).app K').hom =
      (((boundedConstructibleUpperStarComp _ ℓ (diag X) p).app K).symm ≪≫
          eqToIso (by rw [h]) ≪≫ (boundedConstructibleUpperStarId _ ℓ X).app K).hom ≫ f := by
  have h1 := (boundedConstructibleUpperStarComp _ ℓ (diag X) p).inv.naturality f
  have h3 := (boundedConstructibleUpperStarId _ ℓ X).hom.naturality f
  rw [Functor.comp_map] at h1
  rw [Functor.id_map] at h3
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom, eqToIso.hom, Category.assoc]
  rw [reassoc_of% h1, upperStar_map_comp_eqToHom_congrArg_assoc ℓ _ h, h3]

/-- The naturality of `G (A ⊗ B) ≅ G A ⊗ G B ≅ K ⊗ N` for a monoidal functor `G`, given the
naturality of the identifications `G A ≅ K` and `G B ≅ N`. -/
private lemma map_tensorHom_comp_μIso_symm_trans_tensorIso {𝒞 𝒟 : Type*} [Category 𝒞]
    [MonoidalCategory 𝒞] [Category 𝒟] [MonoidalCategory 𝒟] (G : 𝒞 ⥤ 𝒟) [G.Monoidal]
    {A A' B B' : 𝒞} {K K' N N' : 𝒟} (a : A ⟶ A') (b : B ⟶ B') (f : K ⟶ K') (g : N ⟶ N')
    (eA : G.obj A ≅ K) (eA' : G.obj A' ≅ K') (eB : G.obj B ≅ N) (eB' : G.obj B' ≅ N')
    (ha : G.map a ≫ eA'.hom = eA.hom ≫ f) (hb : G.map b ≫ eB'.hom = eB.hom ≫ g) :
    G.map (a ⊗ₘ b) ≫ ((Functor.Monoidal.μIso G A' B').symm ≪≫ tensorIso eA' eB').hom =
      ((Functor.Monoidal.μIso G A B).symm ≪≫ tensorIso eA eB).hom ≫ (f ⊗ₘ g) := by
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom, tensorIso_hom, tensorIso_hom,
    Functor.Monoidal.μIso_inv, Functor.Monoidal.μIso_inv, ← Functor.OplaxMonoidal.δ_natural_assoc,
    Category.assoc, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, ha, hb]

/-- The identification `LΔ^* (K ⊠ N) ≅ K ⊗ N` is natural in `K` and `N`. -/
@[reassoc]
lemma diagUpperStarExternalProductIso_hom_naturality₂
    {K K' N N' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (f : K ⟶ K') (g : N ⟶ N') :
    (boundedConstructibleUpperStar _ ℓ (diag X)).map (externalProductMap ℓ f g) ≫
        (diagUpperStarExternalProductIso ℓ K' N').hom =
      (diagUpperStarExternalProductIso ℓ K N).hom ≫ (f ⊗ₘ g) :=
  map_tensorHom_comp_μIso_symm_trans_tensorIso _ _ _ f g _ _ _ _
    (diag_upperStar_upperStar_naturality ℓ _ (by rw [diag, prod.lift_fst]) f)
    (diag_upperStar_upperStar_naturality ℓ _ (by rw [diag, prod.lift_snd]) g)

/-- The dinaturality of the evaluation, in tensor product form. -/
private lemma tensorHom_id_comp_ev {𝒞 : Type*} [Category 𝒞] [MonoidalCategory 𝒞]
    [MonoidalClosed 𝒞] {K K' : 𝒞} (f : K' ⟶ K) (ω : 𝒞) :
    (f ⊗ₘ 𝟙 ((ihom K).obj ω)) ≫ (ihom.ev K).app ω =
      (𝟙 K' ⊗ₘ (pre f).app ω) ≫ (ihom.ev K').app ω := by
  rw [tensorHom_id, id_tensorHom, id_tensor_pre_app_comp_ev]

/-- The dinaturality of the evaluation against the dualizing complex. -/
private lemma tensorHom_id_comp_ev_verdierDual
    {K K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (f : K' ⟶ K) :
    (f ⊗ₘ 𝟙 (verdierDual ℓ K)) ≫ (ihom.ev K).app (dualizingComplex' ℓ X) =
      (𝟙 K' ⊗ₘ verdierDualMap ℓ f) ≫ (ihom.ev K').app (dualizingComplex' ℓ X) :=
  tensorHom_id_comp_ev f _

/-- **Dinaturality of the evaluation kernel**: for `f : K' ⟶ K`, the two maps
`K' ⊠ D_X K ⟶ RΔ_* ω_X` given by `e_K ∘ (f ⊠ 1)` and `e_{K'} ∘ (1 ⊠ D_X f)` agree. -/
@[reassoc]
lemma externalProductMap_comp_evaluationKernel
    {K K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (f : K' ⟶ K) :
    externalProductMap ℓ f (𝟙 _) ≫ evaluationKernel ℓ K =
      externalProductMap ℓ (𝟙 K') (verdierDualMap ℓ f) ≫
        evaluationKernel ℓ K' := by
  rw [evaluationKernel, evaluationKernel, ← Adjunction.homEquiv_naturality_left,
    ← Adjunction.homEquiv_naturality_left, diagUpperStarExternalProductIso_hom_naturality₂_assoc,
    diagUpperStarExternalProductIso_hom_naturality₂_assoc]
  congr 2
  exact tensorHom_id_comp_ev_verdierDual ℓ f

end Evaluation

/-! ### Supported classes with two coefficient objects -/

namespace Correspondence

variable {ℓ} {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (c : Correspondence ℓ K)

/-- The *supported class* `κ_{K₁,K₂}⁻¹ ∘ [w] : Rc_! ℚ̄_ℓ,C ⟶ K₁ ⊠ D_X K₂` of a coefficient map
`w : Lc₂^* K₂ ⟶ Rc₁^! K₁` with two coefficient objects on the support of `c` (blueprint
`lem-trf-trace-class-diagonal-pairing`, Step 1): the class of `w`, read through
`Lc₂^* = Lc^* Lp₂^*` and `Rc₁^! = Rc^! Rp₁^!`, followed by the inverse Künneth–Verdier map. -/
noncomputable def supportedClassOfCoeff (K₁ K₂ : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (w : (boundedConstructibleUpperStar _ ℓ c.c₂).obj K₂ ⟶
      (boundedConstructibleUpperShriek ℓ c.c₁).obj K₁) :
    (boundedConstructibleLowerShriek ℓ c.support).obj (𝟙_ _) ⟶
      externalProduct ℓ K₁ (verdierDual ℓ K₂) :=
  (correspondenceClassEquiv ℓ c.support K₂ K₁).symm
      (eqToHom (by rw [support_snd]) ≫ w ≫ eqToHom (by rw [support_fst])) ≫
    inv (kunnethVerdierMap ℓ K₁ K₂)

/-- The supported class of the coefficient map `u` of `c` is the supported class of `c`. -/
lemma supportedClassOfCoeff_u : c.supportedClassOfCoeff K K c.u = c.supportedClass := by
  rw [supportedClass_eq, supportedClassOfCoeff]
  refine congrArg (· ≫ inv (kunnethVerdierMap ℓ K K)) ?_
  simp only [correspondenceClassEquiv, Equiv.coe_fn_symm_mk, Iso.trans_inv, Iso.trans_hom,
    eqToIso.inv, eqToIso.hom, Iso.app_inv, Iso.app_hom, Category.assoc]

/-- The supported class of the correspondence with the support of `c` and the coefficient map
`u'`. -/
lemma supportedClass_withCoeff (K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (u' : (boundedConstructibleUpperStar _ ℓ c.c₂).obj K' ⟶
      (boundedConstructibleUpperShriek ℓ c.c₁).obj K') :
    (c.withCoeff K' u').supportedClass = c.supportedClassOfCoeff K' K' u' :=
  ((c.withCoeff K' u').supportedClassOfCoeff_u).symm

/-- Composites `x ≫ i` and `(y ≫ i') ≫ n` agree if `x = y ≫ m` and `m ≫ i = i' ≫ n`. -/
private lemma comp_eq_comp_comp_of_eq {𝒞 : Type*} [Category 𝒞] {A B B' C C' : 𝒞} {x : A ⟶ B}
    {y : A ⟶ B'} {m : B' ⟶ B} {i : B ⟶ C} {i' : B' ⟶ C'} {n : C' ⟶ C} (hx : x = y ≫ m)
    (hi : m ≫ i = i' ≫ n) : x ≫ i = (y ≫ i') ≫ n := by
  rw [hx, Category.assoc, hi, Category.assoc]

/-- The supported class is natural in the first coefficient object. -/
lemma supportedClassOfCoeff_comp_upperShriek_map
    {K₁ K₁' K₂ : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (w : (boundedConstructibleUpperStar _ ℓ c.c₂).obj K₂ ⟶
      (boundedConstructibleUpperShriek ℓ c.c₁).obj K₁) (f : K₁ ⟶ K₁') :
    c.supportedClassOfCoeff K₁' K₂ (w ≫ (boundedConstructibleUpperShriek ℓ c.c₁).map f) =
      c.supportedClassOfCoeff K₁ K₂ w ≫ externalProductMap ℓ f (𝟙 _) := by
  unfold supportedClassOfCoeff
  refine comp_eq_comp_comp_of_eq ?_ (inv_kunnethVerdierMap_naturality_left' ℓ f K₂)
  rw [Equiv.symm_apply_eq, correspondenceClassEquiv_naturality_right, Equiv.apply_symm_apply,
    Category.assoc, Category.assoc, Category.assoc,
    boundedConstructibleUpperShriek_map_comp_eqToHom ℓ (support_fst c).symm]

/-- The supported class is natural in the second coefficient object. -/
lemma supportedClassOfCoeff_upperStar_map_comp
    {K₁ K₂ K₂' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (w : (boundedConstructibleUpperStar _ ℓ c.c₂).obj K₂ ⟶
      (boundedConstructibleUpperShriek ℓ c.c₁).obj K₁) (g : K₂' ⟶ K₂) :
    c.supportedClassOfCoeff K₁ K₂' ((boundedConstructibleUpperStar _ ℓ c.c₂).map g ≫ w) =
      c.supportedClassOfCoeff K₁ K₂ w ≫
        externalProductMap ℓ (𝟙 K₁) (verdierDualMap ℓ g) := by
  unfold supportedClassOfCoeff
  refine comp_eq_comp_comp_of_eq ?_ (inv_kunnethVerdierMap_naturality_right ℓ K₁ g)
  rw [Equiv.symm_apply_eq, correspondenceClassEquiv_naturality_left, Equiv.apply_symm_apply,
    Category.assoc, upperStar_map_comp_eqToHom_congrArg_assoc ℓ _ (support_snd c)]

/-! ### The trace class through the evaluation kernel -/

namespace FixedLocus

variable {c} (F : c.FixedLocus)

/-- The additive map `Hom(Rc_! ℚ̄_ℓ,C, RΔ_* ω_X) ⟶ Hom(ℚ̄_ℓ,Fix(c), ω_Fix(c))` through which the
trace class factors (blueprint `lem-trf-trace-class-diagonal-pairing`, Step 2): a kernel
`φ : Rc_! ℚ̄_ℓ,C ⟶ RΔ_* ω_X` goes to the exceptional adjoint along `d` of
`Rd_! Lι^* ℚ̄_ℓ,C ≅ LΔ^* Rc_! ℚ̄_ℓ,C ⟶ ω_X`, the inverse of base change in the fixed square
followed by the adjoint of `φ`. -/
noncomputable def traceClassOfKernel :
    ((boundedConstructibleLowerShriek ℓ c.support).obj (𝟙_ _) ⟶
        (boundedConstructibleLowerStar ℓ (diag X)).obj (dualizingComplex' ℓ X)) →+
      BorelMooreSection ℓ F.F where
  toFun φ := (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ F.ι)).hom ≫
    (boundedConstructibleUpperShriekAdjunction ℓ F.d).homEquiv _ _
      (F.lowerShriekBaseChangeIso.inv.app (𝟙_ _) ≫
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X)).homEquiv _ _).symm φ) ≫
    (dualizingComplexComp ℓ F.d).hom
  map_zero' := by
    simp [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit]
  map_add' φ ψ := by
    simp [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit]

lemma traceClassOfKernel_apply
    (φ : (boundedConstructibleLowerShriek ℓ c.support).obj (𝟙_ _) ⟶
      (boundedConstructibleLowerStar ℓ (diag X)).obj (dualizingComplex' ℓ X)) :
    F.traceClassOfKernel φ = (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ F.ι)).hom ≫
      (boundedConstructibleUpperShriekAdjunction ℓ F.d).homEquiv _ _
        (F.lowerShriekBaseChangeIso.inv.app (𝟙_ _) ≫
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X)).homEquiv _ _).symm φ) ≫
      (dualizingComplexComp ℓ F.d).hom :=
  rfl

end FixedLocus

/-- **The trace class through the evaluation kernel** (blueprint
`lem-trf-trace-class-diagonal-pairing`): `Tr_c(u)` is the image of `e_K ∘ ũ` under
`FixedLocus.traceClassOfKernel`, `ũ` the supported class of `u`. -/
theorem traceClass_eq_traceClassOfKernel (F : c.FixedLocus) :
    c.traceClass F = F.traceClassOfKernel (c.supportedClass ≫ evaluationKernel ℓ K) := by
  rw [FixedLocus.traceClassOfKernel_apply, evaluationKernel,
    Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  exact traceClass_eq_homEquiv F

/-- The trace class with the coefficient map `u'` through the evaluation kernel of `K'`. -/
theorem FixedLocus.traceClassWithCoeff_eq {c : Correspondence ℓ K} (F : c.FixedLocus)
    (K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (u' : (boundedConstructibleUpperStar _ ℓ c.c₂).obj K' ⟶
      (boundedConstructibleUpperShriek ℓ c.c₁).obj K') :
    F.traceClassWithCoeff K' u' =
      F.traceClassOfKernel (c.supportedClassOfCoeff K' K' u' ≫ evaluationKernel ℓ K') := by
  rw [traceClassWithCoeff, traceClass_eq_traceClassOfKernel]
  exact congrArg F.traceClassOfKernel
    (congrArg (· ≫ evaluationKernel ℓ K') (supportedClass_withCoeff c K' u'))

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
