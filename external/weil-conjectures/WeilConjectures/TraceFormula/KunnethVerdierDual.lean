/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying
public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExternalIhom
public import WeilConjectures.CategoryTheory.Triangulated.IsoLocusContravariant
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.TraceFormula.KunnethVerdierShift

/-!
# The Künneth–Verdier map in the dualized variable

Let `p = p_X : X ⨯ Y ⟶ X` and `q = p_Y : X ⨯ Y ⟶ Y` be the projections, and
```
κ_{M,N} : Lp^* M ⊗ Lq^* D_Y N ⟶ RHom(Lq^* N, Rp^! M)
```
the Künneth–Verdier map (`ProEtale.CondensedRing.kunnethVerdierMap`). This file studies `κ_{M,N}`
as a function of `N`, in which it is contravariant.

* **Base case** (`ProEtale.CondensedRing.isIso_kunnethVerdierMap_of_exactPairing`): if `N` has a
  left dual and the exceptional Künneth map `α : M ⊠ ω_Y ⟶ Rp^! M` is an isomorphism, then `κ_{M,N}`
  is an isomorphism, since `κ = RHom(1, α) ∘ β` and the external Hom map `β` is an isomorphism for
  dualizable `N`.
* **Naturality** (`ProEtale.CondensedRing.kunnethVerdierMap_naturality_right_pre`): `κ_{M,N}` is
  natural in `N`.
* **Two out of three** (`ProEtale.CondensedRing.isIso_kunnethVerdierMap_of_triangEnvelope_right`):
  the objects `N` such that `κ_{M,N⟦n⟧}` is an isomorphism for all `n` form a triangulated
  subcategory closed under retracts. No compatibility of `κ` with the shifts in `N` is used:
  for every test object `T'`, both `N ↦ Hom(M ⊠ D_Y N, T')` and `N ↦ Hom(RHom(Lq^* N, Rp^! M), T')`
  are, by Verdier biduality (`isIso_verdierBiduality`), naturally isomorphic to homological
  functors `Hom(A, F N)` with `F` triangulated, and the five lemma applies
  (`CategoryTheory.NatTrans.isTriangulated_shiftIsoLocusOp`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite

open scoped CategoryTheory.Functor CategoryTheory.Obj

/-! ### Generic lemmas on closed monoidal categories -/

namespace CategoryTheory

/-- The opposite of a functor preserving zero morphisms preserves zero morphisms. -/
instance Functor.preservesZeroMorphisms_op {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    F.op.PreservesZeroMorphisms where
  map_zero X Y := by rw [Functor.op_map, unop_zero, F.map_zero, op_zero]

/-- The external Hom map of `CategoryTheory.externalHomMap` is the external internal-hom map
`CategoryTheory.MonoidalClosed.externalIhomMap`. -/
lemma externalHomMap_eq_externalIhomMap {C₁ C₂ C : Type*} [Category* C₁] [MonoidalCategory C₁]
    [MonoidalClosed C₁] [Category* C₂] [MonoidalCategory C₂] [MonoidalClosed C₂] [Category* C]
    [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C] (P : C₁ ⥤ C) (Q : C₂ ⥤ C)
    [P.Monoidal] [Q.LaxMonoidal] (E₁ L₁ : C₁) (E₂ L₂ : C₂) :
    externalHomMap P Q E₁ L₁ E₂ L₂ = MonoidalClosed.externalIhomMap P Q E₁ L₁ E₂ L₂ := by
  rw [externalHomMap, externalHomPairing, MonoidalClosed.externalIhomMap,
    tensorHom_comp_tensorHom]

namespace MonoidalClosed

variable {𝒞 : Type*} [Category* 𝒞] [MonoidalCategory 𝒞] [MonoidalClosed 𝒞]

/-- Precomposition with an isomorphism is an isomorphism. -/
lemma isIso_pre_app_of_isIso {A B : 𝒞} (f : B ⟶ A) [IsIso f] (Z : 𝒞) :
    IsIso ((pre f).app Z) :=
  ⟨(pre (inv f)).app Z, by rw [← NatTrans.comp_app, ← pre_map, IsIso.inv_hom_id, pre_id]; rfl,
    by rw [← NatTrans.comp_app, ← pre_map, IsIso.hom_inv_id, pre_id]; rfl⟩

/-- The internal uncurrying `[y', [x, z]] ⟶ [x ⊗ y', z]` is natural in `y'`. -/
@[reassoc]
lemma pre_app_comp_ihomUncurry (x : 𝒞) {y y' : 𝒞} (g : y ⟶ y') (z : 𝒞) :
    (pre g).app ((ihom x).obj z) ≫ ihomUncurry x y z =
      ihomUncurry x y' z ≫ (pre (x ◁ g)).app z := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_ihomUncurry, uncurry_pre_app, uncurry_ihomUncurry,
    associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    id_tensor_pre_app_comp_ev, MonoidalCategory.whiskerLeft_comp_assoc,
    associator_naturality_middle_assoc]

section Braided

variable [BraidedCategory 𝒞]

/-- The symmetry `Hom(A, [B, ω]) ≃ Hom(B, [A, ω])` of the pairings `A ⊗ B ⟶ ω`, through the
braiding. -/
noncomputable def homIhomSwap (ω A B : 𝒞) : (A ⟶ (ihom B).obj ω) ≃ (B ⟶ (ihom A).obj ω) where
  toFun f := curry ((β_ A B).hom ≫ uncurry f)
  invFun g := curry ((β_ A B).inv ≫ uncurry g)
  left_inv f := by simp
  right_inv g := by simp

lemma homIhomSwap_comp_left (ω : 𝒞) {A A' : 𝒞} (B : 𝒞) (a : A' ⟶ A)
    (f : A ⟶ (ihom B).obj ω) :
    homIhomSwap ω A' B (a ≫ f) = homIhomSwap ω A B f ≫ (pre a).app ω := by
  apply uncurry_injective
  simp only [homIhomSwap, Equiv.coe_fn_mk]
  rw [uncurry_curry, uncurry_pre_app, uncurry_curry, uncurry_natural_left,
    ← BraidedCategory.braiding_naturality_left_assoc]

lemma homIhomSwap_comp_pre (ω A : 𝒞) {B B' : 𝒞} (b : B' ⟶ B) (f : A ⟶ (ihom B).obj ω) :
    homIhomSwap ω A B' (f ≫ (pre b).app ω) = b ≫ homIhomSwap ω A B f := by
  apply uncurry_injective
  simp only [homIhomSwap, Equiv.coe_fn_mk]
  rw [uncurry_curry, uncurry_pre_app, uncurry_natural_left, uncurry_curry,
    BraidedCategory.braiding_naturality_right_assoc]

/-- In a braided category with zero morphisms whose functors `X ⊗ -` preserve zero morphisms,
`0 ▷ Z = 0`. -/
lemma zero_whiskerRight_of_braided [HasZeroMorphisms 𝒞] (X Y Z : 𝒞) :
    (0 : X ⟶ Y) ▷ Z = 0 := by
  have h : Z ◁ (0 : X ⟶ Y) = 0 := (tensorLeft Z).map_zero X Y
  rw [← cancel_mono (β_ Y Z).hom, BraidedCategory.braiding_naturality_left, h, comp_zero,
    zero_comp]

/-- Precomposition with the zero morphism is zero. -/
lemma pre_zero_app_of_braided [HasZeroMorphisms 𝒞] (A B Z : 𝒞) :
    (pre (0 : A ⟶ B)).app Z = 0 := by
  apply uncurry_injective
  have h : A ◁ (0 : (ihom B).obj Z ⟶ (ihom A).obj Z) = 0 := (tensorLeft A).map_zero _ _
  rw [uncurry_pre, zero_whiskerRight_of_braided, zero_comp, uncurry_eq, h, zero_comp]

/-- The contravariant functor `[-, ω]` preserves zero morphisms. -/
instance preservesZeroMorphisms_internalHom_flip_obj [HasZeroMorphisms 𝒞] (ω : 𝒞) :
    (internalHom.flip.obj ω).PreservesZeroMorphisms where
  map_zero X Y := pre_zero_app_of_braided (unop Y) (unop X) ω

variable (ω : 𝒞) [∀ K : 𝒞, IsIso (toIhomIhom ω K)]

/-- **Contravariant full faithfulness of the duality `D = [-, ω]`.** If all double-dual maps
`K ⟶ D D K` are isomorphisms, then `Hom(D N, W) ≃ Hom(D W, N)`. -/
noncomputable def dualHomEquiv (N W : 𝒞) : ((ihom N).obj ω ⟶ W) ≃ ((ihom W).obj ω ⟶ N) where
  toFun x := homIhomSwap ω _ _ (x ≫ toIhomIhom ω W) ≫ inv (toIhomIhom ω N)
  invFun y := (homIhomSwap ω _ _).symm (y ≫ toIhomIhom ω N) ≫ inv (toIhomIhom ω W)
  left_inv x := by simp
  right_inv y := by simp

/-- `dualHomEquiv` is natural in `N`. -/
lemma dualHomEquiv_comp {N N' : 𝒞} (g : N ⟶ N') (W : 𝒞) (x : (ihom N).obj ω ⟶ W) :
    dualHomEquiv ω N' W ((pre g).app ω ≫ x) = dualHomEquiv ω N W x ≫ g := by
  have key : (pre ((pre g).app ω)).app ω ≫ inv (toIhomIhom ω N') =
      inv (toIhomIhom ω N) ≫ g := by
    rw [IsIso.comp_inv_eq, Category.assoc, toIhomIhom_naturality, IsIso.inv_hom_id_assoc]
  simp only [dualHomEquiv, Equiv.coe_fn_mk]
  rw [Category.assoc, homIhomSwap_comp_left, Category.assoc, key, Category.assoc]

/-- `dualHomEquiv.symm` is natural in `N`. -/
lemma dualHomEquiv_symm_comp {N N' : 𝒞} (g : N ⟶ N') (W : 𝒞) (y : (ihom W).obj ω ⟶ N) :
    (dualHomEquiv ω N' W).symm (y ≫ g) = (pre g).app ω ≫ (dualHomEquiv ω N W).symm y := by
  rw [Equiv.symm_apply_eq, dualHomEquiv_comp, Equiv.apply_symm_apply]

end Braided

end MonoidalClosed

open MonoidalClosed Pretriangulated

/-- **Homological functors from biduality.** Let `F : C ⥤ D'` be a triangulated functor to a
braided monoidal closed category with an object `ω` for which all double-dual maps are
isomorphisms, and let `G ⊣ H`. A functor `S : Cᵒᵖ ⥤ E` with `S N ≅ G [F N, ω]` naturally in `N`
satisfies `IsHomExact`: `Hom(G [F N, ω], T') ≃ Hom([F N, ω], H T') ≃ Hom([H T', ω], F N)`. -/
lemma Functor.isHomExact_of_biduality {C D' E : Type*} [Category* C] [Category* D']
    [Category* E] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [HasZeroObject D'] [HasShift D' ℤ]
    [Preadditive D'] [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
    [MonoidalCategory D'] [MonoidalClosed D'] [BraidedCategory D'] [Preadditive E]
    (ω : D') [∀ K : D', IsIso (toIhomIhom ω K)] (F : C ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    {G : D' ⥤ E} {H : E ⥤ D'} (adj : G ⊣ H) (S : Cᵒᵖ ⥤ E) [S.PreservesZeroMorphisms]
    (φ : ∀ N : C, S.obj (op N) ≅ G.obj ((ihom (F.obj N)).obj ω))
    (hφ : ∀ {N N' : C} (f : N ⟶ N'),
      S.map f.op ≫ (φ N).hom = (φ N').hom ≫ G.map ((pre (F.map f)).app ω)) :
    S.IsHomExact :=
  Functor.IsHomExact.mk_of_homEquiv S F (fun T' ↦ (ihom (H.obj T')).obj ω)
    (fun T' N ↦ ((dualHomEquiv ω (F.obj N) (H.obj T')).symm.trans
      (adj.homEquiv _ _).symm).trans ((φ N).symm.homCongr (Iso.refl T')))
    (fun T' N N' f x ↦ by
      simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom,
        Category.comp_id, dualHomEquiv_symm_comp,
        Adjunction.homEquiv_naturality_left_symm, ← reassoc_of% (hφ f)])

end CategoryTheory

/-! ### Generic lemmas for the naturality in `N` -/

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Generic

/-- Dinaturality of the evaluation through a lax monoidal functor. -/
private lemma whiskerLeft_map_pre_comp_μ_comp_map_ev {𝒞 𝒟 : Type*} [Category* 𝒞]
    [Category* 𝒟] [MonoidalCategory 𝒞] [MonoidalClosed 𝒞] [MonoidalCategory 𝒟] (Q : 𝒞 ⥤ 𝒟)
    [Q.LaxMonoidal] {N N' : 𝒞} (g : N ⟶ N') (ω : 𝒞) :
    Q.obj N ◁ Q.map ((pre g).app ω) ≫ Functor.LaxMonoidal.μ Q N ((ihom N).obj ω) ≫
        Q.map ((ihom.ev N).app ω) =
      Q.map g ▷ Q.obj ((ihom N').obj ω) ≫ Functor.LaxMonoidal.μ Q N' ((ihom N').obj ω) ≫
        Q.map ((ihom.ev N').app ω) := by
  rw [Functor.LaxMonoidal.μ_natural_right_assoc, ← Q.map_comp, id_tensor_pre_app_comp_ev,
    Q.map_comp, Functor.LaxMonoidal.μ_natural_left_assoc]

/-- Dinaturality of the rearranged pairing of the Künneth–Verdier map, for abstract objects. -/
private lemma pairing_dinaturality {𝒞 : Type*} [Category* 𝒞] [MonoidalCategory 𝒞]
    [BraidedCategory 𝒞] {A A' Pm B B' W₁ W₁' W₂ Z : 𝒞} (u : A ⟶ A') (v : B' ⟶ B)
    (m₁ : A ⊗ B ⟶ W₁) (m₂ : W₁ ⟶ W₂) (m₁' : A' ⊗ B' ⟶ W₁') (m₂' : W₁' ⟶ W₂)
    (a : Pm ⊗ W₂ ⟶ Z) (h : A ◁ v ≫ m₁ ≫ m₂ = u ▷ B' ≫ m₁' ≫ m₂') :
    A ◁ (Pm ◁ v) ≫ ((α_ A Pm B).inv ≫ (β_ A Pm).hom ▷ B ≫ (α_ Pm A B).hom ≫ Pm ◁ m₁ ≫
        Pm ◁ m₂ ≫ a) =
      u ▷ (Pm ⊗ B') ≫ ((α_ A' Pm B').inv ≫ (β_ A' Pm).hom ▷ B' ≫ (α_ Pm A' B').hom ≫
        Pm ◁ m₁' ≫ Pm ◁ m₂' ≫ a) := by
  have key : A ◁ (Pm ◁ v) ≫ (α_ A Pm B).inv ≫ (β_ A Pm).hom ▷ B ≫ (α_ Pm A B).hom =
      (α_ A Pm B').inv ≫ (β_ A Pm).hom ▷ B' ≫ (α_ Pm A B').hom ≫ Pm ◁ (A ◁ v) := by
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
      associator_naturality_right]
  have key' : u ▷ (Pm ⊗ B') ≫ (α_ A' Pm B').inv ≫ (β_ A' Pm).hom ▷ B' ≫ (α_ Pm A' B').hom =
      (α_ A Pm B').inv ≫ (β_ A Pm).hom ▷ B' ≫ (α_ Pm A B').hom ≫ Pm ◁ (u ▷ B') := by
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc,
      BraidedCategory.braiding_naturality_left, comp_whiskerRight_assoc,
      associator_naturality_middle]
  rw [reassoc_of% key, reassoc_of% key']
  simp only [← MonoidalCategory.whiskerLeft_comp_assoc, h]

/-- The identification `RHom(A, P) ⟶ RHom(A, [x, z]) ≅ RHom(x ⊗ A, z)` along `δ : P ⟶ [x, z]` is
natural in `A`. -/
private lemma ihom_map_comp_ihomUncurry_naturality {𝒞 : Type*} [Category* 𝒞]
    [MonoidalCategory 𝒞] [MonoidalClosed 𝒞] (x z : 𝒞) {A A' P : 𝒞} (δ : P ⟶ (ihom x).obj z)
    (g : A ⟶ A') :
    (pre g).app P ≫ (ihom A).map δ ≫ ihomUncurry x A z =
      ((ihom A').map δ ≫ ihomUncurry x A' z) ≫ (pre (x ◁ g)).app z := by
  rw [← NatTrans.naturality_assoc, Category.assoc, pre_app_comp_ihomUncurry]

/-- Curried pairings related by a dinaturality square are related by a naturality square. -/
private lemma curry_dinaturality {𝒞 : Type*} [Category* 𝒞] [MonoidalCategory 𝒞]
    [MonoidalClosed 𝒞] {A A' S S' Z : 𝒞} (u : A ⟶ A') (s : S ⟶ S') (p : A ⊗ S' ⟶ Z)
    (p' : A' ⊗ S ⟶ Z) (h : A ◁ s ≫ p = u ▷ S ≫ p') :
    s ≫ curry p = curry p' ≫ (pre u).app Z := by
  rw [← curry_natural_left, h, curry_pre_app]

end Generic

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-! ### The base case -/

/-- **The Künneth–Verdier map for dualizable `N`** (the base case of the dévissage in `N` of the
proof of blueprint `lemma-external-duality-trace-morphism--1`): if `N` has a left dual `N'` and the
exceptional Künneth map `α : M ⊠ ω_Y ⟶ Rp^! M` is an isomorphism, then `κ_{M,N}` is an isomorphism,
as `κ = RHom(1, α) ∘ β` and the external Hom map `β` is an isomorphism for dualizable `N`. -/
theorem isIso_kunnethVerdierMap_of_exactPairing (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N N' : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) [ExactPairing N' N]
    [IsIso (exceptionalKunnethMap ℓ (Y := Y) M)] : IsIso (kunnethVerdierMap ℓ M N) := by
  have := MonoidalClosed.isIso_externalIhomMap_of_exactPairing
    (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X))
    (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)) (𝟙_ _) (𝟙_ _) M N' N
    (dualizingComplex' ℓ Y)
  have := isIso_pre_app_of_isIso (unitExternalMap
    (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X))
    (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)) N)
    ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M ⊗
      (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj (dualizingComplex' ℓ Y))
  rw [kunnethVerdierMap_eq, externalHomMap_eq_externalIhomMap]
  infer_instance

/-! ### Naturality in `N` -/

/-- **The Künneth–Verdier map is natural in `N`**: for `g : N ⟶ N'`, the square
```
M ⊠ D_Y N' ──── κ_{M,N'} ────▶ RHom(Lq^* N', Rp^! M)
     │                                 │
 1 ⊠ D_Y g                     RHom(Lq^* g, 1)
     ▼                                 ▼
M ⊠ D_Y N ───── κ_{M,N} ─────▶ RHom(Lq^* N, Rp^! M)
```
commutes. -/
@[reassoc]
lemma kunnethVerdierMap_naturality_right_pre (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {N N' : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (g : N ⟶ N') :
    (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M ◁
        (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).map
          ((pre g).app (dualizingComplex' ℓ Y)) ≫ kunnethVerdierMap ℓ M N =
      kunnethVerdierMap ℓ M N' ≫
        (pre ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).map g)).app
          ((boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M) :=
  curry_dinaturality _ _ _ _ (pairing_dinaturality _ _ _ _ _ _ _
    (whiskerLeft_map_pre_comp_μ_comp_map_ev _ g _))

/-! ### Two out of three in `N` -/

variable (Y) in
/-- The source `N ↦ M ⊠ D_Y N = Lp^* M ⊗ Lq^* D_Y N` of the Künneth–Verdier map, as a functor of
`N ∈ Dᵇc(Y)⟦ℚ̄_ℓ⟧ᵒᵖ`. -/
noncomputable def kunnethVerdierSource (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)ᵒᵖ ⥤
      Dᵇc((X ⨯ Y).left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  internalHom.flip.obj (dualizingComplex' ℓ Y) ⋙
    boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y) ⋙
      (curriedTensor _).obj ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M)

variable (Y) in
/-- The target `N ↦ RHom(Lq^* N, Rp^! M)` of the Künneth–Verdier map, as a functor of
`N ∈ Dᵇc(Y)⟦ℚ̄_ℓ⟧ᵒᵖ`. -/
noncomputable def kunnethVerdierTarget (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)ᵒᵖ ⥤
      Dᵇc((X ⨯ Y).left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).op ⋙
    internalHom.flip.obj ((boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M)

variable (Y) in
/-- The Künneth–Verdier map `κ_{M,N}`, as a natural transformation in `N ∈ Dᵇc(Y)⟦ℚ̄_ℓ⟧ᵒᵖ`. -/
@[simps]
noncomputable def kunnethVerdierNatTransRight (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    kunnethVerdierSource ℓ Y M ⟶ kunnethVerdierTarget ℓ Y M where
  app N := kunnethVerdierMap ℓ M N.unop
  naturality _ _ f := kunnethVerdierMap_naturality_right_pre ℓ M f.unop

instance (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (kunnethVerdierSource ℓ Y M).PreservesZeroMorphisms := by
  have : ((curriedTensor _).obj
      ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M)).IsLeftAdjoint :=
    ⟨_, ⟨boundedConstructibleTensorIhomAdjunction _⟩⟩
  have h₁ : (internalHom.flip.obj (dualizingComplex' ℓ Y)).PreservesZeroMorphisms :=
    preservesZeroMorphisms_internalHom_flip_obj _
  have h₂ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (prod.snd : X ⨯ Y ⟶ Y)).PreservesZeroMorphisms := inferInstance
  have h₃ : ((curriedTensor _).obj
      ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have h₄ := Functor.preservesZeroMorphisms_comp
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (prod.snd : X ⨯ Y ⟶ Y))
    ((curriedTensor _).obj ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M))
  exact Functor.preservesZeroMorphisms_comp _ _

instance (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (kunnethVerdierTarget ℓ Y M).PreservesZeroMorphisms := by
  exact Functor.preservesZeroMorphisms_comp _ _

instance (Z : Over (Spec (.of k))) [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] (K : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (toIhomIhom (dualizingComplex' ℓ Z) K) :=
  isIso_verdierBiduality ℓ K

/-- `Hom(M ⊠ D_Y N, T') ≃ Hom(D_Y Rq_* RHom(Lp^* M, T'), N)`, by the tensor-hom adjunction, the
adjunction `Lq^* ⊣ Rq_*` and biduality on `Y`. -/
instance isHomExact_kunnethVerdierSource (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (kunnethVerdierSource ℓ Y M).IsHomExact :=
  Functor.isHomExact_of_biduality (dualizingComplex' ℓ Y) (𝟭 _)
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ (prod.snd : X ⨯ Y ⟶ Y)).comp
      (boundedConstructibleTensorIhomAdjunction
        ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M)))
    _ (fun _ ↦ Iso.refl _) (fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm)

/-- `Hom(RHom(Lq^* N, P), T') ≃ Hom(D T', D P ⊗ Lq^* N)` with `P = Rp^! M` and `D` the Verdier
dual of `X ⨯ Y`, by biduality `P ≅ D D P`, `RHom(A, D B) ≅ D(B ⊗ A)` and biduality on `X ⨯ Y`. -/
instance isHomExact_kunnethVerdierTarget (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (kunnethVerdierTarget ℓ Y M).IsHomExact :=
  Functor.isHomExact_of_biduality (dualizingComplex' ℓ (X ⨯ Y))
    (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y) ⋙ (curriedTensor _).obj
      ((ihom ((boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M)).obj
        (dualizingComplex' ℓ (X ⨯ Y))))
    (Adjunction.id) _
    (fun _ ↦ (ihom _).mapIso (asIso (toIhomIhom (dualizingComplex' ℓ (X ⨯ Y))
      ((boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M))) ≪≫
        (ihomCurryIso _ _ _).symm)
    (fun _ ↦ ihom_map_comp_ihomUncurry_naturality _ _ _ _)

/-- **Dévissage in `N` for the Künneth–Verdier map**: if `κ_{M,N⟦n⟧}` is an isomorphism for all
shifts of the objects `N` of a class `P`, then `κ_{M,N}` is an isomorphism for every `N` in the
triangulated envelope of `P`. -/
lemma isIso_kunnethVerdierMap_of_triangEnvelope_right
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {P : ObjectProperty (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)}
    (h : ∀ N, P N → ∀ n : ℤ, IsIso (kunnethVerdierMap ℓ M (N⟦n⟧)))
    {N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (hN : P.triangEnvelope N) :
    IsIso (kunnethVerdierMap ℓ M N) :=
  (kunnethVerdierNatTransRight ℓ Y M).isIso_app_op_of_triangEnvelope h hN

/-- **Two out of three in `N` for the Künneth–Verdier map**: for a distinguished triangle
`N₁ ⟶ N₂ ⟶ N₃ ⟶ N₁[1]` of `Dᵇc(Y)⟦ℚ̄_ℓ⟧`, if `κ_{M,N₁⟦n⟧}` and `κ_{M,N₃⟦n⟧}` are isomorphisms for
all `n`, so are the `κ_{M,N₂⟦n⟧}`. -/
lemma isIso_kunnethVerdierMap_of_distinguished_right
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (T : Pretriangulated.Triangle (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))
    (hT : T ∈ Pretriangulated.distinguishedTriangles)
    (h₁ : ∀ n : ℤ, IsIso (kunnethVerdierMap ℓ M (T.obj₁⟦n⟧)))
    (h₃ : ∀ n : ℤ, IsIso (kunnethVerdierMap ℓ M (T.obj₃⟦n⟧))) (n : ℤ) :
    IsIso (kunnethVerdierMap ℓ M (T.obj₂⟦n⟧)) :=
  ObjectProperty.ext_of_isTriangulatedClosed₂
    (kunnethVerdierNatTransRight ℓ Y M).shiftIsoLocusOp T hT h₁ h₃ n

end AlgebraicGeometry.ProEtale.CondensedRing
