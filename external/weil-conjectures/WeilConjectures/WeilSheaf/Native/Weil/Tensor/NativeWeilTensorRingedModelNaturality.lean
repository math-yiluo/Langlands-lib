/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedModel

/-! # Naturality of the explicit native one-K-flat model

Source: Stacks 06YU, 0FPT and the representative step of native tensor transport.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local irreducible] Functor.mapDerivedCategory

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (b : NativeWeilTensorRingedBridge k₀ l X)
  [HasDerivedCategory.{u + 2} (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)]
  (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X)
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
  (adj : T ⊣₂ ihomBifunctor k₀ l X)
  (A : NativeWeilRingedTensorComplexes b T adj)
  (SB : CoefficientClosedStructure
    (derivedInternalHomOfUniverses.{u + 1, u + 1, u + 1, u + 2} b.J b.R))
  (TB : CoefficientTensorModels.{u + 1, u + 1, u + 1, u + 2} b.J b.R SB)
  (βB : @SymmetricCategory _ _ SB.monoidal)
  (cB : RingedDerivedTensorCoherence b.J b.R SB TB βB)

private theorem mapped_square {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y X' Y' : C} {a : X ⟶ Y} {b : X' ⟶ Y'}
    {f : X ⟶ X'} {g : Y ⟶ Y'} (h : f ≫ b = a ≫ g) :
    F.map f ≫ F.map b = F.map a ≫ F.map g := by
  rw [← F.map_comp, ← F.map_comp, h]

private theorem mapped_prod_square {C D E : Type*}
    [Category C] [Category D] [Category E] (F : C × D ⥤ E)
    {X Y X' Y' : C} {Z W Z' W' : D}
    {a : X ⟶ Y} {b : X' ⟶ Y'} {c : Z ⟶ W} {d : Z' ⟶ W'}
    {f : X ⟶ X'} {g : Y ⟶ Y'} {h : Z ⟶ Z'} {i : W ⟶ W'}
    (hc : f ≫ b = a ≫ g) (hd : h ≫ d = c ≫ i) :
    F.map (Prod.mkHom f h) ≫ F.map (Prod.mkHom b d) =
      F.map (Prod.mkHom a c) ≫ F.map (Prod.mkHom g i) := by
  apply mapped_square
  exact Prod.hom_ext hc hd

private theorem inverse_square {C : Type*} [Category C] {A B A' B' : C}
    (e : A ≅ B) (e' : A' ≅ B') (f : A ⟶ A') (g : B ⟶ B')
    (h : f ≫ e'.hom = e.hom ≫ g) : g ≫ e'.inv = e.inv ≫ f := by
  calc
    g ≫ e'.inv = e.inv ≫ (e.hom ≫ g) ≫ e'.inv := by simp
    _ = e.inv ≫ (f ≫ e'.hom) ≫ e'.inv := by rw [h]
    _ = e.inv ≫ f := by simp

private theorem four_squares {C : Type*} [Category C]
    {A0 A1 A2 A3 A4 B0 B1 B2 B3 B4 : C}
    {a1 : A0 ⟶ A1} {b1 : B0 ⟶ B1} {a2 : A1 ⟶ A2} {b2 : B1 ⟶ B2}
    {a3 : A2 ⟶ A3} {b3 : B2 ⟶ B3} {a4 : A3 ⟶ A4} {b4 : B3 ⟶ B4}
    {f0 : A0 ⟶ B0} {f1 : A1 ⟶ B1} {f2 : A2 ⟶ B2}
    {f3 : A3 ⟶ B3} {f4 : A4 ⟶ B4}
    (h1 : f0 ≫ b1 = a1 ≫ f1) (h2 : f1 ≫ b2 = a2 ≫ f2)
    (h3 : f2 ≫ b3 = a3 ≫ f3) (h4 : f3 ≫ b4 = a4 ≫ f4) :
    f0 ≫ b1 ≫ b2 ≫ b3 ≫ b4 = a1 ≫ a2 ≫ a3 ≫ a4 ≫ f4 := by
  rw [reassoc_of% h1, reassoc_of% h2, reassoc_of% h3, h4]

/-- Naturality of the explicit transported model in both representative complexes.
Source: Stacks 06YU, 0FPT
(blueprint: lem-sf-native-weil-tensor-ringed-model-naturality). -/
theorem nativeWeilRingedTensorModel_naturality
    (P Q P' Q' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeTensorKFlat k₀ l X T P) (hP' : NativeTensorKFlat k₀ l X T P')
    (f : P ⟶ P') (g : Q ⟶ Q') :
    (@MonoidalCategory.tensor _ _ (nativeWeilRingedMonoidal b SB)).map
        (X := (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
        (Y := (DerivedCategory.Q.obj Q', DerivedCategory.Q.obj P'))
        (Prod.mkHom (DerivedCategory.Q.map g) (DerivedCategory.Q.map f)) ≫
        (nativeWeilRingedTensorModel b T adj A SB TB βB cB P' Q' hP').hom =
      (nativeWeilRingedTensorModel b T adj A SB TB βB cB P Q hP).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap f g T (.up ℤ)) := by
  let E := nativeWeilRingedDerivedEquivalence b
  let Ec := b.native.functor.mapHomologicalComplex (.up ℤ)
  let τ := b.native.functor.mapDerivedCategoryFactors
  let r := HomologicalComplex.mapBifunctorMap f g T (.up ℤ)
  let ci := nativeWeilRingedTensorComplexModel b T adj A SB TB βB cB P Q hP
  let ci' := nativeWeilRingedTensorComplexModel b T adj A SB TB βB cB P' Q' hP'
  let d := SB.tensor.map (Prod.mkHom (E.functor.map (DerivedCategory.Q.map g))
    (E.functor.map (DerivedCategory.Q.map f)))
  let dc := SB.tensor.map (Prod.mkHom (DerivedCategory.Q.map (Ec.map g))
    (DerivedCategory.Q.map (Ec.map f)))
  have hc : dc ≫ ci'.hom = ci.hom ≫ DerivedCategory.Q.map (Ec.map r) :=
    nativeWeilRingedTensorComplexModel_naturality b T adj A SB TB βB cB
      P Q P' Q' hP hP' f g
  have ht : d ≫ SB.tensor.map (Prod.mkHom (τ.hom.app Q') (τ.hom.app P')) =
      SB.tensor.map (Prod.mkHom (τ.hom.app Q) (τ.hom.app P)) ≫ dc :=
    mapped_prod_square SB.tensor (τ.hom.naturality g) (τ.hom.naturality f)
  have hε : E.functor.map (E.inverse.map d) ≫ E.counitIso.hom.app _ =
      E.counitIso.hom.app _ ≫ d := E.counitIso.hom.naturality d
  have hd := inverse_square (τ.app (CochainComplex.mapBifunctor P Q T))
    (τ.app (CochainComplex.mapBifunctor P' Q' T))
    (E.functor.map (DerivedCategory.Q.map r)) (DerivedCategory.Q.map (Ec.map r))
      (τ.hom.naturality r)
  have hmap : (@MonoidalCategory.tensor _ _ (nativeWeilRingedMonoidal b SB)).map
      (Prod.mkHom (DerivedCategory.Q.map g) (DerivedCategory.Q.map f)) = E.inverse.map d :=
    rfl
  apply E.functor.map_injective
  simp only [Functor.map_comp, hmap, nativeWeilRingedTensorModel, E,
    Functor.preimageIso_hom,
    Functor.map_preimage, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.prod]
  change E.functor.map (E.inverse.map d) ≫ E.counitIso.hom.app _ ≫
      SB.tensor.map (Prod.mkHom (τ.hom.app Q') (τ.hom.app P')) ≫ ci'.hom ≫
        τ.inv.app (CochainComplex.mapBifunctor P' Q' T) =
    (E.counitIso.hom.app _ ≫
      SB.tensor.map (Prod.mkHom (τ.hom.app Q) (τ.hom.app P)) ≫ ci.hom ≫
        τ.inv.app (CochainComplex.mapBifunctor P Q T)) ≫
          E.functor.map (DerivedCategory.Q.map r)
  simp only [Category.assoc]
  exact four_squares hε ht hc hd

end AlgebraicGeometry.ProEtaleWeilSheaf
