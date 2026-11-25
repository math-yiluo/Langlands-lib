/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedComplexes
public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedStructure

/-! # The ringed total-to-native-total middle comparison

Source: Stacks 06YU and the representative step of native tensor transport.
This module isolates the two middle squares of the transported model.
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

/-- The ringed one-K-flat model followed by the localized native total comparison.
Source: Stacks 06YU
(blueprint: def-sf-native-weil-tensor-ringed-complex-model). -/
def nativeWeilRingedTensorComplexModel
    (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeTensorKFlat k₀ l X T P) :
    SB.tensor.obj
        (DerivedCategory.Q.obj ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj Q),
          DerivedCategory.Q.obj ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj P)) ≅
      DerivedCategory.Q.obj ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor P Q T)) :=
  (cB.tensorIso
    ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj Q)
    ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj P)
    (Or.inr (A.flat P hP))).symm ≪≫ (DerivedCategory.Q.mapIso (A.chain P Q)).symm

private theorem mapped_square {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y X' Y' : C} {a : X ⟶ Y} {b : X' ⟶ Y'}
    {f : X ⟶ X'} {g : Y ⟶ Y'} (h : f ≫ b = a ≫ g) :
    F.map f ≫ F.map b = F.map a ≫ F.map g := by
  rw [← F.map_comp, ← F.map_comp, h]

private theorem inverse_square {C : Type*} [Category C] {A B A' B' : C}
    (e : A ≅ B) (e' : A' ≅ B') (f : A ⟶ A') (g : B ⟶ B')
    (h : f ≫ e'.hom = e.hom ≫ g) : g ≫ e'.inv = e.inv ≫ f := by
  calc
    g ≫ e'.inv = e.inv ≫ (e.hom ≫ g) ≫ e'.inv := by simp
    _ = e.inv ≫ (f ≫ e'.hom) ≫ e'.inv := by rw [h]
    _ = e.inv ≫ f := by simp

private theorem two_squares {C : Type*} [Category C]
    {A B D A' B' D' : C} {a : A ⟶ B} {b : B ⟶ D}
    {a' : A' ⟶ B'} {b' : B' ⟶ D'}
    {f : A ⟶ A'} {g : B ⟶ B'} {h : D ⟶ D'}
    (ha : f ≫ a' = a ≫ g) (hb : g ≫ b' = b ≫ h) :
    f ≫ a' ≫ b' = a ≫ b ≫ h := by
  rw [reassoc_of% ha, hb]

/-- Naturality of the two middle comparison factors.
Source: Stacks 06YU
(blueprint: def-sf-native-weil-tensor-ringed-complex-model). -/
theorem nativeWeilRingedTensorComplexModel_naturality
    (P Q P' Q' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeTensorKFlat k₀ l X T P) (hP' : NativeTensorKFlat k₀ l X T P')
    (f : P ⟶ P') (g : Q ⟶ Q') :
    SB.tensor.map (Prod.mkHom
        (DerivedCategory.Q.map ((b.native.functor.mapHomologicalComplex (.up ℤ)).map g))
        (DerivedCategory.Q.map ((b.native.functor.mapHomologicalComplex (.up ℤ)).map f))) ≫
        (nativeWeilRingedTensorComplexModel b T adj A SB TB βB cB P' Q' hP').hom =
      (nativeWeilRingedTensorComplexModel b T adj A SB TB βB cB P Q hP).hom ≫
        DerivedCategory.Q.map ((b.native.functor.mapHomologicalComplex (.up ℤ)).map
          (HomologicalComplex.mapBifunctorMap f g T (.up ℤ))) := by
  let Ec := b.native.functor.mapHomologicalComplex (.up ℤ)
  let ci := cB.tensorIso (Ec.obj Q) (Ec.obj P) (Or.inr (A.flat P hP))
  let ci' := cB.tensorIso (Ec.obj Q') (Ec.obj P') (Or.inr (A.flat P' hP'))
  let z := (coefficientTotalTensor.{u + 1, u + 1, u + 1} b.J b.R).map
    (Prod.mkHom (Ec.map g) (Ec.map f))
  let dc := SB.tensor.map (Prod.mkHom (DerivedCategory.Q.map (Ec.map g))
    (DerivedCategory.Q.map (Ec.map f)))
  let r := HomologicalComplex.mapBifunctorMap f g T (.up ℤ)
  have hn : DerivedCategory.Q.map z ≫ ci'.hom = ci.hom ≫ dc :=
    cB.tensorIso_naturality (Ec.obj Q) (Ec.obj P) (Ec.obj Q') (Ec.obj P')
      (Or.inr (A.flat P hP)) (Or.inr (A.flat P' hP')) (Ec.map g) (Ec.map f)
  have hc : DerivedCategory.Q.map (Ec.map r) ≫
      (DerivedCategory.Q.mapIso (A.chain P' Q')).hom =
        (DerivedCategory.Q.mapIso (A.chain P Q)).hom ≫ DerivedCategory.Q.map z :=
    mapped_square DerivedCategory.Q (A.naturality P Q P' Q' f g)
  have ha := inverse_square ci ci' (DerivedCategory.Q.map z) dc hn
  have hb := inverse_square (DerivedCategory.Q.mapIso (A.chain P Q))
    (DerivedCategory.Q.mapIso (A.chain P' Q')) (DerivedCategory.Q.map (Ec.map r))
      (DerivedCategory.Q.map z) hc
  simp only [nativeWeilRingedTensorComplexModel, Iso.trans_hom, Iso.symm_hom]
  change dc ≫ ci'.inv ≫ (DerivedCategory.Q.mapIso (A.chain P' Q')).inv =
    (ci.inv ≫ (DerivedCategory.Q.mapIso (A.chain P Q)).inv) ≫
      DerivedCategory.Q.map (Ec.map r)
  simp only [Category.assoc]
  exact two_squares ha hb

end AlgebraicGeometry.ProEtaleWeilSheaf
