/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Functor.Currying
import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilHomRightAdjoint
import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilUnitMateIsIso

/-! # Native derived tensor adjoints and their invertible forgetful mate

Source: Stacks 06YS, 08J9 and 0A97; the adjoint-construction part of
lem-sf-native-weil-tensor-lift (blueprint: lem-sf-native-weil-tensor-adjoints).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  WeilConjectures

private noncomputable def adjointFamily
    {C : Type*} [Category C] (H : Cᵒᵖ ⥤ C ⥤ C)
    (L : C → C ⥤ C) (a : ∀ K, L K ⊣ H.obj (op K)) : C ⥤ C ⥤ C where
  obj := L
  map {K K'} f := (conjugateEquiv (a K') (a K)).symm (H.map f.op)
  map_id K := by
    rw [op_id, H.map_id, conjugateEquiv_symm_id]
  map_comp {K K' K''} f g := by
    rw [op_comp, H.map_comp, ← conjugateEquiv_symm_comp]

private def adjointSliceIso
    {C : Type*} [Category C] (G : C ⥤ C ⥤ C) (K : C) :
    Prod.sectL C K ⋙ (CategoryTheory.Prod.swap C C ⋙ Functor.uncurry.obj G) ≅ G.obj K :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro A B f
    change ((G.map (𝟙 K)).app A ≫ (G.obj K).map f) ≫ 𝟙 _ =
      𝟙 _ ≫ (G.obj K).map f
    rw [G.map_id]
    simp only [NatTrans.id_app, Category.id_comp, Category.comp_id])

private theorem tensor_of_pointwise_adjoints
    {C : Type*} [Category C] (H : Cᵒᵖ × C ⥤ C)
    (h : ∀ K : C, (Prod.sectR (op K) C ⋙ H).IsRightAdjoint) :
    ∃ T : C × C ⥤ C,
    ∃ a : ∀ K : C, Prod.sectL C K ⋙ T ⊣ Prod.sectR (op K) C ⋙ H,
      (∀ (K K' L : C) (f : K' ⟶ K),
        T.map (X := (H.obj (op K, L), K')) (Y := (H.obj (op K', L), K'))
            (H.map (X := (op K, L)) (Y := (op K', L)) (f.op, 𝟙 L), 𝟙 K') ≫
              (a K').counit.app L =
          T.map (X := (H.obj (op K, L), K')) (Y := (H.obj (op K, L), K))
            (𝟙 (H.obj (op K, L)), f) ≫ (a K).counit.app L) ∧
      (∀ (A K K' : C) (f : K' ⟶ K),
        (a K).unit.app A ≫ H.map (X := (op K, T.obj (A, K)))
            (Y := (op K', T.obj (A, K))) (f.op, 𝟙 _) =
          (a K').unit.app A ≫ H.map (X := (op K', T.obj (A, K')))
            (Y := (op K', T.obj (A, K)))
            (𝟙 _, T.map (X := (A, K')) (Y := (A, K)) (𝟙 A, f))) := by
  let R := Functor.curry.obj H
  have (K : C) : (R.obj (op K)).IsRightAdjoint := h K
  let L : C → C ⥤ C := fun K ↦ (R.obj (op K)).leftAdjoint
  let a : ∀ K : C, L K ⊣ R.obj (op K) := fun K ↦ Adjunction.ofIsRightAdjoint _
  let G := adjointFamily R L a
  let T := CategoryTheory.Prod.swap C C ⋙ Functor.uncurry.obj G
  let e (K : C) := adjointSliceIso G K
  let b (K : C) : Prod.sectL C K ⋙ T ⊣ Prod.sectR (op K) C ⋙ H :=
    (a K).ofNatIsoLeft (e K).symm
  have hc (K N : C) : (b K).counit.app N = (a K).counit.app N := by
    change 𝟙 _ ≫ (a K).counit.app N = _
    exact Category.id_comp _
  have hu (K A : C) : (b K).unit.app A = (a K).unit.app A := by
    change (a K).unit.app A ≫ (R.obj (op K)).map (𝟙 _) = _
    rw [CategoryTheory.Functor.map_id]
    exact Category.comp_id ((a K).unit.app A)
  have ht {A B K : C} (f : A ⟶ B) :
      T.map (X := (A, K)) (Y := (B, K)) (f, 𝟙 K) = (L K).map f := by
    change (G.map (𝟙 K)).app A ≫ (G.obj K).map f = _
    rw [G.map_id]
    exact Category.id_comp _
  have hk {A K K' : C} (f : K' ⟶ K) :
      T.map (X := (A, K')) (Y := (A, K)) (𝟙 A, f) = (G.map f).app A := by
    change (G.map f).app A ≫ (G.obj K).map (𝟙 A) = _
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  refine ⟨T, b, ?_, ?_⟩
  · intro K K' N f
    rw [ht, hk, hc, hc]
    exact conjugateEquiv_counit_symm (a K) (a K') (R.map f.op) N
  · intro A K K' f
    rw [hu, hu, hk]
    exact unit_conjugateEquiv_symm (a K) (a K') (R.map f.op) A

private theorem uncurry_tensor_precomp
    {D : Type*} [Category D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {A B K N : D}
    (f : A ⟶ B) (g : B ⟶ H.obj (op K, N)) :
    (S.transpose A K N).symm (f ≫ g) =
      S.tensor.map (f, 𝟙 K) ≫ (S.transpose B K N).symm g := by
  let := S.monoidal
  change ((S.adjunction K).homEquiv A N).symm (f ≫ g) =
    (f ⊗ₘ 𝟙 K) ≫ ((S.adjunction K).homEquiv B N).symm g
  rw [MonoidalCategory.tensorHom_id]
  exact (S.adjunction K).homEquiv_naturality_left_symm f g

private theorem uncurry_tensor_postcomp
    {D : Type*} [Category D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {A K N N' : D}
    (g : A ⟶ H.obj (op K, N)) (f : N ⟶ N') :
    (S.transpose A K N').symm (g ≫ H.map (𝟙 (op K), f)) =
      (S.transpose A K N).symm g ≫ f :=
  (S.adjunction K).homEquiv_naturality_right_symm g f

private theorem uncurry_tensor_parameter
    {D : Type*} [Category D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {A K K' N : D}
    (f : K ⟶ K') (g : A ⟶ H.obj (op K', N)) :
    (S.transpose A K N).symm (g ≫ H.map (X := (op K', N)) (Y := (op K, N)) (f.op, 𝟙 N)) =
      S.tensor.map (𝟙 A, f) ≫ (S.transpose A K' N).symm g := by
  let := S.monoidal
  have he (B P Q : D) (h : B ⟶ H.obj (op P, Q)) :
      (S.transpose B P Q).symm h =
        S.tensor.map (X := (B, P)) (Y := (H.obj (op P, Q), P))
          (h, 𝟙 P) ≫ (S.adjunction P).counit.app Q := by
    change _ = (h ⊗ₘ 𝟙 P) ≫ _
    rw [MonoidalCategory.tensorHom_id]
    rfl
  have hn : S.tensor.map
      (X := (H.obj (op K', N), K)) (Y := (H.obj (op K, N), K))
      (H.map (X := (op K', N)) (Y := (op K, N)) (f.op, 𝟙 N), 𝟙 K) ≫ (S.adjunction K).counit.app N =
    S.tensor.map
      (X := (H.obj (op K', N), K)) (Y := (H.obj (op K', N), K'))
      (𝟙 (H.obj (op K', N)), f) ≫ (S.adjunction K').counit.app N := by
    change (H.map (X := (op K', N)) (Y := (op K, N)) (f.op, 𝟙 N) ⊗ₘ 𝟙 K) ≫ _ =
      (𝟙 (H.obj (op K', N)) ⊗ₘ f) ≫ _
    rw [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
    exact S.evaluation_naturality K' K N f
  rw [he, he]
  calc
    _ = S.tensor.map (X := (A, K)) (Y := (H.obj (op K', N), K)) (g, 𝟙 K) ≫
        S.tensor.map (X := (H.obj (op K', N), K)) (Y := (H.obj (op K, N), K))
          (H.map (X := (op K', N)) (Y := (op K, N)) (f.op, 𝟙 N), 𝟙 K) ≫
            (S.adjunction K).counit.app N := by
      rw [← S.tensor.map_comp_assoc]
      apply congrArg (fun q : (A, K) ⟶ (H.obj (op K, N), K) ↦
        S.tensor.map q ≫ (S.adjunction K).counit.app N)
      exact Prod.ext rfl (Category.id_comp (𝟙 K)).symm
    _ = S.tensor.map (X := (A, K)) (Y := (H.obj (op K', N), K)) (g, 𝟙 K) ≫
        S.tensor.map (X := (H.obj (op K', N), K)) (Y := (H.obj (op K', N), K'))
          (𝟙 (H.obj (op K', N)), f) ≫ (S.adjunction K').counit.app N := by
      rw [hn]
    _ = _ := by
      rw [← S.tensor.map_comp_assoc, ← S.tensor.map_comp_assoc]
      apply congrArg (fun q : (A, K) ⟶ (H.obj (op K', N), K') ↦
        S.tensor.map q ≫ (S.adjunction K').counit.app N)
      exact Prod.ext
        ((Category.comp_id _).trans (Category.id_comp _).symm)
        ((Category.id_comp _).trans (Category.comp_id _).symm)

private def unitMateComponent
    {C D : Type*} [Category C] [Category D]
    {H : Cᵒᵖ × C ⥤ C} {H' : Dᵒᵖ × D ⥤ D}
    (F : C ⥤ D) (η : H ⋙ F ≅ (F.op.prod F) ⋙ H')
    (S : CoefficientClosedStructure H') (T : C × C ⥤ C)
    (a : ∀ K : C, Prod.sectL C K ⋙ T ⊣ Prod.sectR (op K) C ⋙ H)
    (A K : C) : S.tensor.obj (F.obj A, F.obj K) ⟶ F.obj (T.obj (A, K)) :=
  (S.transpose (F.obj A) (F.obj K) (F.obj (T.obj (A, K)))).symm
    (F.map ((a K).unit.app A) ≫ η.hom.app (op K, T.obj (A, K)))

private theorem unitMateComponent_left
    {C D : Type*} [Category C] [Category D]
    {H : Cᵒᵖ × C ⥤ C} {H' : Dᵒᵖ × D ⥤ D}
    (F : C ⥤ D) (η : H ⋙ F ≅ (F.op.prod F) ⋙ H')
    (S : CoefficientClosedStructure H') (T : C × C ⥤ C)
    (a : ∀ K : C, Prod.sectL C K ⋙ T ⊣ Prod.sectR (op K) C ⋙ H)
    {A B : C} (f : A ⟶ B) (K : C) :
    S.tensor.map (F.map f, 𝟙 (F.obj K)) ≫ unitMateComponent F η S T a B K =
      unitMateComponent F η S T a A K ≫
        F.map (T.map (X := (A, K)) (Y := (B, K)) (f, 𝟙 K)) := by
  let t : T.obj (A, K) ⟶ T.obj (B, K) := T.map (f, 𝟙 K)
  unfold unitMateComponent
  rw [← uncurry_tensor_precomp, ← uncurry_tensor_postcomp]
  congr 1
  have hn : f ≫ (a K).unit.app B =
      (a K).unit.app A ≫
        H.map (X := (op K, T.obj (A, K))) (Y := (op K, T.obj (B, K))) (𝟙 _, t) :=
    (a K).unit.naturality f
  have he : F.map (H.map (X := (op K, T.obj (A, K)))
        (Y := (op K, T.obj (B, K))) (𝟙 _, t)) ≫
      η.hom.app (op K, T.obj (B, K)) =
    η.hom.app (op K, T.obj (A, K)) ≫
      H'.map (X := (op (F.obj K), F.obj (T.obj (A, K))))
        (Y := (op (F.obj K), F.obj (T.obj (B, K)))) (𝟙 _, F.map t) := by
    simpa using η.hom.naturality (Prod.mkHom (𝟙 (op K)) t)
  rw [← Category.assoc, ← F.map_comp, hn, F.map_comp, Category.assoc, he]
  simp only [Category.assoc, t]

private theorem unitMateComponent_right
    {C D : Type*} [Category C] [Category D]
    {H : Cᵒᵖ × C ⥤ C} {H' : Dᵒᵖ × D ⥤ D}
    (F : C ⥤ D) (η : H ⋙ F ≅ (F.op.prod F) ⋙ H')
    (S : CoefficientClosedStructure H') (T : C × C ⥤ C)
    (a : ∀ K : C, Prod.sectL C K ⋙ T ⊣ Prod.sectR (op K) C ⋙ H)
    (hu : ∀ (A K K' : C) (f : K' ⟶ K),
      (a K).unit.app A ≫ H.map (X := (op K, T.obj (A, K)))
          (Y := (op K', T.obj (A, K))) (f.op, 𝟙 _) =
        (a K').unit.app A ≫ H.map (X := (op K', T.obj (A, K')))
          (Y := (op K', T.obj (A, K))) (𝟙 _, T.map (X := (A, K')) (Y := (A, K)) (𝟙 A, f)))
    (A : C) {K K' : C} (f : K ⟶ K') :
    S.tensor.map (𝟙 (F.obj A), F.map f) ≫ unitMateComponent F η S T a A K' =
      unitMateComponent F η S T a A K ≫ F.map (T.map (X := (A, K)) (Y := (A, K')) (𝟙 A, f)) := by
  let t : T.obj (A, K) ⟶ T.obj (A, K') := T.map (𝟙 A, f)
  unfold unitMateComponent
  rw [← uncurry_tensor_parameter, ← uncurry_tensor_postcomp]
  congr 1
  have hp : F.map (H.map (X := (op K', T.obj (A, K')))
      (Y := (op K, T.obj (A, K'))) (f.op, 𝟙 _)) ≫
        η.hom.app (op K, T.obj (A, K')) =
      η.hom.app (op K', T.obj (A, K')) ≫
        H'.map (X := (op (F.obj K'), F.obj (T.obj (A, K'))))
          (Y := (op (F.obj K), F.obj (T.obj (A, K')))) ((F.map f).op, 𝟙 _) := by
    simpa using η.hom.naturality
      (Prod.mkHom f.op (𝟙 (T.obj (A, K'))))
  have ht : F.map (H.map (X := (op K, T.obj (A, K)))
        (Y := (op K, T.obj (A, K'))) (𝟙 _, t)) ≫
      η.hom.app (op K, T.obj (A, K')) =
    η.hom.app (op K, T.obj (A, K)) ≫
      H'.map (X := (op (F.obj K), F.obj (T.obj (A, K))))
        (Y := (op (F.obj K), F.obj (T.obj (A, K')))) (𝟙 _, F.map t) := by
    simpa using η.hom.naturality (Prod.mkHom (𝟙 (op K)) t)
  rw [Category.assoc, ← hp, ← Category.assoc, ← F.map_comp,
    hu A K' K f, F.map_comp, Category.assoc, ht]
  simp only [Category.assoc, t]

private def unitMate
    {C D : Type*} [Category C] [Category D]
    {H : Cᵒᵖ × C ⥤ C} {H' : Dᵒᵖ × D ⥤ D}
    (F : C ⥤ D) (η : H ⋙ F ≅ (F.op.prod F) ⋙ H')
    (S : CoefficientClosedStructure H') (T : C × C ⥤ C)
    (a : ∀ K : C, Prod.sectL C K ⋙ T ⊣ Prod.sectR (op K) C ⋙ H)
    (hu : ∀ (A K K' : C) (f : K' ⟶ K),
      (a K).unit.app A ≫ H.map (X := (op K, T.obj (A, K)))
          (Y := (op K', T.obj (A, K))) (f.op, 𝟙 _) =
        (a K').unit.app A ≫ H.map (X := (op K', T.obj (A, K')))
          (Y := (op K', T.obj (A, K))) (𝟙 _, T.map (X := (A, K')) (Y := (A, K)) (𝟙 A, f))) :
    (F.prod F) ⋙ S.tensor ⟶ T ⋙ F where
  app X := unitMateComponent F η S T a X.1 X.2
  naturality {X Y} f := by
    let t₁ : T.obj X ⟶ T.obj (Y.1, X.2) :=
      T.map (X := X) (Y := (Y.1, X.2)) (f.1, 𝟙 X.2)
    let t₂ : T.obj (Y.1, X.2) ⟶ T.obj Y :=
      T.map (X := (Y.1, X.2)) (Y := Y) (𝟙 Y.1, f.2)
    have ht : t₁ ≫ t₂ = T.map f := by
      dsimp only [t₁, t₂]
      rw [← T.map_comp]
      congr 1
      exact Prod.ext (Category.comp_id _) (Category.id_comp _)
    change S.tensor.map (F.map f.1, F.map f.2) ≫
        unitMateComponent F η S T a Y.1 Y.2 =
      unitMateComponent F η S T a X.1 X.2 ≫ F.map (T.map f)
    calc
      _ = S.tensor.map
            (X := (F.obj X.1, F.obj X.2)) (Y := (F.obj Y.1, F.obj X.2))
            (F.map f.1, 𝟙 (F.obj X.2)) ≫
          S.tensor.map
            (X := (F.obj Y.1, F.obj X.2)) (Y := (F.obj Y.1, F.obj Y.2))
            (𝟙 (F.obj Y.1), F.map f.2) ≫
            unitMateComponent F η S T a Y.1 Y.2 := by
        rw [← S.tensor.map_comp_assoc]
        simp
      _ = S.tensor.map (F.map f.1, 𝟙 (F.obj X.2)) ≫
          unitMateComponent F η S T a Y.1 X.2 ≫ F.map t₂ := by
        rw [unitMateComponent_right F η S T a hu]
      _ = unitMateComponent F η S T a X.1 X.2 ≫ F.map t₁ ≫ F.map t₂ := by
        rw [← Category.assoc, unitMateComponent_left F η S T a, Category.assoc]
      _ = _ := by rw [← F.map_comp, ht]

private theorem adjoints_of_pointwise
    {C D : Type*} [Category C] [Category D]
    (H : Cᵒᵖ × C ⥤ C) (H' : Dᵒᵖ × D ⥤ D)
    (F : C ⥤ D) (η : H ⋙ F ≅ (F.op.prod F) ⋙ H')
    (S : CoefficientClosedStructure H')
    (h : ∀ K : C, (Prod.sectR (op K) C ⋙ H).IsRightAdjoint)
    (hm : ∀ (K : C) (L : C ⥤ C) (a : L ⊣ Prod.sectR (op K) C ⋙ H) (A : C),
      IsIso ((S.transpose (F.obj A) (F.obj K) (F.obj (L.obj A))).symm
        (F.map (a.unit.app A) ≫ η.hom.app (op K, L.obj A)))) :
    ∃ T : C × C ⥤ C,
    ∃ a : ∀ K : C, Prod.sectL C K ⋙ T ⊣ Prod.sectR (op K) C ⋙ H,
      (∀ (K K' L : C) (f : K' ⟶ K),
        T.map (X := (H.obj (op K, L), K')) (Y := (H.obj (op K', L), K'))
            (H.map (X := (op K, L)) (Y := (op K', L)) (f.op, 𝟙 L), 𝟙 K') ≫
              (a K').counit.app L =
          T.map (X := (H.obj (op K, L), K')) (Y := (H.obj (op K, L), K))
            (𝟙 (H.obj (op K, L)), f) ≫ (a K).counit.app L) ∧
      ∃ τ : T ⋙ F ≅ (F.prod F) ⋙ S.tensor,
      ∀ A K : C, τ.inv.app (A, K) =
        (S.transpose (F.obj A) (F.obj K) (F.obj (T.obj (A, K)))).symm
          (F.map ((a K).unit.app A) ≫ η.hom.app (op K, T.obj (A, K))) := by
  obtain ⟨T, a, ha, hu⟩ := tensor_of_pointwise_adjoints H h
  let m := unitMate F η S T a hu
  have (P : C × C) : IsIso (m.app P) := hm P.2 (Prod.sectL C P.2 ⋙ T) (a P.2) P.1
  have : IsIso m := NatIso.isIso_of_isIso_app m
  exact ⟨T, a, ha, (asIso m).symm, fun _ _ ↦ rfl⟩

namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Construct the tensor bifunctor representing native internal Hom and identify
its forgetful mate. This assertion concerns adjoints and an invertible natural
transformation; it supplies no associator, unitors, tensor unit or symmetry.

Source: Stacks 06YS, 08J9 and 0A97; native tensor lift, step 1 and the
representative comparison in step 2
(blueprint: lem-sf-native-weil-tensor-adjoints).

Proof: present Weil sheaves as modules on the Frobenius ringed action site using
frobenius_action_resolutions. The additive equivalence preserves products and
coproducts and takes K-flat and K-injective resolutions to the native ones.
The ringed tensor-Hom adjunction, transported through this equivalence, identifies
maps out of its total tensor with maps into the product-total native Hom.
Compare this Hom with M.weilHom on every source complex and K-injective target
using M.weilRepresentatives.model. Their naturality descends through the
K-injective localization equivalence in both variables. Conjugate the right
adjoints by these comparisons. Parameter naturality of the chain evaluation
then gives the displayed counit equation, including morphisms in K.
Apply the ordinary adjunction to the image of each resulting native unit,
followed by eta. On flat-term K-flat representatives, hη identifies this mate
with the sum-total of the underived identity on relative tensor factors:
project the Hom comparison to each (p,q) component and use the ordinary
normalization hS. The row-sign conversions cancel on these components.
Forgetting preserves both resolutions, so this mate is invertible on every
K-flat pair. Naturality on complex maps and the universal property of tensor
localization extend it and its inverse to every derived pair. The displayed
formula specifies its inverse as the mate of the unit; no associativity,
unitality or symmetry assertion is needed for this construction. Zero complexes
and the empty scheme use the same universal properties without an exception. -/
theorem native_weil_tensor_adjoints
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (M : NativeClosedHomModels k₀ l X)
    (η : M.weilHom ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).op.prod (nativeForget k₀ l X) ⋙ M.ordinaryHom)
    (hη : NativeHomRepresentativeCompatibility (ihomBifunctor k₀ l X)
      (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      M.weilHom M.ordinaryHom M.weilRepresentatives M.ordinaryRepresentatives
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) η)
    (S : CoefficientClosedStructure M.ordinaryHom)
    (β : @SymmetricCategory _ _ S.monoidal)
    (hmonoidal : S.monoidal = (inferInstance : MonoidalCategory
      (DerivedCategory (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))))
    (hS : NativeOrdinaryTensorModels l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
      M.ordinaryHom M.ordinaryRepresentatives S β) :
    ∃ T : (DerivedCategory (ProEtaleWeilSheaf k₀ l X)) ×
      DerivedCategory (ProEtaleWeilSheaf k₀ l X) ⥤
        DerivedCategory (ProEtaleWeilSheaf k₀ l X),
    ∃ a : ∀ K : DerivedCategory (ProEtaleWeilSheaf k₀ l X),
      Prod.sectL _ K ⋙ T ⊣ Prod.sectR (op K) _ ⋙ M.weilHom,
      (∀ (K K' L : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) (f : K' ⟶ K),
        T.map (X := (M.weilHom.obj (op K, L), K'))
            (Y := (M.weilHom.obj (op K', L), K'))
            (M.weilHom.map (X := (op K, L)) (Y := (op K', L)) (f.op, 𝟙 L), 𝟙 K') ≫
              (a K').counit.app L =
          T.map (X := (M.weilHom.obj (op K, L), K'))
            (Y := (M.weilHom.obj (op K, L), K))
            (𝟙 (M.weilHom.obj (op K, L)), f) ≫ (a K).counit.app L) ∧
      ∃ τ : T ⋙ nativeForget k₀ l X ≅
        (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ S.tensor,
      ∀ A K : DerivedCategory (ProEtaleWeilSheaf k₀ l X),
        τ.inv.app (A, K) =
          (S.transpose ((nativeForget k₀ l X).obj A) ((nativeForget k₀ l X).obj K)
            ((nativeForget k₀ l X).obj (T.obj (A, K)))).symm
              ((nativeForget k₀ l X).map ((a K).unit.app A) ≫
                η.hom.app (op K, T.obj (A, K))) := by
  exact adjoints_of_pointwise M.weilHom M.ordinaryHom (nativeForget k₀ l X) η S
    (native_weil_hom_isRightAdjoint k₀ l X M)
    (fun K L a A ↦ native_weil_unit_mate_isIso k₀ l X M η hη S β hmonoidal hS K L a A)

end AlgebraicGeometry.ProEtaleWeilSheaf
