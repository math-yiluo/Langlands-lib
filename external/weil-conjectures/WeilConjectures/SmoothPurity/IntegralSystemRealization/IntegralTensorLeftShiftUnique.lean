/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.IntegralSystemRealization.IntegralTensorShiftProperties
import all WeilConjectures.SixFunctors.Completed.CompletedTensorFiniteShift
import all WeilConjectures.SixFunctors.Completed.CompletedTensorShiftRight
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
/-! # Unique normalized shift in the unsigned completed first slot -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 1024
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
universe a b c d e f u v w
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  SheafOfModules.monoidalCategory
section GenericLeftShift
variable {A : Type a} [Category.{b} A] [Preadditive A] {B : Type c} [Category.{d} B]
  [Preadditive B] {C : Type e} [Category.{f} C] [Preadditive C] (F : A ⥤ B) [F.Additive] (G : B ⥤
    C) [G.Additive]
private local instance (priority := 2000) : F.PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive F
private local instance (priority := 2000) : G.PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive G
variable (T : B ⥤ B ⥤ B) [T.PreservesZeroMorphisms] [T.Additive]
  [∀ X, (T.obj X).Additive]
private local instance (priority := 2000) : ∀ X, (T.obj X).PreservesZeroMorphisms :=
  fun X ↦ Functor.preservesZeroMorphisms_of_additive (T.obj X)
variable [∀ X Y : CochainComplex B ℤ, CochainComplex.HasMapBifunctor X Y T]

private def leftLevelIso (P Q : CochainComplex A ℤ) (r : ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj (P⟦r⟧))
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) T) ≅
      ((G.mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj P)
            ((F.mapHomologicalComplex (.up ℤ)).obj Q) T))⟦r⟧ :=
  (G.mapHomologicalComplex (.up ℤ)).mapIso
      ((T.map₂CochainComplex.flip.obj ((F.mapHomologicalComplex (.up ℤ)).obj Q)).mapIso
          ((F.mapCochainComplexShiftIso r).app P) ≪≫
        CochainComplex.mapBifunctorShift₁Iso ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) T r) ≪≫
    (G.mapCochainComplexShiftIso r).app _

private theorem leftLevelIso_ι (P Q : CochainComplex A ℤ) (r i j : ℤ) :
    G.map
          (CochainComplex.ιMapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj (P⟦r⟧))
            ((F.mapHomologicalComplex (.up ℤ)).obj Q) T i j (i + j) rfl) ≫
        (leftLevelIso F G T P Q r).hom.f (i + j) =
      G.map
          (CochainComplex.ιMapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj P)
            ((F.mapHomologicalComplex (.up ℤ)).obj Q) T (i + r) j ((i + r) + j) rfl) ≫
        (CochainComplex.shiftFunctorObjXIso
            ((G.mapHomologicalComplex (.up ℤ)).obj
              (CochainComplex.mapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj P)
                ((F.mapHomologicalComplex (.up ℤ)).obj Q) T))
            r (i + j) ((i + r) + j) (by omega)).inv := by
  let P' := (F.mapHomologicalComplex (.up ℤ)).obj P
  let Q' := (F.mapHomologicalComplex (.up ℤ)).obj Q
  have hm :=
    HomologicalComplex.ι_mapBifunctorMap ((F.mapCochainComplexShiftIso r).hom.app P) (𝟙 Q') T
      (.up ℤ) i j (i + j)
      rfl
  dsimp only [HomologicalComplex.id_f, Functor.mapCochainComplexShiftIso_hom_app_f] at hm
  change
    _ =
      (T.map (𝟙 (F.obj (P.X (i + r))))).app (F.obj (Q.X j)) ≫
        (T.obj (F.obj (P.X (i + r)))).map (𝟙 (F.obj (Q.X j))) ≫ _ at hm
  rw [T.map_id, NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.id_comp] at hm
  have hs :=
    CochainComplex.ι_mapBifunctorShift₁Iso_hom_f P' Q' T r i j (i + j) rfl (i + r) ((i + r) + j)
      rfl (by omega)
  change _ = (T.map (𝟙 (F.obj (P.X (i + r))))).app (F.obj (Q.X j)) ≫ _ at hs
  rw [T.map_id, NatTrans.id_app, Category.id_comp] at hs
  have hc :=
    congrArg (fun k ↦ G.map k)
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k ↦ k ≫ (CochainComplex.mapBifunctorShift₁Iso P' Q' T r).hom.f (i + j))
          hm).trans hs))
  dsimp only [Functor.comp_obj] at hc
  convert hc using 1 <;>
    simp only [leftLevelIso, Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, Functor.mapCochainComplexShiftIso_hom_app_f, Iso.app_hom,
      Functor.map_comp, Category.assoc, CochainComplex.shiftFunctorObjXIso,
        HomologicalComplex.XIsoOfEq, P', Q',
      eqToIso.inv, eqToHom_map]
  · rfl
  · change _ ≫ _ ≫ _ ≫ 𝟙 _ = _ ≫ _ ≫ _
    exact congrArg₂ (fun f g ↦ f ≫ g) rfl (congrArg₂ (fun f g ↦ f ≫ g) rfl (Category.comp_id _))

private def firstShiftIsoGeneric {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] (T : D ⥤ D ⥤ D) [T.CommShift₂Int] (n : ℤ) :
    (shiftFunctor D n).prod (𝟭 D) ⋙ uncurry.obj T ≅ uncurry.obj T ⋙ shiftFunctor D n :=
  NatIso.ofComponents (fun X ↦ ((T.flip.obj X.2).commShiftIso n).app X.1)
    (by
      rintro ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ ⟨f₁, f₂⟩
      change
        ((T.map (f₁⟦n⟧')).app X₂ ≫ (T.obj (Y₁⟦n⟧)).map f₂) ≫ ((T.flip.obj Y₂).commShiftIso
          n).hom.app Y₁ =
          ((T.flip.obj X₂).commShiftIso n).hom.app X₁ ≫ ((T.map f₁).app X₂ ≫ (T.obj Y₁).map f₂)⟦n⟧'
      have hh := NatTrans.shift_app_comm (T.flip.map f₂) n Y₁
      change
        ((T.flip.obj X₂).commShiftIso n).hom.app Y₁ ≫ ((T.obj Y₁).map f₂)⟦n⟧' =
          (T.obj (Y₁⟦n⟧)).map f₂ ≫ ((T.flip.obj Y₂).commShiftIso n).hom.app Y₁ at hh
      have h₁ := (T.flip.obj X₂).commShiftIso_hom_naturality f₁ n
      change
        (T.map (f₁⟦n⟧')).app X₂ ≫ ((T.flip.obj X₂).commShiftIso n).hom.app Y₁ =
          ((T.flip.obj X₂).commShiftIso n).hom.app X₁ ≫ ((T.map f₁).app X₂)⟦n⟧' at h₁
      rw [Category.assoc, ← hh, ← Category.assoc, h₁, Category.assoc,
        CategoryTheory.Functor.map_comp])

private def leftTensorShiftIso (r : ℤ) :
    ((shiftFunctor _ r).prod (𝟭 (CochainComplex B ℤ))) ⋙ Functor.uncurry.obj T.map₂CochainComplex ≅
      Functor.uncurry.obj T.map₂CochainComplex ⋙ shiftFunctor _ r :=
  firstShiftIsoGeneric T.map₂CochainComplex r

private def leftLevelNatIso (r : ℤ) :
    ((shiftFunctor _ r).prod (𝟭 (CochainComplex A ℤ))) ⋙
        (F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ)) ⋙
          Functor.uncurry.obj T.map₂CochainComplex ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      ((F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ)) ⋙
          Functor.uncurry.obj T.map₂CochainComplex ⋙ G.mapHomologicalComplex (.up ℤ)) ⋙
        shiftFunctor _ r :=
  isoWhiskerRight (NatIso.prod (F.mapCochainComplexShiftIso r) (Iso.refl (F.mapHomologicalComplex
    (.up ℤ))))
      (Functor.uncurry.obj T.map₂CochainComplex ⋙ G.mapHomologicalComplex (.up ℤ)) ≪≫
    isoWhiskerLeft ((F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ)))
        (isoWhiskerRight (leftTensorShiftIso T r) (G.mapHomologicalComplex (.up ℤ))) ≪≫
      isoWhiskerLeft
        ((F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ)) ⋙
          Functor.uncurry.obj T.map₂CochainComplex)
        (G.mapCochainComplexShiftIso r)

private theorem leftLevelNatIso_app (P Q : CochainComplex A ℤ) (r : ℤ) :
    (leftLevelNatIso F G T r).app (P, Q) = leftLevelIso F G T P Q r := by
  apply Iso.ext
  dsimp only [leftLevelNatIso, Iso.app_hom, Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, NatIso.prod_hom, Iso.refl_hom,
      NatTrans.id_app,
    Functor.comp_map, Functor.uncurry_obj_map]
  change
    (G.mapHomologicalComplex (.up ℤ)).map
          ((T.map₂CochainComplex.map _).app _ ≫ (T.map₂CochainComplex.obj _).map (𝟙 _)) ≫
        _ ≫ _ =
      _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  simp only [leftLevelIso, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    leftTensorShiftIso,
    firstShiftIsoGeneric, NatIso.ofComponents_hom_app]
  rfl

end GenericLeftShift

section GenericTowerShift
variable {A : Type a} [Category.{b} A] {B : Type c} [Category.{d} B]
private def towerShiftGeneric (F : ℕ → A ⥤ B) (τ : ∀ n, F (n + 1) ⟶ F n)
    (U : A ⥤ A) (S : B ⥤ B) (β : ∀ n, U ⋙ F n ≅ F n ⋙ S)
    (h : ∀ n, whiskerLeft U (τ n) ≫ (β n).hom =
      (β (n + 1)).hom ≫ whiskerRight (τ n) S) :
    U ⋙ (Functor.ofOpSequence τ).flip ≅
      (Functor.ofOpSequence τ).flip ⋙ (whiskeringRight ℕᵒᵖ B B).obj S :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun n ↦ (β n.unop).app X) (by
    intro n m f
    let η : ((Functor.ofOpSequence τ).flip.obj (U.obj X)) ⟶
        (Functor.ofOpSequence τ).flip.obj X ⋙ S :=
      NatTrans.ofOpSequence (fun n ↦ (β n).hom.app X) (by
        intro n
        have hn := congrArg (fun t ↦ t.app X) (h n)
        simpa only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
          Functor.flip_obj_map, Functor.comp_map,
          Functor.ofOpSequence_map_homOfLE_succ] using hn)
    exact η.naturality f)) (by
      intro X Y f
      apply NatTrans.ext
      funext n
      exact (β n.unop).hom.naturality f)
private theorem towerShiftGeneric_hom_app (F : ℕ → A ⥤ B)
    (τ : ∀ n, F (n + 1) ⟶ F n) (U : A ⥤ A) (S : B ⥤ B)
    (β : ∀ n, U ⋙ F n ≅ F n ⋙ S)
    (h : ∀ n, whiskerLeft U (τ n) ≫ (β n).hom =
      (β (n + 1)).hom ≫ whiskerRight (τ n) S) (X : A) (n : ℕᵒᵖ) :
    ((towerShiftGeneric F τ U S β h).hom.app X).app n = (β n.unop).hom.app X := rfl

end GenericTowerShift

section GenericCancellation
variable {A : Type a} [Category.{b} A] {X Y Z W : A}
private theorem cancelOuterIso (a : X ⟶ Y) [IsIso a] (b : Z ⟶ W) [IsIso b]
    (f g : Y ⟶ Z) (h : a ≫ f ≫ b = a ≫ g ≫ b) : f = g := by
  apply (cancel_epi a).mp
  apply (cancel_mono b).mp
  simpa only [Category.assoc] using h
private theorem normalizeComponent {V : A} {a a' : X ⟶ Y} {f : Y ⟶ Z}
    {b : Z ⟶ W} {c : X ⟶ V} {d d' : V ⟶ W}
    (ha : a = a') (hd : d = d') (h : a ≫ f ≫ b = c ≫ d) :
    a' ≫ f ≫ b = c ≫ d' := by
  subst a'
  subst d'
  exact h

private theorem normalizedComponent_unique {H : Prop} {M : Type c} {N : Type d}
    (F : M → Prop) (C : M → N → Prop) (R : H → N → (X ⟶ W))
    (a : X ⟶ Y) [IsIso a] (b : Z ⟶ W) [IsIso b] (s t : Y ⟶ Z)
    (hF : ∀ α β, F α → F β → α = β)
    (hC : ∀ α δ ε, C α δ → C α ε → δ = ε)
    (hs : ∃ p : H, ∃ α, F α ∧ ∃ δ, C α δ ∧ a ≫ s ≫ b = R p δ)
    (ht : ∃ p : H, ∃ α, F α ∧ ∃ δ, C α δ ∧ a ≫ t ≫ b = R p δ) : s = t := by
  obtain ⟨p, α, hα, δ, hδ, es⟩ := hs
  obtain ⟨q, β, hβ, ε, hε, et⟩ := ht
  have hab := hF α β hα hβ
  subst β
  have hde := hC α δ ε hδ hε
  subst ε
  exact cancelOuterIso a b s t (es.trans et.symm)
end GenericCancellation

section GenericDescentComponents
variable {A : Type a} [Category.{b} A] {B : Type c} [Category.{d} B]
private theorem mapComp_congr (F : A ⥤ B) {X Y : A} {Z : B}
    {f g : X ⟶ Y} {a b : F.obj Y ⟶ Z} (hf : f = g) (ha : a = b) :
    F.map f ≫ a = F.map g ≫ b := by
  subst g
  subst b
  rfl

private def firstInputIso (U : A ⥤ A) (L : A ⥤ B) (S : B ⥤ B)
    (γ : U ⋙ L ≅ L ⋙ S) :
    U.prod (𝟭 A) ⋙ L.prod L ≅ L.prod L ⋙ S.prod (𝟭 B) :=
  NatIso.prod γ (Iso.refl L)

private theorem iso_ext_of_representatives {C : Type e} [Category.{f} C] (L : A ⥤ B)
    (hL : ∀ Y, ∃ X, Nonempty (L.obj X ≅ Y))
    {F G : B ⥤ C} (σ τ : F ≅ G)
    (h : ∀ X, σ.hom.app (L.obj X) = τ.hom.app (L.obj X)) : σ = τ := by
  apply Iso.ext
  apply NatTrans.ext
  funext Y
  obtain ⟨X, ⟨e⟩⟩ := hL Y
  apply (cancel_epi (F.map e.hom)).mp
  exact (σ.hom.naturality e.hom).trans
    ((congrArg (fun f ↦ f ≫ G.map e.hom) (h X)).trans (τ.hom.naturality e.hom).symm)

section NormalizedExtensionality
universe g h
variable {C : Type e} [Category.{f} C]
private theorem iso_ext_normalized (L : A ⥤ B)
    (hL : ∀ Y, ∃ X, Nonempty (L.obj X ≅ Y))
    {F G : B ⥤ C} (D T : A → C)
    (a : ∀ X, D X ⟶ F.obj (L.obj X)) (ha : ∀ X, IsIso (a X))
    (b : ∀ X, G.obj (L.obj X) ⟶ T X) (hb : ∀ X, IsIso (b X))
    (H : A → Prop) {M : A → Type g} {N : A → Type h}
    (P : ∀ X, M X → Prop) (Q : ∀ X, M X → N X → Prop)
    (R : ∀ X, H X → N X → (D X ⟶ T X))
    (hP : ∀ X α β, P X α → P X β → α = β)
    (hQ : ∀ X α δ ε, Q X α δ → Q X α ε → δ = ε)
    (σ τ : F ≅ G)
    (hσ : ∀ X, ∃ p : H X, ∃ α, P X α ∧ ∃ δ, Q X α δ ∧
      a X ≫ σ.hom.app (L.obj X) ≫ b X = R X p δ)
    (hτ : ∀ X, ∃ p : H X, ∃ α, P X α ∧ ∃ δ, Q X α δ ∧
      a X ≫ τ.hom.app (L.obj X) ≫ b X = R X p δ) : σ = τ := by
  apply iso_ext_of_representatives L hL σ τ
  intro X
  let := ha X
  let := hb X
  exact normalizedComponent_unique (P X) (Q X) (R X) (a X) (b X)
    _ _ (hP X) (hQ X) (hσ X) (hτ X)
end NormalizedExtensionality

variable [Abelian A] [HasCountableProducts A]
private theorem roosShiftNaturalIso_component
    (F : B ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ) (V : B ⥤ B) (r : ℤ)
    (β : V ⋙ F ≅ F ⋙
      (whiskeringRight ℕᵒᵖ (CochainComplex A ℤ) (CochainComplex A ℤ)).obj
        (shiftFunctor (CochainComplex A ℤ) r)) (X : B) :
    (WeilConjectures.roosShiftNaturalIso F V r β).hom.app X =
      (WeilConjectures.completedTensorShiftRoosIso (F.obj X) (F.obj (V.obj X)) r
        (WeilConjectures.coneIso _ _ r (β.app X))).hom := rfl
end GenericDescentComponents

attribute [local irreducible] leftLevelIso leftLevelNatIso towerShiftGeneric
  CochainComplex.mapBifunctorShift₁Iso
  CategoryTheory.constantSheaf
  WeilConjectures.unrestrictedIntegralReductionFunctor
  WeilConjectures.unrestrictedIntegralReductionExistence
section StrictModelShift
universe g h
variable {A : Type a} [Category.{b} A] {B : Type c} [Category.{d} B]
  {C : Type e} [Category.{f} C] {D : Type g} [Category.{h} D]
private def strictModelShiftIso (I : A ⥤ B) (U : A ⥤ A) (V : B ⥤ B)
    (S : C ⥤ C) (Z : D ⥤ D) (T : B ⥤ C) (Q : C ⥤ D)
    (h : U ⋙ I = I ⋙ V) (τ : V ⋙ T ≅ T ⋙ S) (q : S ⋙ Q ≅ Q ⋙ Z) :
    U ⋙ (I ⋙ (T ⋙ Q)) ≅ (I ⋙ (T ⋙ Q)) ⋙ Z :=
  Eq.mp (congrArg (fun F : A ⥤ B ↦
    F ⋙ (T ⋙ Q) ≅ (I ⋙ (T ⋙ Q)) ⋙ Z) h.symm)
    (isoWhiskerRight (isoWhiskerLeft I τ) Q ≪≫ isoWhiskerLeft (I ⋙ T) q)
private def strictInputShiftIso (I : A ⥤ B) (U : A ⥤ A) (V : B ⥤ B)
    (F : B ⥤ C) (S : C ⥤ C) (h : U ⋙ I = I ⋙ V) (γ : V ⋙ F ≅ F ⋙ S) :
    U ⋙ (I ⋙ F) ≅ (I ⋙ F) ⋙ S :=
  Eq.mp (congrArg (fun H : A ⥤ B ↦ H ⋙ F ≅ (I ⋙ F) ⋙ S) h.symm)
    (isoWhiskerLeft I γ)
end StrictModelShift

section GenericDescentProperty
variable {A : Type a} [Category.{b} A] {B : Type c} [Category.{d} B]
  {C : Type e} [Category.{f} C]
private theorem hom_ext_of_full (F : A ⥤ B) {X Y : A}
    (f g : F.obj X ⟶ F.obj Y)
    (hFull : ∀ φ : F.obj X ⟶ F.obj Y, ∃ ψ : X ⟶ Y, F.map ψ = φ)
    (h : ∀ f' g' : X ⟶ Y, F.map f' = f → F.map g' = g → f' = g') : f = g := by
  obtain ⟨f', hf⟩ := hFull f
  obtain ⟨g', hg⟩ := hFull g
  rw [← hf, ← hg, h f' g' hf hg]

private theorem descendShift_property (L : A ⥤ B) (U : A ⥤ A) (V : B ⥤ B)
    (S : C ⥤ C) [S.IsEquivalence] (G : B ⥤ C) (T : A ⥤ C)
    (ε : L ⋙ G ≅ T) (κ : U ⋙ L ≅ L ⋙ V) (τ : U ⋙ T ≅ T ⋙ S)
    (hG : ∀ (G' : B ⥤ C) (ε' : L ⋙ G' ≅ T),
      ∃ ι : G ≅ G', isoWhiskerLeft L ι ≪≫ ε' = ε)
    (H : (V ⋙ G ≅ G ⋙ S) → Prop)
    (hH : ∀ σ : V ⋙ G ≅ G ⋙ S,
      (∀ X, G.map (κ.hom.app X) ≫ σ.hom.app (L.obj X) ≫ S.map (ε.hom.app X) =
        ε.hom.app (U.obj X) ≫ τ.hom.app X) → H σ) :
    ∃ σ : V ⋙ G ≅ G ⋙ S, H σ :=
  Exists.imp hH (WeilConjectures.descendShift L U V S G T ε κ τ hG)
end GenericDescentProperty
section GenericSectionLeftShift
variable {A : Type a} [Category.{b} A] [Preadditive A]
  {C : Type c} [Category.{d} C] {J : GrothendieckTopology C}
  {R S : Sheaf J RingCat.{e}}
  (F : A ⥤ SheafOfModules.{f} R) [F.Additive] (π : S ⟶ R)
private local instance (priority := 2000) : F.PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive F
variable (T : SheafOfModules.{f} R ⥤ SheafOfModules.{f} R ⥤ SheafOfModules.{f} R)
  [T.PreservesZeroMorphisms] [T.Additive] [∀ X, (T.obj X).Additive]
private local instance (priority := 2000) : ∀ X, (T.obj X).PreservesZeroMorphisms :=
  fun X ↦ Functor.preservesZeroMorphisms_of_additive (T.obj X)
variable
  [∀ P Q : CochainComplex (SheafOfModules.{f} R) ℤ, CochainComplex.HasMapBifunctor P Q T]

private theorem restrict_apply {M N : SheafOfModules.{f} R} (φ : M ⟶ N)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    ((SheafOfModules.restrictScalars π).map φ).val.app U x = φ.val.app U x := rfl

private theorem leftLevelSectionFormula (P Q : CochainComplex A ℤ) (r i j : ℤ)
    (U : Cᵒᵖ)
    (z : ((T.obj (F.obj (P.X (i + r)))).obj (F.obj (Q.X j))).val.obj U) :
    ((leftLevelIso F (SheafOfModules.restrictScalars π) T P Q r).hom.f (i + j)).val.app U
        ((CochainComplex.ιMapBifunctor
          ((F.mapHomologicalComplex (.up ℤ)).obj (P⟦r⟧))
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) T i j (i + j) rfl).val.app U z) =
      ((CochainComplex.shiftFunctorObjXIso
        (((SheafOfModules.restrictScalars π).mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj P)
            ((F.mapHomologicalComplex (.up ℤ)).obj Q) T))
        r (i + j) ((i + r) + j) (by omega)).inv.val.app U)
        ((CochainComplex.ιMapBifunctor
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) T
          (i + r) j ((i + r) + j) rfl).val.app U z) := by
  have h := leftLevelIso_ι F (SheafOfModules.restrictScalars π) T P Q r i j
  have he := congrArg (fun k ↦ k.val.app U z) h
  have hleft := restrict_apply π
    (CochainComplex.ιMapBifunctor
      ((F.mapHomologicalComplex (.up ℤ)).obj (P⟦r⟧))
      ((F.mapHomologicalComplex (.up ℤ)).obj Q) T i j (i + j) rfl) U z
  have hright := restrict_apply π
    (CochainComplex.ιMapBifunctor
      ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ((F.mapHomologicalComplex (.up ℤ)).obj Q) T (i + r) j ((i + r) + j) rfl) U z
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at he
  have ha := congrArg
    (fun x ↦ ((leftLevelIso F (SheafOfModules.restrictScalars π) T P Q r).hom.f
      (i + j)).val.app U x) hleft
  have hb := congrArg
    (fun x ↦ (CochainComplex.shiftFunctorObjXIso
      (((SheafOfModules.restrictScalars π).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) T))
      r (i + j) ((i + r) + j) (by omega)).inv.val.app U x) hright
  exact ha.symm.trans (he.trans hb)

end GenericSectionLeftShift

namespace WeilConjectures.IntegralSystemRealization
attribute [local implicit_reducible] integralOperationsGoodLocalization
  integralOperationsTensorOnGood

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]

private def leftFiniteNatIso (W : Scheme.{u}) (r : ℤ) (n : ℕ) :
    tensorShiftFirst (CochainComplex (integralTowerModules l E W) ℤ) r ⋙
      integralOperationsTensorLevel l E W n ≅
      integralOperationsTensorLevel l E W n ⋙ shiftFunctor _ r := by
  let := finiteTensorAdditive l E W n
  let := finiteTensorAdditiveFirst l E W n
  exact
    leftLevelNatIso (unrestrictedIntegralReductionFunctor l E W n)
      (SheafOfModules.restrictScalars
        ((sheafCompose (Scheme.ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (completedIntegralCommRingProjectionUnrestricted l E W n)))
      (MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n)) r

private def leftFiniteIso (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (r : ℤ) (n : ℕ) :
    (integralOperationsTensorLevel l E W n).obj (P⟦r⟧, Q) ≅
      ((integralOperationsTensorLevel l E W n).obj (P, Q))⟦r⟧ :=
  (leftFiniteNatIso l E W r n).app (P, Q)

private theorem leftFiniteFormula (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (r : ℤ) (n : ℕ) (i j : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex l E W n).obj P).X (i + r)).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E W n).obj Q).X j).val.obj U) :
    (((leftFiniteIso l E W P Q r n).hom.f (i + j)).val.app U)
        (integralOperationsTotalTensorSection l E W n (P⟦r⟧) Q i j U x y) =
      ((CochainComplex.shiftFunctorObjXIso ((integralOperationsTensorLevel l E W n).obj (P, Q)) r
        (i + j)
              ((i + r) + j) (by omega)).inv.val.app
          U)
        (integralOperationsTotalTensorSection l E W n P Q (i + r) j U x y) := by
  let := finiteTensorAdditive l E W n
  let := finiteTensorAdditiveFirst l E W n
  have h := leftLevelSectionFormula
    (unrestrictedIntegralReductionFunctor l E W n)
    ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (completedIntegralCommRingProjectionUnrestricted l E W n))
    (MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n))
    P Q r i j U (integralOperationsTensorSection l E W n _ _ U x y)
  rw [← leftLevelNatIso_app] at h
  with_unfolding_all exact h

private theorem leftFiniteNatIso_app (W : Scheme.{u}) (r : ℤ) (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    (leftFiniteNatIso l E W r n).app (P, Q) = leftFiniteIso l E W P Q r n := rfl

private theorem leftFiniteNatIso_hom_app (W : Scheme.{u}) (r : ℤ) (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    (leftFiniteNatIso l E W r n).hom.app (P, Q) = (leftFiniteIso l E W P Q r n).hom :=
  congrArg Iso.hom (leftFiniteNatIso_app l E W r n P Q)

private def leftUnshiftedTransition (W : Scheme.{u}) (r : ℤ) (n : ℕ) :
    integralOperationsTensorLevel l E W (n + 1) ⟶ integralOperationsTensorLevel l E W n := by
  let A := CochainComplex (integralTowerModules l E W) ℤ
  let S := shiftFunctor A r
  let H := (whiskeringRight (A × A) A A).obj S
  let V := S.prod (𝟭 A)
  exact
    H.preimage
      ((leftFiniteNatIso l E W r (n + 1)).inv ≫
        whiskerLeft V (integralOperationsTensorTransition l E W n) ≫ (leftFiniteNatIso l E W r
          n).hom)

private theorem leftUnshiftedTransition_square (W : Scheme.{u}) (r : ℤ) (n : ℕ) :
    (leftFiniteNatIso l E W r (n + 1)).hom ≫ whiskerRight (leftUnshiftedTransition l E W r n)
      (shiftFunctor _ r) =
      whiskerLeft (tensorShiftFirst _ r) (integralOperationsTensorTransition l E W n) ≫
        (leftFiniteNatIso l E W r n).hom := by
  have h :=
    Functor.map_preimage ((whiskeringRight _ _ _).obj (shiftFunctor _ r))
      ((leftFiniteNatIso l E W r (n + 1)).inv ≫
        whiskerLeft (tensorShiftFirst _ r) (integralOperationsTensorTransition l E W n) ≫
          (leftFiniteNatIso l E W r n).hom)
  change whiskerRight (leftUnshiftedTransition l E W r n) (shiftFunctor _ r) = _ at h
  rw [h]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

section LeftTransitionGenerators
attribute [local implicit_reducible] integralOperationsTensorLevel integralOperationsRestrict
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj Functor.map₂HomologicalComplex
  integralCoefficientCommRingSheaf completedIntegralCommRingSheafUnrestricted
  integralCoefficientSheaf sheafCompose ModuleCat.restrictScalars

private theorem leftUnshiftedTransition_generator (W : Scheme.{u}) (r : ℤ) (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj P).X p).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj Q).X q).val.obj U) :
    (((leftUnshiftedTransition l E W r n).app (P, Q)).f (p + q)).val.app U
        (integralOperationsTotalTensorSection l E W (n + 1) P Q p q U x y) =
      integralOperationsTotalTensorSection l E W n P Q p q U
        ((((unrestrictedIntegralTransition l E W n).app P).f p).val.app U x)
        ((((unrestrictedIntegralTransition l E W n).app Q).f q).val.app U y) := by
  obtain ⟨i, rfl⟩ : ∃ i : ℤ, p = i + r := ⟨p - r, by omega⟩
  have he :=
    congrArg
      (fun k ↦
        (((k.app (P, Q)).f (i + q)).val.app U)
          (integralOperationsTotalTensorSection l E W (n + 1) (P⟦r⟧) Q i q U x y))
      (leftUnshiftedTransition_square l E W r n)
  dsimp only [NatTrans.comp_app, HomologicalComplex.comp_f, SheafOfModules.comp_val,
    PresheafOfModules.comp_app,
    ModuleCat.comp_apply, whiskerLeft_app, whiskerRight_app] at he
  rw [leftFiniteNatIso_hom_app, leftFiniteNatIso_hom_app] at he
  simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply, Functor.prod_obj, Functor.id_obj,
    tensorShiftFirst] at he
  have hleft :=
    congrArg
      (fun z ↦
        (((((shiftFunctor _ r).map ((leftUnshiftedTransition l E W r n).app (P, Q))).f (i +
          q)).val.app U) z))
      (leftFiniteFormula l E W P Q r (n + 1) i q U x y)
  have ht := (integralOperationsTensorTransition_existsUnique l E W n).exists.choose_spec (P⟦r⟧)
    Q i q U x y
  have hright := congrArg (fun z ↦ (((leftFiniteIso l E W P Q r n).hom.f (i + q)).val.app U) z) ht
  have hs :=
    leftFiniteFormula l E W P Q r n i q U ((((unrestrictedIntegralTransition l E W n).app P).f (i
      + r)).val.app U x)
      ((((unrestrictedIntegralTransition l E W n).app Q).f q).val.app U y)
  rw [reductionTransition_shift] at hright
  have hcomb := hleft.symm.trans (he.trans (hright.trans hs))
  simp only [CochainComplex.shiftFunctor_map_f', CochainComplex.shiftFunctorObjXIso] at hcomb
  exact
    reindex_section ((leftUnshiftedTransition l E W r n).app (P, Q)) (show i + q + r = (i + r) +
      q by omega) U _ _
      hcomb

end LeftTransitionGenerators

private theorem leftFinite_transition (W : Scheme.{u}) (r : ℤ) (n : ℕ) :
    whiskerLeft (tensorShiftFirst _ r) (integralOperationsTensorTransition l E W n) ≫
        (leftFiniteNatIso l E W r n).hom =
      (leftFiniteNatIso l E W r (n + 1)).hom ≫
        whiskerRight (integralOperationsTensorTransition l E W n) (shiftFunctor _ r) := by
  have h :=
    (integralOperationsTensorTransition_existsUnique l E W n).unique
      (leftUnshiftedTransition_generator l E W r n)
      (integralOperationsTensorTransition_existsUnique l E W n).exists.choose_spec
  exact
    (leftUnshiftedTransition_square l E W r n).symm.trans
      (congrArg (fun τ ↦ (leftFiniteNatIso l E W r (n + 1)).hom ≫ whiskerRight τ (shiftFunctor _
        r)) h)

attribute [local irreducible] leftFiniteIso leftFiniteNatIso

private noncomputable def leftTowerNatIso (W : Scheme.{u}) (r : ℤ) :
    tensorShiftFirst (CochainComplex (integralTowerModules l E W) ℤ) r ⋙
      integralOperationsTensorTowerFunctor l E W ≅
    integralOperationsTensorTowerFunctor l E W ⋙
      (whiskeringRight ℕᵒᵖ (CochainComplex (integralTowerModules l E W) ℤ)
        (CochainComplex (integralTowerModules l E W) ℤ)).obj (shiftFunctor _ r) :=
  towerShiftGeneric (integralOperationsTensorLevel l E W)
    (integralOperationsTensorTransition l E W) (tensorShiftFirst _ r) (shiftFunctor _ r)
    (leftFiniteNatIso l E W r) (leftFinite_transition l E W r)

private noncomputable def leftTowerIso (W : Scheme.{u}) (r : ℤ)
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    (integralOperationsTensorTowerFunctor l E W).obj (P⟦r⟧, Q) ≅
      (integralOperationsTensorTowerFunctor l E W).obj (P, Q) ⋙ shiftFunctor _ r :=
  (leftTowerNatIso l E W r).app (P, Q)

private theorem leftTowerIso_hom_app (W : Scheme.{u}) (r : ℤ)
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕᵒᵖ) :
    (leftTowerIso l E W r P Q).hom.app n =
      (leftFiniteIso l E W P Q r n.unop).hom := by
  exact (towerShiftGeneric_hom_app (integralOperationsTensorLevel l E W)
    (integralOperationsTensorTransition l E W) (tensorShiftFirst _ r) (shiftFunctor _ r)
    (leftFiniteNatIso l E W r) (leftFinite_transition l E W r) (P, Q) n).trans
    (leftFiniteNatIso_hom_app l E W r n.unop P Q)

attribute [local implicit_reducible] leftTowerIso

section LeftTowerFormula
attribute [local implicit_reducible] integralOperationsTensorLevel integralOperationsRestrict
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj Functor.map₂HomologicalComplex
  integralCoefficientCommRingSheaf completedIntegralCommRingSheafUnrestricted
  integralCoefficientSheaf sheafCompose ModuleCat.restrictScalars

private theorem leftTowerFormula (W : Scheme.{u}) (r : ℤ)
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    integralTensorLeftFormula l E W P Q r (leftTowerIso l E W r P Q) := by
  intro n i j U x y
  rw [leftTowerIso_hom_app]
  dsimp only [integralOperationsTensorTowerFunctor, Functor.comp_obj,
    Functor.flip_obj_obj, Functor.ofOpSequence_obj]
  exact leftFiniteFormula l E W P Q r n i j U x y
end LeftTowerFormula

section LeftShiftExtensionality
private theorem finitePure_ext (W : Scheme.{u}) (n : ℕ)
    (M N H : integralOperationsFiniteModules l E W n)
    (f g : MonoidalCategory.tensorObj M N ⟶ H)
    (h : ∀ (U : W.ProEtᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
      f.val.app U (integralOperationsTensorSection l E W n M N U x y) =
      g.val.app U (integralOperationsTensorSection l E W n M N U x y)) : f = g := by
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let := integralCoefficientAbSheafify.{u, u} W
  let := integralCoefficientAbLocallyBijective.{u, u} W
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1}
    (J := Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W n)
  let e := SheafOfModules.tensorObjIsoSheafification
    (R := integralCoefficientCommRingSheaf l E W n) M N
  apply (cancel_epi e.inv).mp
  let R := (sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (integralCoefficientCommRingSheaf l E W n)
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 R.obj)
  apply (adj.homEquiv (MonoidalCategory.tensorObj M.val N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h U x y

private theorem leftFormula_ext (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (r : ℤ)
    (α β : (integralOperationsTensorTowerFunctor l E W).obj (P⟦r⟧, Q) ≅
      (integralOperationsTensorTowerFunctor l E W).obj (P, Q) ⋙ shiftFunctor _ r)
    (hα : integralTensorLeftFormula l E W P Q r α)
    (hβ : integralTensorLeftFormula l E W P Q r β) : α = β := by
  apply Iso.ext
  apply NatTrans.ext
  funext n
  apply HomologicalComplex.hom_ext
  intro k
  let π := (sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (completedIntegralCommRingProjectionUnrestricted l E W n.unop)
  let := completedProjection_locallySurjective l E W n.unop
  let P' := (unrestrictedIntegralFiniteComplex l E W n.unop).obj (P⟦r⟧)
  let Q' := (unrestrictedIntegralFiniteComplex l E W n.unop).obj Q
  let T := MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n.unop)
  let X := (CochainComplex.mapBifunctor P' Q' T).X k
  let Y := (CochainComplex.mapBifunctor
    ((unrestrictedIntegralFiniteComplex l E W n.unop).obj P) Q' T).X (k + r)
  let e := PresheafOfModules.restrictHomEquivOfIsLocallySurjective
    π.hom Y.isSheaf (M₁ := X.val)
  apply hom_ext_of_full (SheafOfModules.restrictScalars π) (X := X) (Y := Y)
  · intro φ
    refine ⟨⟨e.symm φ.val⟩, ?_⟩
    apply SheafOfModules.hom_ext
    exact e.apply_symm_apply _
  · intro f g hf hg
    apply HomologicalComplex.mapBifunctor.hom_ext
      (K₁ := P') (K₂ := Q') (F := T) (c := .up ℤ)
    intro i j hij
    apply finitePure_ext l E W n.unop
    intro U x y
    change i + j = k at hij
    subst k
    have h := (hα n.unop i j U x y).trans (hβ n.unop i j U x y).symm
    rw [← hf, ← hg] at h
    exact h

private theorem coneFormula_ext {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] (C D : ℕᵒᵖ ⥤ CochainComplex A ℤ) (r : ℤ)
    (α : D ≅ C ⋙ shiftFunctor (CochainComplex A ℤ) r)
    (δ ε : CochainComplex.mappingCone (completedTensorShiftOneSub D) ≅
      (CochainComplex.mappingCone (completedTensorShiftOneSub C))⟦r⟧)
    (hδ : completedTensorShiftConeFormula C D r α δ)
    (hε : completedTensorShiftConeFormula C D r α ε) : δ = ε := by
  apply Iso.ext
  apply HomologicalComplex.hom_ext
  intro j
  apply CochainComplex.mappingCone.ext_from _ (j + 1) j rfl
  · exact (hδ.2 (j + 1) j (by omega)).trans (hε.2 (j + 1) j (by omega)).symm
  · exact (hδ.1 j).trans (hε.1 j).symm

attribute [local irreducible] integralCompletedTensorComparison
attribute [local irreducible] integralOperationsTensorTowerFunctor

end LeftShiftExtensionality

section ModelNormalization
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
  {D : Type v} [Category.{w} D]
  (r : ℤ) (Good : ObjectProperty (CochainComplex A ℤ))

private abbrev modelLocalization (F : CochainComplex A ℤ ⥤ D) := Good.ι ⋙ F

private abbrev modelTensor
    (T : CochainComplex A ℤ × CochainComplex A ℤ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (F : CochainComplex A ℤ ⥤ D) :=
  (Good.ι.prod Good.ι) ⋙ (T ⋙ integralOperationsRoosFunctor) ⋙ F

private abbrev modelShift (hShift : ∀ P : Good.FullSubcategory, Good (P.obj⟦r⟧)) :=
  (Good.lift (Good.ι ⋙ shiftFunctor (CochainComplex A ℤ) r) hShift).prod
    (𝟭 Good.FullSubcategory)

private def modelInputIso (F : CochainComplex A ℤ ⥤ D) (S : D ⥤ D)
    (γ : shiftFunctor (CochainComplex A ℤ) r ⋙ F ≅ F ⋙ S)
    (hShift : ∀ P : Good.FullSubcategory, Good (P.obj⟦r⟧)) :
    modelShift r Good hShift ⋙ (modelLocalization Good F).prod (modelLocalization Good F) ≅
      (modelLocalization Good F).prod (modelLocalization Good F) ⋙ S.prod (𝟭 D) :=
  firstInputIso (Good.lift (Good.ι ⋙ shiftFunctor _ r) hShift)
    (modelLocalization Good F) S
    (strictInputShiftIso Good.ι (Good.lift (Good.ι ⋙ shiftFunctor _ r) hShift)
      (shiftFunctor _ r) F S (by rfl) γ)

omit [HasCountableProducts A] in
private theorem modelInputIso_hom_app (F : CochainComplex A ℤ ⥤ D) (S : D ⥤ D)
    (γ : shiftFunctor (CochainComplex A ℤ) r ⋙ F ≅ F ⋙ S)
    (hShift : ∀ P : Good.FullSubcategory, Good (P.obj⟦r⟧)) (P Q : Good.FullSubcategory) :
    (modelInputIso r Good F S γ hShift).hom.app (P, Q) =
      (γ.hom.app P.obj, 𝟙 (F.obj Q.obj)) := rfl

variable (T : CochainComplex A ℤ × CochainComplex A ℤ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ)

private def modelOutputIso (F : CochainComplex A ℤ ⥤ D) (S : D ⥤ D)
    (γ : shiftFunctor (CochainComplex A ℤ) r ⋙ F ≅ F ⋙ S)
    (hShift : ∀ P : Good.FullSubcategory, Good (P.obj⟦r⟧))
    (β : tensorShiftFirst (CochainComplex A ℤ) r ⋙ T ≅ T ⋙
      (whiskeringRight ℕᵒᵖ (CochainComplex A ℤ) (CochainComplex A ℤ)).obj
        (shiftFunctor _ r)) :
    modelShift r Good hShift ⋙ modelTensor Good T F ≅ modelTensor Good T F ⋙ S :=
  strictModelShiftIso (Good.ι.prod Good.ι) (modelShift r Good hShift)
    (tensorShiftFirst (CochainComplex A ℤ) r) (shiftFunctor _ r) S
    (T ⋙ integralOperationsRoosFunctor) F (by rfl)
    (roosShiftNaturalIso T (tensorShiftFirst (CochainComplex A ℤ) r) r β) γ

private theorem modelOutputIso_hom_app (F : CochainComplex A ℤ ⥤ D) (S : D ⥤ D)
    (γ : shiftFunctor (CochainComplex A ℤ) r ⋙ F ≅ F ⋙ S)
    (hShift : ∀ P : Good.FullSubcategory, Good (P.obj⟦r⟧))
    (β : tensorShiftFirst (CochainComplex A ℤ) r ⋙ T ≅ T ⋙
      (whiskeringRight ℕᵒᵖ (CochainComplex A ℤ) (CochainComplex A ℤ)).obj
        (shiftFunctor _ r)) (P Q : Good.FullSubcategory) :
    (modelOutputIso r Good T F S γ hShift β).hom.app (P, Q) =
      F.map ((roosShiftNaturalIso T (tensorShiftFirst (CochainComplex A ℤ) r) r β).hom.app
        (P.obj, Q.obj)) ≫ γ.hom.app ((T ⋙ integralOperationsRoosFunctor).obj (P.obj, Q.obj)) :=
  rfl

attribute [local irreducible] modelInputIso modelOutputIso

variable
  (Φ : ∀ P Q : CochainComplex A ℤ,
    (T.obj (P⟦r⟧, Q) ≅ T.obj (P, Q) ⋙ shiftFunctor (CochainComplex A ℤ) r) → Prop)
  (hShift : ∀ P : Good.FullSubcategory, Good (P.obj⟦r⟧))
  (β : tensorShiftFirst (CochainComplex A ℤ) r ⋙ T ≅ T ⋙
    (whiskeringRight ℕᵒᵖ (CochainComplex A ℤ) (CochainComplex A ℤ)).obj (shiftFunctor _ r))
  (hΦ : ∀ P Q, Φ P Q (β.app (P, Q)))

include hΦ in
private theorem modelShift_property (F : CochainComplex A ℤ ⥤ D) (S : D ⥤ D)
    (γ : shiftFunctor (CochainComplex A ℤ) r ⋙ F ≅ F ⋙ S) (G : D × D ⥤ D)
    (ε : (modelLocalization Good F).prod (modelLocalization Good F) ⋙ G ≅
      modelTensor Good T F) (σ : S.prod (𝟭 D) ⋙ G ≅ G ⋙ S)
    (hσ : ∀ X, G.map ((modelInputIso r Good F S γ hShift).hom.app X) ≫
      σ.hom.app (((modelLocalization Good F).prod (modelLocalization Good F)).obj X) ≫
      S.map (ε.hom.app X) = ε.hom.app ((modelShift r Good hShift).obj X) ≫
        (modelOutputIso r Good T F S γ hShift β).hom.app X) :
    integralTensorLeftModelProperty r Good T Φ F S γ G ε σ := by
  intro P Q
  refine ⟨hShift P, β.app (P.obj, Q.obj), hΦ P.obj Q.obj,
    coneIso _ _ r (β.app (P.obj, Q.obj)), coneIso_formula _ _ r (β.app (P.obj, Q.obj)), ?_⟩
  have hroos := roosShiftNaturalIso_component T
    (tensorShiftFirst (CochainComplex A ℤ) r) r β (P.obj, Q.obj)
  have houtput := (modelOutputIso_hom_app r Good T F S γ hShift β P Q).trans
    (mapComp_congr F hroos rfl)
  have hinput := congrArg G.map (modelInputIso_hom_app r Good F S γ hShift P Q)
  exact normalizeComponent hinput houtput (hσ (P, Q))

include hShift β hΦ in
private theorem modelShift_exists (F : CochainComplex A ℤ ⥤ D) (S : D ⥤ D)
    [S.IsEquivalence] (γ : shiftFunctor (CochainComplex A ℤ) r ⋙ F ≅ F ⋙ S)
    (G : D × D ⥤ D)
    (ε : (modelLocalization Good F).prod (modelLocalization Good F) ⋙ G ≅
      modelTensor Good T F)
    (hG : ∀ (G' : D × D ⥤ D)
      (ε' : (modelLocalization Good F).prod (modelLocalization Good F) ⋙ G' ≅
        modelTensor Good T F), ∃ ι : G ≅ G',
      isoWhiskerLeft ((modelLocalization Good F).prod (modelLocalization Good F)) ι ≪≫ ε' = ε) :
    ∃ σ : S.prod (𝟭 D) ⋙ G ≅ G ⋙ S,
      integralTensorLeftModelProperty r Good T Φ F S γ G ε σ :=
  descendShift_property ((modelLocalization Good F).prod (modelLocalization Good F))
    (modelShift r Good hShift) (S.prod (𝟭 D)) S G (modelTensor Good T F) ε
    (modelInputIso r Good F S γ hShift) (modelOutputIso r Good T F S γ hShift β) hG
    (integralTensorLeftModelProperty r Good T Φ F S γ G ε)
    (modelShift_property r Good T Φ hShift β hΦ F S γ G ε)

variable (hΦ_unique : ∀ P Q α α', Φ P Q α → Φ P Q α' → α = α')

include hΦ_unique in
private theorem modelShift_ext (F : CochainComplex A ℤ ⥤ D) (S : D ⥤ D)
    (γ : shiftFunctor (CochainComplex A ℤ) r ⋙ F ≅ F ⋙ S) (G : D × D ⥤ D)
    (ε : (modelLocalization Good F).prod (modelLocalization Good F) ⋙ G ≅
      modelTensor Good T F)
    (hL : ∀ Y, ∃ X, Nonempty ((modelLocalization Good F).obj X ≅ Y))
    (σ τ : S.prod (𝟭 D) ⋙ G ≅ G ⋙ S)
    (hσ : integralTensorLeftModelProperty r Good T Φ F S γ G ε σ)
    (hτ : integralTensorLeftModelProperty r Good T Φ F S γ G ε τ) : σ = τ := by
  exact iso_ext_normalized ((modelLocalization Good F).prod (modelLocalization Good F))
    (fun Y ↦ by
      obtain ⟨P, ⟨eP⟩⟩ := hL Y.1
      obtain ⟨Q, ⟨eQ⟩⟩ := hL Y.2
      exact ⟨(P, Q), ⟨eP.prod eQ⟩⟩)
    (F := S.prod (𝟭 D) ⋙ G) (G := G ⋙ S)
    (fun X ↦ G.obj (F.obj (X.1.obj⟦r⟧), F.obj X.2.obj))
    (fun X ↦ S.obj ((modelTensor Good T F).obj X))
    (fun X ↦ G.map (γ.hom.app X.1.obj, 𝟙 (F.obj X.2.obj)))
    (fun X ↦ by
      have : IsIso (show (F.obj (X.1.obj⟦r⟧), F.obj X.2.obj) ⟶
          (S.obj (F.obj X.1.obj), F.obj X.2.obj) from
          (γ.hom.app X.1.obj, 𝟙 _)) :=
        (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
      infer_instance)
    (fun X ↦ S.map (ε.hom.app X)) (fun _ ↦ inferInstance)
    (fun X ↦ Good (X.1.obj⟦r⟧)) (fun X ↦ Φ X.1.obj X.2.obj)
    (fun X ↦ completedTensorShiftConeFormula
      (T.obj (X.1.obj, X.2.obj)) (T.obj (X.1.obj⟦r⟧, X.2.obj)) r)
    (fun X hP δ ↦ ε.hom.app (⟨X.1.obj⟦r⟧, hP⟩, X.2) ≫ F.map
      (completedTensorShiftRoosIso (T.obj (X.1.obj, X.2.obj))
        (T.obj (X.1.obj⟦r⟧, X.2.obj)) r δ).hom ≫
      γ.hom.app ((T ⋙ integralOperationsRoosFunctor).obj (X.1.obj, X.2.obj)))
    (fun X ↦ hΦ_unique X.1.obj X.2.obj) (fun _ ↦ coneFormula_ext _ _ r)
    σ τ (fun X ↦ hσ X.1 X.2) (fun X ↦ hτ X.1 X.2)

include hShift β hΦ hΦ_unique in
private theorem modelShift_unique (F : CochainComplex A ℤ ⥤ D) (S : D ⥤ D)
    [S.IsEquivalence] (γ : shiftFunctor (CochainComplex A ℤ) r ⋙ F ≅ F ⋙ S)
    (G : D × D ⥤ D)
    (ε : (modelLocalization Good F).prod (modelLocalization Good F) ⋙ G ≅
      modelTensor Good T F)
    (hG : ∀ (G' : D × D ⥤ D)
      (ε' : (modelLocalization Good F).prod (modelLocalization Good F) ⋙ G' ≅
        modelTensor Good T F), ∃ ι : G ≅ G',
      isoWhiskerLeft ((modelLocalization Good F).prod (modelLocalization Good F)) ι ≪≫ ε' = ε)
    (hL : ∀ Y, ∃ X, Nonempty ((modelLocalization Good F).obj X ≅ Y)) :
    ∃! σ : S.prod (𝟭 D) ⋙ G ≅ G ⋙ S,
      integralTensorLeftModelProperty r Good T Φ F S γ G ε σ := by
  obtain ⟨σ, hσ⟩ := modelShift_exists r Good T Φ hShift β hΦ F S γ G ε hG
  exact ⟨σ, hσ, fun τ hτ ↦ modelShift_ext r Good T Φ hΦ_unique F S γ G ε hL τ σ hτ hσ⟩
end ModelNormalization

private theorem goodModelRepresentative (W : Scheme.{u}) (Y : Integral l E W) :
    ∃ P : (integralOperationsGoodComplex l E W).FullSubcategory,
      Nonempty ((integralOperationsGoodLocalization l E W).obj P ≅ Y) := by
  have := integralOperationsGoodLocalization_isLocalization l E W
  have := Localization.essSurj (integralOperationsGoodLocalization l E W)
    ((HomologicalComplex.quasiIso (integralTowerModules l E W) (.up ℤ)).inverseImage
      (integralOperationsGoodComplex l E W).ι)
  exact ⟨(integralOperationsGoodLocalization l E W).objPreimage Y,
    ⟨(integralOperationsGoodLocalization l E W).objObjPreimageIso Y⟩⟩

attribute [local irreducible] integralTensorLeftModelProperty integralTensorLeftFormula
  completedTensorShiftConeFormula completedTensorShiftRoosIso
attribute [local instance 3000] integralOperationsCommHasDerivedCategory

/-- The unsigned finite tensor shift descends to a unique normalized completed shift.
Source: Stacks 011G, 012Z, 014E, 06YU, 0941; blueprint purity transport, Step 2
(blueprint: lem-pur-integral-tensor-left-shift-unique).

Proof: reduction and restriction act termwise, so the first tensor shift has
coefficient one on each generator. Conjugating the quotient transition by these
comparisons gives its original generator formula, hence the same transition.
The comparisons therefore assemble into a natural tower isomorphism. Apply the
product/cone comparison with coordinates (1,(-1)^r), shift by -1, and commute
shifts. Shift preserves good complexes. Localize this natural comparison and use
the universal property of the completed tensor descent to obtain the derived
isomorphism and its normalization on every good pair. Representative
extensionality proves uniqueness. -/
theorem integralTensorLeftShift_existsUnique (W : Scheme.{u}) (r : ℤ) :
    ∃! σ : tensorShiftFirst (Integral l E W) r ⋙ integralCompletedTensor l E W ≅
      integralCompletedTensor l E W ⋙ shiftFunctor (Integral l E W) r,
      integralTensorLeftProperty l E W r σ := by
  apply modelShift_unique (β := leftTowerNatIso l E W r)
  case hShift => exact fun P ↦ goodShift l E W P r
  case hΦ => exact fun P Q ↦ leftTowerFormula l E W r P Q
  case hΦ_unique => exact fun P Q ↦ leftFormula_ext l E W P Q r
  case hG => exact completedTensorUniversal l E W
  case hL => exact goodModelRepresentative l E W
end WeilConjectures.IntegralSystemRealization
