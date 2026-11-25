/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilRingedPresentation
import WeilConjectures.CategoryTheory.RingedForgetTwoInjective.StandardBifunctorHomModel
import WeilConjectures.CategoryTheory.Ringed.RingedHomComplexComparison
import WeilConjectures.CategoryTheory.K.KInjectiveHomComparisonDescent
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Monoidal.Transport

/-! # Closed structure for native derived internal Hom

Source: native tensor lift, adjoint-construction step; Stacks Tags 06YS and 08J9.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProEtaleWeilSheaf
private theorem closedFromCurrying
    {D : Type*} [Category D] [MonoidalCategory D]
    (H : Dᵒᵖ × D ⥤ D)
    (e : ∀ T P I : D, (T ⊗ P ⟶ I) ≃ (T ⟶ H.obj (op P, I)))
    (hn : ∀ (T T' P P' I I' : D)
      (f : T' ⟶ T) (g : P' ⟶ P) (h : I ⟶ I') (φ : T ⟶ H.obj (op P, I)),
      (e T' P' I').symm (f ≫ φ ≫ H.map (Prod.mkHom g.op h)) =
        (f ⊗ₘ g) ≫ (e T P I).symm φ ≫ h) :
    ∃ S : CoefficientClosedStructure H,
      S.monoidal = (inferInstance : MonoidalCategory D) ∧
        ∀ T P I, HEq (S.transpose T P I) (e T P I) := by
  have hId (P I : D) : H.map (Prod.mkHom (𝟙 P).op (𝟙 I)) = 𝟙 _ := by
    change H.map (𝟙 _) = 𝟙 _
    exact H.map_id _
  let adj : ∀ P : D, tensorRight P ⊣ Prod.sectR (op P) D ⋙ H := fun P ↦
    Adjunction.mkOfHomEquiv
      { homEquiv := fun T I ↦ e T P I
        homEquiv_naturality_left_symm := fun {T' T I} f φ ↦ by
          change (e T' P I).symm (f ≫ φ) = (f ▷ P) ≫ (e T P I).symm φ
          simpa only [hId, Category.comp_id, tensorHom_id] using
              hn T T' P P I I f (𝟙 P) (𝟙 I) φ
        homEquiv_naturality_right := fun {T} {I I'} ψ h ↦ by
          apply (e T P I').symm.injective
          have he := hn T T P P I I' (𝟙 T) (𝟙 P) h (e T P I ψ)
          change (e T P I').symm (e T P I' (ψ ≫ h)) =
            (e T P I').symm (e T P I ψ ≫ H.map (𝟙 (op P), h))
          rw [Equiv.symm_apply_apply]
          simpa only [op_id, id_tensorHom_id, Category.id_comp,
            Equiv.symm_apply_apply] using he.symm }
  let S : CoefficientClosedStructure H :=
    { monoidal := inferInstance
      adjunction := adj
      evaluation_naturality := by
        intro P P' I g
        have h₁ := hn (H.obj (op P', I)) (H.obj (op P, I)) P' P' I I
          (H.map (Prod.mkHom g.op (𝟙 I))) (𝟙 P') (𝟙 I) (𝟙 _)
        have h₂ := hn (H.obj (op P, I)) (H.obj (op P, I)) P P' I I
          (𝟙 _) g (𝟙 I) (𝟙 _)
        change (H.map (Prod.mkHom g.op (𝟙 I)) ▷ P') ≫
            (e (H.obj (op P', I)) P' I).symm (𝟙 _) =
          (H.obj (op P, I) ◁ g) ≫ (e (H.obj (op P, I)) P I).symm (𝟙 _)
        simp only [hId, Category.id_comp, Category.comp_id, tensorHom_id, id_tensorHom]
          at h₁ h₂
        exact h₁.symm.trans h₂ }
  refine ⟨S, rfl, ?_⟩
  intro T P I
  apply heq_of_eq
  change (adj P).homEquiv T I = e T P I
  dsimp only [adj]
  rw [Adjunction.mkOfHomEquiv_homEquiv]

private theorem uncurryNatural
    {D : Type*} [Category D] {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H)
    (T T' P P' I I' : D) (f : T' ⟶ T) (g : P' ⟶ P) (h : I ⟶ I')
    (φ : T ⟶ H.obj (op P, I)) :
    (S.transpose T' P' I').symm (f ≫ φ ≫ H.map (Prod.mkHom g.op h)) =
      S.tensor.map (Prod.mkHom f g) ≫ (S.transpose T P I).symm φ ≫ h := by
  let := S.monoidal
  have he (A B C : D) (ψ : A ⟶ H.obj (op B, C)) :
      (S.transpose A B C).symm ψ =
        S.tensor.map (Prod.mkHom ψ (𝟙 B)) ≫ S.evaluation B C := by
    dsimp only [CoefficientClosedStructure.transpose, CoefficientClosedStructure.evaluation,
      CoefficientClosedStructure.tensor, Adjunction.homEquiv, Equiv.symm]
    change (ψ ▷ B) ≫ _ = (ψ ⊗ₘ 𝟙 B) ≫ _
    rw [tensorHom_id]
  have ht : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom g.op (𝟙 I))) (𝟙 P')) ≫
      S.evaluation P' I =
      S.tensor.map (Prod.mkHom (𝟙 (H.obj (op P, I))) g) ≫ S.evaluation P I := by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using
      S.evaluation_naturality P P' I g
  have harg : (S.transpose T' P' I).symm
      (f ≫ φ ≫ H.map (Prod.mkHom g.op (𝟙 I))) =
      S.tensor.map (Prod.mkHom f g) ≫ (S.transpose T P I).symm φ := by
    rw [he, he]
    calc
      _ = S.tensor.map (Prod.mkHom f (𝟙 P')) ≫
          S.tensor.map (Prod.mkHom φ (𝟙 P')) ≫
          S.tensor.map (Prod.mkHom (H.map (Prod.mkHom g.op (𝟙 I))) (𝟙 P')) ≫
            S.evaluation P' I := by
        rw [← S.tensor.map_comp_assoc, ← S.tensor.map_comp_assoc]
        simp
      _ = S.tensor.map (Prod.mkHom f (𝟙 P')) ≫
          S.tensor.map (Prod.mkHom φ (𝟙 P')) ≫
          S.tensor.map (Prod.mkHom (𝟙 (H.obj (op P, I))) g) ≫
            S.evaluation P I := by rw [ht]
      _ = _ := by
        rw [← S.tensor.map_comp_assoc, ← S.tensor.map_comp_assoc,
          ← S.tensor.map_comp_assoc]
        simp
  have hd : H.map (Prod.mkHom g.op h) =
      H.map (Prod.mkHom g.op (𝟙 I)) ≫ H.map (Prod.mkHom (𝟙 (op P')) h) := by
    rw [← H.map_comp]
    simp
  calc
    _ = (S.transpose T' P' I').symm
        ((f ≫ φ ≫ H.map (Prod.mkHom g.op (𝟙 I))) ≫
          H.map (Prod.mkHom (𝟙 (op P')) h)) := by
      rw [hd]
      simp only [Category.assoc]
    _ = (S.transpose T' P' I).symm
        (f ≫ φ ≫ H.map (Prod.mkHom g.op (𝟙 I))) ≫ h :=
      (S.adjunction P').homEquiv_naturality_right_symm _ h
    _ = _ := by rw [harg]; simp only [Category.assoc]

private theorem closedTransport
    {C D : Type*} [Category C] [Category D]
    (E : C ≌ D) (H : Cᵒᵖ × C ⥤ C) (H' : Dᵒᵖ × D ⥤ D)
    (S : CoefficientClosedStructure H')
    (η : H ⋙ E.functor ≅ E.functor.op.prod E.functor ⋙ H') :
    Nonempty (CoefficientClosedStructure H) := by
  let := S.monoidal
  let := Monoidal.transport E.symm
  let F := E.functor
  let : F.Monoidal :=
    inferInstanceAs (Monoidal.equivalenceTransported E.symm).inverse.Monoidal
  let s (T P I : D) : (T ⊗ P ⟶ I) ≃ (T ⟶ H'.obj (op P, I)) :=
    (S.adjunction P).homEquiv T I
  let ff := Functor.FullyFaithful.ofFullyFaithful F
  let e (T P I : C) : (T ⟶ H.obj (op P, I)) ≃ (T ⊗ P ⟶ I) :=
    ff.homEquiv.trans ((η.app (op P, I)).homToEquiv.trans
      ((s (F.obj T) (F.obj P) (F.obj I)).symm.trans
        ((Functor.Monoidal.μIso F T P).homFromEquiv.trans ff.homEquiv.symm)))
  have he (T P I : C) (φ : T ⟶ H.obj (op P, I)) :
      F.map (e T P I φ) = (Functor.Monoidal.μIso F T P).inv ≫
        (s (F.obj T) (F.obj P) (F.obj I)).symm
          (F.map φ ≫ η.hom.app (op P, I)) := by
    simp [e, Iso.homFromEquiv, Iso.homToEquiv]
    rfl
  obtain ⟨W, _, _⟩ := closedFromCurrying H (fun T P I ↦ (e T P I).symm) (by
    intro T T' P P' I I' f g h φ
    change e T' P' I' (f ≫ φ ≫ H.map (Prod.mkHom g.op h)) = (f ⊗ₘ g) ≫ e T P I φ ≫ h
    apply F.map_injective
    simp only [he, Functor.map_comp, Category.assoc]
    have hη := η.hom.naturality (X := (op P, I)) (Y := (op P', I')) (Prod.mkHom g.op h)
    change F.map (H.map (Prod.mkHom g.op h)) ≫ η.hom.app (op P', I') =
      η.hom.app (op P, I) ≫ H'.map (Prod.mkHom (F.map g).op (F.map h)) at hη
    have hn := uncurryNatural S (F.obj T) (F.obj T') (F.obj P) (F.obj P')
      (F.obj I) (F.obj I') (F.map f) (F.map g) (F.map h)
      (F.map φ ≫ η.hom.app (op P, I))
    change (s (F.obj T') (F.obj P') (F.obj I')).symm
        (F.map f ≫ (F.map φ ≫ η.hom.app (op P, I)) ≫
          H'.map (Prod.mkHom (F.map g).op (F.map h))) =
      (F.map f ⊗ₘ F.map g) ≫
        (s (F.obj T) (F.obj P) (F.obj I)).symm
          (F.map φ ≫ η.hom.app (op P, I)) ≫ F.map h at hn
    simp only [Category.assoc] at hn
    rw [hη, hn]
    simp only [Functor.Monoidal.μIso_inv,
      Functor.OplaxMonoidal.δ_natural_assoc])
  exact ⟨W⟩

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The native product-total Hom model admits a closed derived tensor structure.

Source: internal-Hom/transposition paragraph and native tensor lift steps 1--2;
Stacks Tags 06YS and 08J9.
The construction presents native Weil sheaves on the Frobenius action site,
transports the normalized ringed-site tensor--Hom adjunction through the additive
module equivalence, and identifies the resulting product-total Hom with the
specified row-sign model in `NativeClosedHomModels`. The tensor, evaluation,
and source-parameter naturality fields are part of this closed-structure package.
(blueprint: lem-sf-native-weil-hom-closed-structure)
-/
theorem native_weil_hom_closed_structure
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (M : NativeClosedHomModels k₀ l X) :
    Nonempty (CoefficientClosedStructure M.weilHom) := by
  classical
  obtain ⟨C, instC, J, R, E, hE, ⟨h⟩⟩ := native_weil_ringed_presentation k₀ l X
  let := instC
  let := hE
  let A := RingedTensorModules.{u + 1, u + 1, u + 1} J R
  let : HasDerivedCategory.{u + 2} A := HasDerivedCategory.standard A
  let U := E.functor
  let B := CategoryTheory.RingedForgetTwoInjective.standardHomModel (ihomBifunctor k₀ l X)
  let F := Functor.uncurry.obj (homComplexFunctor (R := R))
  obtain ⟨chain, _⟩ := ringedHomComplexComparison U
    (ihomBifunctor k₀ l X) (SheafOfModules.homFunctor (R := R))
    B.complex F B.π (homComplexπ (R := R))
    B.product (homComplexIsLimit (R := R))
    B.differential (homComplex_d_π (R := R)) B.map_projection
    (by
      intro K K' I I' f g n p q hpq
      simpa only [F, Functor.uncurry_obj_map, Functor.uncurry_obj_obj,
        SheafOfModules.homFunctor_obj_obj, Quiver.Hom.unop_op,
        SheafOfModules.homFunctor_map_app, SheafOfModules.homFunctor_obj_map,
        Category.assoc, SheafOfModules.homObjMap_comp_homObjMap,
        Category.id_comp, Category.comp_id] using
        homComplexFunctor_map_f_π (R := R) f g n p q hpq) h
  obtain ⟨ρ⟩ := CategoryTheory.RingedForgetTwoInjective.ringedRepresentatives J R
  obtain ⟨η, _⟩ := kInjectiveHomComparisonDescent U B.complex F
    M.weilHom (derivedInternalHomOfUniverses J R)
    (fun K I _ ↦ M.weilRepresentatives.model K I inferInstance) ρ.iso
    (by
      intro K K' I I' _ _ f g
      exact M.weilRepresentatives.naturality K' K I I' inferInstance inferInstance f g)
    ρ.naturality chain
  obtain ⟨S, _, _, _⟩ := ringedDerived_closed_symmetric_monoidal J R
  exact closedTransport U.mapDerivedCategory.asEquivalence M.weilHom
    (derivedInternalHomOfUniverses J R) S η

end AlgebraicGeometry.ProEtaleWeilSheaf
