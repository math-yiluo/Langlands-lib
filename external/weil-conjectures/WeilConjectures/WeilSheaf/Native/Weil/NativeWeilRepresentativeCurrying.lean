/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.NativeWeilTensorPresentation.NativeWeilTensorPresentation
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryRepresentativeCurrying

/-! # Derived currying from native tensor representatives

Source: Stacks 08J9 and 0A97; native ringed tensor model, adjunction step.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf
namespace PresentedCurrying
universe a b

private instance totalExists {C : Type a} [Category.{b} C] [Abelian C]
    [HasCountableCoproducts C] (T : C ⥤ C ⥤ C)
    [T.Additive] [∀ P, (T.obj P).Additive] (P Q : CochainComplex C ℤ) :
    P.HasMapBifunctor Q T := NativeCurrying.totalExists T P Q

private def kflat {C : Type a} [Category.{b} C] [Abelian C]
    [HasCountableCoproducts C] (T : C ⥤ C ⥤ C)
    [T.Additive] [∀ P, (T.obj P).Additive] (P : CochainComplex C ℤ) : Prop :=
  ∀ L : CochainComplex C ℤ, L.Acyclic → (CochainComplex.mapBifunctor P L T).Acyclic

private structure Presentation {C : Type a} [Category.{b} C] [Abelian C]
    [HasCountableCoproducts C] [HasDerivedCategory.{b} C]
    [Abelian.HasKInjectiveResolutions C]
    (H₀ : Cᵒᵖ ⥤ C ⥤ C) where
  tensor : C ⥤ C ⥤ C
  [tensor_additive : tensor.Additive]
  [tensor_obj_additive : ∀ P, (tensor.obj P).Additive]
  adjunction : tensor ⊣₂ H₀
  localization :
    (ObjectProperty.ι (kflat tensor) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso C (.up ℤ)).inverseImage
        (ObjectProperty.ι (kflat tensor)))

attribute [instance] Presentation.tensor_additive Presentation.tensor_obj_additive

variable {C : Type a} [Category.{b} C] [Abelian C]
  [HasCountableProducts C] [HasCountableCoproducts C] [HasDerivedCategory.{b} C]
  [Abelian.HasKInjectiveResolutions C] [MonoidalCategory (DerivedCategory C)]
  {H₀ : Cᵒᵖ ⥤ C ⥤ C} [H₀.Additive] [∀ P, (H₀.obj P).Additive]

private abbrev flat (N : Presentation H₀) : ObjectProperty (CochainComplex C ℤ) := kflat N.tensor
private abbrev flatProperty (N : Presentation H₀) : ObjectProperty (CochainComplex C ℤ) :=
  flat N
private noncomputable abbrev total (N : Presentation H₀)
    (P Q : CochainComplex C ℤ) : CochainComplex C ℤ :=
  CochainComplex.mapBifunctor P Q N.tensor

private instance flatLocalization (N : Presentation H₀) :
    (ObjectProperty.ι (flatProperty N) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso C (.up ℤ)).inverseImage
        (ObjectProperty.ι (flatProperty N))) := N.localization

private noncomputable def representativeFunctor (N : Presentation H₀) :=
  (DerivedCategory.Q (C := C)).op.prod
    (((ObjectProperty.ι (flatProperty N)) ⋙
      DerivedCategory.Q).op.prod
        (CochainComplex.KInjectives.ι (C := C) ⋙ DerivedCategory.Q))

private def representativeW (N : Presentation H₀) :=
  let W := HomologicalComplex.quasiIso C (.up ℤ)
  W.op.prod ((W.inverseImage
    (ObjectProperty.ι (flatProperty N))).op.prod
      (CochainComplex.KInjectives.quasiIso C))

private instance representativeLocalization (N : Presentation H₀) :
    (representativeFunctor N).IsLocalization (representativeW N) := by
  let W := HomologicalComplex.quasiIso C (.up ℤ)
  have : (DerivedCategory.Q (C := C)).IsLocalization W := inferInstance
  have : (ObjectProperty.ι (flatProperty N) ⋙
      DerivedCategory.Q).IsLocalization
        (W.inverseImage (ObjectProperty.ι (flatProperty N))) :=
    flatLocalization N
  have : (CochainComplex.KInjectives.ι (C := C) ⋙
      DerivedCategory.Q).IsLocalization
        (CochainComplex.KInjectives.quasiIso C) :=
    inferInstance
  -- The restricted property is a definition, so register its identity instance explicitly.
  have : (CochainComplex.KInjectives.quasiIso C).ContainsIdentities := by
    dsimp only [CochainComplex.KInjectives.quasiIso]
    infer_instance
  dsimp only [representativeFunctor, representativeW]
  infer_instance

private noncomputable def representativeEquiv (N : Presentation H₀)
    (H : (DerivedCategory C)ᵒᵖ × DerivedCategory C ⥤ DerivedCategory C)
    (R : NativeHomRepresentatives H₀ H)
    (model : ∀ P Q : CochainComplex C ℤ, flat N P →
      (DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj P ≅
        DerivedCategory.Q.obj (total N P Q)))
    (P Q I : CochainComplex C ℤ) (hP : flat N P) [I.IsKInjective] :
    (DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj I) ≃
      (DerivedCategory.Q.obj Q ⟶ H.obj (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I)) :=
  (model P Q hP).homFromEquiv.trans
    (NativeCurrying.derivedEquiv (T := N.tensor) (H := H₀) N.adjunction H R P Q I hP)

private theorem representativeEquiv_uncurry (N : Presentation H₀)
    (H : (DerivedCategory C)ᵒᵖ × DerivedCategory C ⥤ DerivedCategory C)
    (R : NativeHomRepresentatives H₀ H)
    (model : ∀ P Q : CochainComplex C ℤ, flat N P →
      (DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj P ≅
        DerivedCategory.Q.obj (total N P Q)))
    (P Q I : CochainComplex C ℤ) (hP : flat N P) [I.IsKInjective]
    (φ : Q ⟶ CochainComplex.bifunctorHomObj H₀ P I) :
    (representativeEquiv N H R model P Q I hP).symm
        (DerivedCategory.Q.map φ ≫ (R.model P I inferInstance).inv) =
      (model P Q hP).hom ≫ DerivedCategory.Q.map
        ((NativeCurrying.internalHomEquiv (T := N.tensor) (H := H₀)
          N.adjunction P I Q).symm φ) := by
  change (model P Q hP).hom ≫
    (NativeCurrying.derivedEquiv (T := N.tensor) (H := H₀) N.adjunction H R P Q I hP).symm _ = _
  rw [NativeCurrying.derivedEquiv_symm_map]

private theorem representativeEquiv_naturality (N : Presentation H₀)
    (H : (DerivedCategory C)ᵒᵖ × DerivedCategory C ⥤ DerivedCategory C)
    (R : NativeHomRepresentatives H₀ H)
    (model : ∀ P Q : CochainComplex C ℤ, flat N P →
      (DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj P ≅
        DerivedCategory.Q.obj (total N P Q)))
    (hn : ∀ (P Q P' Q' : CochainComplex C ℤ)
      (hP : flat N P) (hP' : flat N P') (f : P ⟶ P') (g : Q ⟶ Q'),
      (DerivedCategory.Q.map g ⊗ₘ DerivedCategory.Q.map f) ≫ (model P' Q' hP').hom =
        (model P Q hP).hom ≫ DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f g N.tensor (.up ℤ)))
    (P P' Q Q' I I' : CochainComplex C ℤ)
    (hP : flat N P) (hP' : flat N P') [I.IsKInjective] [I'.IsKInjective]
    (f : Q' ⟶ Q) (g : P' ⟶ P) (h : I ⟶ I')
    (φ : DerivedCategory.Q.obj Q ⟶
      H.obj (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I)) :
    (representativeEquiv N H R model P' Q' I' hP').symm
        (DerivedCategory.Q.map f ≫ φ ≫ H.map
          (Prod.mkHom (DerivedCategory.Q.map g).op (DerivedCategory.Q.map h))) =
      (DerivedCategory.Q.map f ⊗ₘ DerivedCategory.Q.map g) ≫
        (representativeEquiv N H R model P Q I hP).symm φ ≫ DerivedCategory.Q.map h := by
  have hd := NativeCurrying.derivedEquiv_naturality (T := N.tensor) (H := H₀)
    N.adjunction H R P P' Q Q' I I' hP hP' g f h
      ((NativeCurrying.derivedEquiv (T := N.tensor) (H := H₀)
        N.adjunction H R P Q I hP).symm φ)
  rw [Equiv.apply_symm_apply] at hd
  have he := congrArg (NativeCurrying.derivedEquiv (T := N.tensor) (H := H₀)
    N.adjunction H R P' Q' I' hP').symm hd
  rw [Equiv.symm_apply_apply] at he
  change (model P' Q' hP').hom ≫
      (NativeCurrying.derivedEquiv (T := N.tensor) (H := H₀) N.adjunction H R P' Q' I' hP').symm _ =
    (DerivedCategory.Q.map f ⊗ₘ DerivedCategory.Q.map g) ≫
      ((model P Q hP).hom ≫
        (NativeCurrying.derivedEquiv (T := N.tensor) (H := H₀)
          N.adjunction H R P Q I hP).symm φ) ≫ DerivedCategory.Q.map h
  rw [← he, ← Category.assoc, ← hn P' Q' P Q hP' hP g f]
  simp only [Category.assoc]

attribute [local irreducible] representativeEquiv

private noncomputable def representativeIso (N : Presentation H₀)
    (H : (DerivedCategory C)ᵒᵖ × DerivedCategory C ⥤ DerivedCategory C)
    (R : NativeHomRepresentatives H₀ H)
    (model : ∀ P Q : CochainComplex C ℤ, flat N P →
      (DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj P ≅
        DerivedCategory.Q.obj (total N P Q)))
    (hn : ∀ (P Q P' Q' : CochainComplex C ℤ)
      (hP : flat N P) (hP' : flat N P') (f : P ⟶ P') (g : Q ⟶ Q'),
      (DerivedCategory.Q.map g ⊗ₘ DerivedCategory.Q.map f) ≫ (model P' Q' hP').hom =
        (model P Q hP).hom ≫ DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f g N.tensor (.up ℤ))) :
    representativeFunctor N ⋙ CurryingDescent.homHoms H ≅
      representativeFunctor N ⋙ CurryingDescent.tensorHoms :=
  NatIso.ofComponents
    (fun X ↦ by
      let := X.2.2.property
      exact (representativeEquiv N H R model X.2.1.unop.obj X.1.unop X.2.2.obj
        X.2.1.unop.property).symm.toIso)
    (fun {X Y} f ↦ by
      let := X.2.2.property
      let := Y.2.2.property
      ext φ
      exact representativeEquiv_naturality N H R model hn
        X.2.1.unop.obj Y.2.1.unop.obj X.1.unop Y.1.unop X.2.2.obj Y.2.2.obj
        X.2.1.unop.property Y.2.1.unop.property f.1.unop f.2.1.unop.hom f.2.2.hom φ)

private noncomputable def localizedIso (N : Presentation H₀)
    (H : (DerivedCategory C)ᵒᵖ × DerivedCategory C ⥤ DerivedCategory C)
    (R : NativeHomRepresentatives H₀ H)
    (model : ∀ P Q : CochainComplex C ℤ, flat N P →
      (DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj P ≅
        DerivedCategory.Q.obj (total N P Q)))
    (hn : ∀ (P Q P' Q' : CochainComplex C ℤ)
      (hP : flat N P) (hP' : flat N P') (f : P ⟶ P') (g : Q ⟶ Q'),
      (DerivedCategory.Q.map g ⊗ₘ DerivedCategory.Q.map f) ≫ (model P' Q' hP').hom =
        (model P Q hP).hom ≫ DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f g N.tensor (.up ℤ))) :
    CurryingDescent.homHoms H ≅ CurryingDescent.tensorHoms :=
  (Localization.fullyFaithfulWhiskeringLeft (representativeFunctor N)
    (representativeW N) (Type b)).preimageIso (representativeIso N H R model hn)

private theorem localizedIso_restrict (N : Presentation H₀)
    (H : (DerivedCategory C)ᵒᵖ × DerivedCategory C ⥤ DerivedCategory C)
    (R : NativeHomRepresentatives H₀ H)
    (model : ∀ P Q : CochainComplex C ℤ, flat N P →
      (DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj P ≅
        DerivedCategory.Q.obj (total N P Q)))
    (hn : ∀ (P Q P' Q' : CochainComplex C ℤ)
      (hP : flat N P) (hP' : flat N P') (f : P ⟶ P') (g : Q ⟶ Q'),
      (DerivedCategory.Q.map g ⊗ₘ DerivedCategory.Q.map f) ≫ (model P' Q' hP').hom =
        (model P Q hP).hom ≫ DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f g N.tensor (.up ℤ))) :
    Functor.isoWhiskerLeft (representativeFunctor N) (localizedIso N H R model hn) =
      representativeIso N H R model hn := by
  apply Iso.ext
  exact (Localization.fullyFaithfulWhiskeringLeft (representativeFunctor N)
    (representativeW N) (Type b)).map_preimage _

attribute [local irreducible] localizedIso

private theorem result (N : Presentation H₀)
    (H : (DerivedCategory C)ᵒᵖ × DerivedCategory C ⥤ DerivedCategory C)
    (R : NativeHomRepresentatives H₀ H)
    (model : ∀ P Q : CochainComplex C ℤ, flat N P →
      (DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj P ≅
        DerivedCategory.Q.obj (total N P Q)))
    (hn : ∀ (P Q P' Q' : CochainComplex C ℤ)
      (hP : flat N P) (hP' : flat N P') (f : P ⟶ P') (g : Q ⟶ Q'),
      (DerivedCategory.Q.map g ⊗ₘ DerivedCategory.Q.map f) ≫ (model P' Q' hP').hom =
        (model P Q hP).hom ≫ DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f g N.tensor (.up ℤ))) :
    ∃ e : ∀ T P I : DerivedCategory C,
      (T ⊗ P ⟶ I) ≃ (T ⟶ H.obj (op P, I)),
      (∀ (T T' P P' I I' : DerivedCategory C)
        (f : T' ⟶ T) (g : P' ⟶ P) (h : I ⟶ I') (φ : T ⟶ H.obj (op P, I)),
        (e T' P' I').symm (f ≫ φ ≫ H.map (Prod.mkHom g.op h)) =
          (f ⊗ₘ g) ≫ (e T P I).symm φ ≫ h) ∧
      (∀ (P Q I : CochainComplex C ℤ)
        (hP : flat N P) (_hQ : flat N Q)
        (hI : I.IsKInjective)
        (φ : Q ⟶ CochainComplex.bifunctorHomObj (H₀) P I),
        ∃ ψ : total N P Q ⟶ I,
          (∀ (p q n : ℤ) (hpq : p + q = n),
            HomologicalComplex.ιMapBifunctor P Q (N.tensor)
                (.up ℤ) p q n hpq ≫ ψ.f n =
              ((N.tensor).obj (P.X p)).map (φ.f q ≫
                  CochainComplex.bifunctorHomπ (H₀) P I q p n hpq) ≫
                (N.adjunction.adj (P.X p)).counit.app (I.X n)) ∧
          (model P Q hP).hom ≫ DerivedCategory.Q.map ψ =
            (e (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P)
              (DerivedCategory.Q.obj I)).symm
                (DerivedCategory.Q.map φ ≫ (R.model P I hI).inv)) := by
  classical
  let e := CurryingDescent.derivedEquiv H (PresentedCurrying.localizedIso N H R model hn)
  refine ⟨e, ?_, ?_⟩
  · exact CurryingDescent.derivedEquiv_symm_naturality H
      (PresentedCurrying.localizedIso N H R model hn)
  · intro P Q I hP _hQ hI φ
    let := hI
    let ψ := (NativeCurrying.internalHomEquiv (T := N.tensor) (H := H₀) N.adjunction P I Q).symm φ
    refine ⟨ψ, ?_, ?_⟩
    · intro p q n hpq
      exact NativeCurrying.uncurry_component (T := N.tensor) (H := H₀)
        N.adjunction P Q I φ p q n hpq
    · have hr := congrArg
        (fun i ↦ i.hom.app
          (op Q, (op (⟨P, hP⟩ : ObjectProperty.FullSubcategory
            (PresentedCurrying.flat N : ObjectProperty
              (CochainComplex C ℤ))),
            (⟨I, hI⟩ : CochainComplex.KInjectives C))))
        (PresentedCurrying.localizedIso_restrict N H R model hn)
      have he : (e (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P)
            (DerivedCategory.Q.obj I)).symm
              (DerivedCategory.Q.map φ ≫ (R.model P I hI).inv) =
          (PresentedCurrying.representativeEquiv N H R model P Q I hP).symm
            (DerivedCategory.Q.map φ ≫ (R.model P I hI).inv) :=
        congrArg (fun k ↦ k (DerivedCategory.Q.map φ ≫ (R.model P I hI).inv)) hr
      rw [he, PresentedCurrying.representativeEquiv_uncurry]

end PresentedCurrying

/-- The presented native total tensor has natural derived currying, with its
componentwise uncurrying formula on K-flat sources and K-injective targets.

Source: Stacks 08J9 and 0A97; native ringed tensor model, step 2.
(blueprint: lem-sf-native-weil-representative-currying).

Proof: apply the existing generic NativeCurrying chain and homotopy equivalences
to the presentation's underived parameterized adjunction. Its acyclic-test
K-flats make Hom(P,I) K-injective. Combine the derived Hom bijection into a
K-injective target with the presentation's tensor model and the supplied Hom
representatives. The two representative naturality squares make this bijection
natural in all three complex variables. Precomposition with the product of
the ordinary localization, the presented K-flat localization and K-injective
localization is fully faithful. Extend the natural isomorphism of Hom functors
through it. Its preimage equation fixes the representative uncurrying formula;
the generic chain calculation supplies its unsigned degree-zero components.
No forgetting comparison or monoidal coherence is needed for this proof. -/
theorem native_weil_representative_currying
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    {M : NativeClosedHomModels k₀ l X} {S : CoefficientClosedStructure M.ordinaryHom}
    {m : MonoidalCategory (DerivedCategory (ProEtaleWeilSheaf k₀ l X))}
    {t : @MonoidalCategory.tensor _ _ m ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ S.tensor}
    (N : NativeWeilTensorPresentation k₀ l X M S m t) :
    ∃ e : ∀ A K L : DerivedCategory (ProEtaleWeilSheaf k₀ l X),
      (m.tensorObj A K ⟶ L) ≃ (A ⟶ M.weilHom.obj (op K, L)),
      (∀ (A A' K K' L L' : DerivedCategory (ProEtaleWeilSheaf k₀ l X))
        (f : A' ⟶ A) (g : K' ⟶ K) (h : L ⟶ L')
        (φ : A ⟶ M.weilHom.obj (op K, L)),
        (e A' K' L').symm (f ≫ φ ≫ M.weilHom.map (g.op, h)) =
          (@MonoidalCategory.tensor _ _ m).map (Prod.mkHom f g) ≫ (e A K L).symm φ ≫ h) ∧
      (∀ (P Q I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
        (hP : NativeTensorKFlat k₀ l X N.tensor P)
        (_hQ : NativeTensorKFlat k₀ l X N.tensor Q) (hI : I.IsKInjective)
        (φ : Q ⟶ CochainComplex.bifunctorHomObj (ihomBifunctor k₀ l X) P I),
        ∃ ψ : CochainComplex.mapBifunctor P Q N.tensor ⟶ I,
          (∀ (p q n : ℤ) (hpq : p + q = n),
            HomologicalComplex.ιMapBifunctor P Q N.tensor (.up ℤ) p q n hpq ≫ ψ.f n =
              (N.tensor.obj (P.X p)).map (φ.f q ≫
                CochainComplex.bifunctorHomπ (ihomBifunctor k₀ l X) P I q p n hpq) ≫
                  (N.adjunction.adj (P.X p)).counit.app (I.X n)) ∧
          (N.model P Q hP).hom ≫ DerivedCategory.Q.map ψ =
            (e (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P)
              (DerivedCategory.Q.obj I)).symm
                (DerivedCategory.Q.map φ ≫ (M.weilRepresentatives.model P I hI).inv)) := by
  let := m
  let : Abelian.HasKInjectiveResolutions (ProEtaleWeilSheaf k₀ l X) :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{u + 1}
  let N' : PresentedCurrying.Presentation (ihomBifunctor k₀ l X) :=
    { tensor := N.tensor
      adjunction := N.adjunction
      localization := N.localization }
  exact PresentedCurrying.result N' M.weilHom M.weilRepresentatives N.model
    N.model_naturality

end AlgebraicGeometry.ProEtaleWeilSheaf
