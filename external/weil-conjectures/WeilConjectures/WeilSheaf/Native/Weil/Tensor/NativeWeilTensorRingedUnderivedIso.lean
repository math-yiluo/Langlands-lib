/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedUnderivedData
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures MonoidalCategory
  BraidedCategory
namespace AlgebraicGeometry.ProEtaleWeilSheaf

private theorem compose_naturality
    {C : Type*} [Category* C] {A B D E F G : C}
    (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) (i : E ⟶ G)
    (j : D ⟶ F) (k : F ⟶ G) (hn : h ≫ i = j ≫ k) :
    (f ≫ g ≫ h) ≫ i = (f ≫ g ≫ j) ≫ k := by
  simp only [Category.assoc]
  rw [hn]

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (b : NativeWeilTensorRingedBridge k₀ l X)
  (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X)
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
  (adj : T ⊣₂ ihomBifunctor k₀ l X)

set_option linter.unusedSectionVars false in
private theorem normalized_uncurry
    (U : NativeWeilRingedTensorUnderivedData b T adj)
    (P Q I : ProEtaleWeilSheaf k₀ l X) (f : (T.obj P).obj Q ⟶ I) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients b.R
    letI := SheafOfModules.monoidalCategory b.R
    letI := SheafOfModules.symmetricCategory b.R
    (U.underived P Q).inv ≫ b.native.functor.map f =
      (β_ (b.native.functor.obj Q) (b.native.functor.obj P)).hom ≫
        (SheafOfModules.tensorHomEquiv (R := b.R) (b.native.functor.obj P)
          (b.native.functor.obj Q) (b.native.functor.obj I)).symm
            (b.native.functor.map ((adj.adj P).homEquiv Q I f) ≫
              b.nativeHom.hom.app (op P, I)) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients b.R
  let := SheafOfModules.monoidalCategory b.R
  let := SheafOfModules.symmetricCategory b.R
  have h := U.uncurry P Q I ((adj.adj P).homEquiv Q I f)
  simp only [Equiv.symm_apply_apply, SheafOfModules.tensorHomAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv, nativeRingedTensorObjData] at h
  convert h using 1

private theorem native_hom_naturality
    (P P' I : ProEtaleWeilSheaf k₀ l X) (p : P ⟶ P') :
    b.native.functor.map (((ihomBifunctor k₀ l X).map p.op).app I) ≫
        b.nativeHom.hom.app (op P, I) =
      b.nativeHom.hom.app (op P', I) ≫
        SheafOfModules.homObjMap (R := b.R) (b.native.functor.map p) (𝟙 _) := by
  have nh := b.nativeHom.hom.naturality
    (show (op P', I) ⟶ (op P, I) from (p.op, 𝟙 _))
  dsimp only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map,
    Functor.op_map, Functor.prod_obj, Functor.op_obj] at nh
  erw [((ihomBifunctor k₀ l X).obj (op P)).map_id I,
    Category.comp_id, b.native.functor.map_id I,
    ((SheafOfModules.homFunctor b.R).obj (op (b.native.functor.obj P))).map_id
      (b.native.functor.obj I), Category.comp_id] at nh
  exact nh

set_option linter.unusedSectionVars false in
private theorem parameter_adjunct_map
    (P Q P' Q' : ProEtaleWeilSheaf k₀ l X) (p : P ⟶ P') (q : Q ⟶ Q') :
    (adj.adj P).homEquiv Q _ ((T.map p).app Q ≫ (T.obj P').map q) =
        q ≫ (adj.adj P').homEquiv Q' _ (𝟙 _) ≫
          ((ihomBifunctor k₀ l X).map p.op).app ((T.obj P').obj Q') := by
  have h₁ := adj.homEquiv_naturality_one p ((T.obj P').map q)
  simp only [ParametrizedAdjunction.homEquiv_eq] at h₁
  rw [h₁]
  have ht := (adj.adj P').homEquiv_naturality_left q (𝟙 ((T.obj P').obj Q'))
  simpa only [Category.comp_id, Category.assoc] using
    congrArg (fun z ↦ z ≫
      ((ihomBifunctor k₀ l X).map p.op).app ((T.obj P').obj Q')) ht

set_option linter.unusedSectionVars false in
-- The monoidal unfolding of the ringed tensor mate needs extra time.
private theorem inverse_naturality
    (U : NativeWeilRingedTensorUnderivedData b T adj)
    (P Q P' Q' : ProEtaleWeilSheaf k₀ l X) (p : P ⟶ P') (q : Q ⟶ Q') :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients b.R
    letI := SheafOfModules.monoidalCategory b.R
    letI := SheafOfModules.symmetricCategory b.R
    (U.underived P Q).inv ≫
        b.native.functor.map ((T.map p).app Q ≫ (T.obj P').map q) =
      (b.native.functor.map q ⊗ₘ b.native.functor.map p) ≫
        (U.underived P' Q').inv := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients b.R
  let := SheafOfModules.monoidalCategory b.R
  let := SheafOfModules.symmetricCategory b.R
  let E : ProEtaleWeilSheaf k₀ l X ⥤ SheafOfModules.{u + 1}
      ((sheafCompose b.J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj b.R) :=
    b.native.functor
  let c (P I : ProEtaleWeilSheaf k₀ l X) :
      E.obj (((ihomBifunctor k₀ l X).obj (op P)).obj I) ⟶
        SheafOfModules.homObj (R := b.R) (E.obj P) (E.obj I) := b.nativeHom.hom.app (op P, I)
  let e (P Q : ProEtaleWeilSheaf k₀ l X) :
      E.obj ((T.obj P).obj Q) ≅ E.obj Q ⊗ E.obj P := U.underived P Q
  have hu (P Q I : ProEtaleWeilSheaf k₀ l X) (f : (T.obj P).obj Q ⟶ I) :
      (e P Q).inv ≫ E.map f =
        (β_ (E.obj Q) (E.obj P)).hom ≫
          (SheafOfModules.tensorHomEquiv (R := b.R) (E.obj P) (E.obj Q) (E.obj I)).symm
            (E.map ((adj.adj P).homEquiv Q I f) ≫ c P I) := by
    exact normalized_uncurry b T adj U P Q I f
  have hi (P Q : ProEtaleWeilSheaf k₀ l X) :
      (e P Q).inv =
        (β_ (E.obj Q) (E.obj P)).hom ≫
          (SheafOfModules.tensorHomEquiv (R := b.R) (E.obj P) (E.obj Q)
            (E.obj ((T.obj P).obj Q))).symm
            (E.map ((adj.adj P).homEquiv Q _ (𝟙 _)) ≫
              c P ((T.obj P).obj Q)) := by
    have h := hu P Q _ (𝟙 _)
    rw [E.map_id, Category.comp_id] at h
    exact h
  rw [hu, hi P' Q', ← Category.assoc, braiding_naturality, Category.assoc]
  apply (cancel_epi (β_ (E.obj Q) (E.obj P)).hom).2
  apply (SheafOfModules.tensorHomEquiv (R := b.R) (E.obj P) (E.obj Q)
    (E.obj ((T.obj P').obj Q'))).injective
  rw [Equiv.apply_symm_apply, MonoidalCategory.tensorHom_def, Category.assoc,
    SheafOfModules.tensorHomEquiv_whiskerRight_comp (R := b.R) (E.map p),
    SheafOfModules.tensorHomEquiv_whiskerLeft_comp (R := b.R) (E.obj P') (E.map q),
    Equiv.apply_symm_apply]
  have ha := parameter_adjunct_map T adj P Q P' Q' p q
  have nh := native_hom_naturality b P P' ((T.obj P').obj Q') p
  change E.map (((ihomBifunctor k₀ l X).map p.op).app ((T.obj P').obj Q')) ≫
      c P ((T.obj P').obj Q') =
    c P' ((T.obj P').obj Q') ≫
      SheafOfModules.homObjMap (R := b.R) (E.map p) (𝟙 _) at nh
  have hm : E.map (q ≫ (adj.adj P').homEquiv Q' _ (𝟙 _) ≫
        ((ihomBifunctor k₀ l X).map p.op).app ((T.obj P').obj Q')) =
      E.map q ≫ E.map ((adj.adj P').homEquiv Q' _ (𝟙 _)) ≫
        E.map (((ihomBifunctor k₀ l X).map p.op).app ((T.obj P').obj Q')) := by
    exact (E.map_comp q _).trans
      (congrArg (E.map q ≫ ·) (E.map_comp _ _))
  calc
    _ = E.map (q ≫ (adj.adj P').homEquiv Q' _ (𝟙 _) ≫
        ((ihomBifunctor k₀ l X).map p.op).app ((T.obj P').obj Q')) ≫
          c P ((T.obj P').obj Q') :=
      congrArg (fun z ↦ E.map z ≫ c P ((T.obj P').obj Q')) ha
    _ = (E.map q ≫ E.map ((adj.adj P').homEquiv Q' _ (𝟙 _)) ≫
        E.map (((ihomBifunctor k₀ l X).map p.op).app ((T.obj P').obj Q'))) ≫
          c P ((T.obj P').obj Q') := congrArg (· ≫ c P ((T.obj P').obj Q')) hm
    _ = _ := compose_naturality (E.map q) (E.map ((adj.adj P').homEquiv Q' _ (𝟙 _)))
      _ _ _ _ nh

set_option linter.unusedSectionVars false in
/-- The pointwise underived comparisons assemble into a bifunctor isomorphism.
Source: Stacks 06YS and 06YU (blueprint: lem-sf-native-weil-tensor-ringed-chain-data).

Proof: use the normalized uncurrying equation to identify both composites with the
same tensor--Hom mate.  Naturality in each variable follows from uniqueness of
mates under the two adjunctions; this is the underived naturality step needed by
the total-complex comparison. -/
theorem native_weil_tensor_ringed_underived_iso
    (U : NativeWeilRingedTensorUnderivedData b T adj) :
    ∃ e : (Functor.uncurry.obj T ⋙ b.native.functor) ≅
      (b.native.functor.prod b.native.functor) ⋙
        Functor.uncurry.obj
          (MonoidalCategory.curriedTensor
            (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)).flip,
      ∀ P Q : ProEtaleWeilSheaf k₀ l X,
        e.hom.app (P, Q) = (U.underived P Q).hom := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients b.R
  let := SheafOfModules.monoidalCategory b.R
  let := SheafOfModules.symmetricCategory b.R
  let E : ProEtaleWeilSheaf k₀ l X ⥤ SheafOfModules.{u + 1}
      ((sheafCompose b.J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj b.R) :=
    b.native.functor
  let e (P Q : ProEtaleWeilSheaf k₀ l X) :
      E.obj ((T.obj P).obj Q) ≅ E.obj Q ⊗ E.obj P := U.underived P Q
  refine ⟨(NatIso.ofComponents (fun PQ ↦ (e PQ.1 PQ.2).symm) ?_).symm, ?_⟩
  · rintro ⟨P, Q⟩ ⟨P', Q'⟩ ⟨p, q⟩
    dsimp only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map,
      Functor.flip_obj_map, Functor.flip_map_app,
      MonoidalCategory.curriedTensor_obj_map, MonoidalCategory.curriedTensor_map_app]
    change (E.obj Q ◁ E.map p ≫ E.map q ▷ E.obj P') ≫
        (e P' Q').inv =
      (e P Q).inv ≫ E.map ((T.map p).app Q ≫ (T.obj P').map q)
    rw [← MonoidalCategory.tensorHom_def' (E.map q) (E.map p)]
    exact (inverse_naturality b T adj U P Q P' Q' p q).symm
  · intro P Q
    rfl

end AlgebraicGeometry.ProEtaleWeilSheaf
