/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryRingedTensorCoherenceData

/-! Naturality of an evaluation-normalized ordinary tensor comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite WeilConjectures
  BraidedCategory
namespace AlgebraicGeometry.ProEtaleWeilSheaf

section

private theorem compose_naturality
    {C : Type*} [Category* C] {A B D E F G : C}
    (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) (i : E ⟶ G)
    (j : D ⟶ F) (k : F ⟶ G) (hn : h ≫ i = j ≫ k) :
    (f ≫ g ≫ h) ≫ i = (f ≫ g ≫ j) ≫ k := by
  simp only [Category.assoc]
  rw [hn]

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
  {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u + 1}}
  (E₀ : ProEtale.AdicSheaf l Y ≌ RingedTensorModules.{u + 1, u + 1, u + 1} J R)
  [E₀.functor.Additive]
  (H : Functor.uncurry.obj (ordinaryIhomBifunctor l Y) ⋙ E₀.functor ≅
    E₀.functor.op.prod E₀.functor ⋙
      Functor.uncurry.obj (SheafOfModules.homFunctor (R := R)))

set_option linter.unusedSectionVars false in
private theorem normalized_uncurry
    (U : OrdinaryRingedTensorUnderivedData l Y J R E₀ H)
    (P Q I : ProEtale.AdicSheaf l Y) (f : ((ordinaryTensorBifunctor l Y).obj P).obj Q ⟶ I) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.symmetricCategory R
    (U.underived P Q).inv ≫ E₀.functor.map f =
      (β_ (E₀.functor.obj Q) (E₀.functor.obj P)).hom ≫
        (SheafOfModules.tensorHomEquiv (R := R) (E₀.functor.obj P)
          (E₀.functor.obj Q) (E₀.functor.obj I)).symm
            (E₀.functor.map ((Mod.ihomAdjunction P).homEquiv Q I f) ≫
              H.hom.app (op P, I)) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  have h := U.uncurry P Q I ((Mod.ihomAdjunction P).homEquiv Q I f)
  simp only [Equiv.symm_apply_apply, SheafOfModules.tensorHomAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv] at h
  convert h using 1

omit [E₀.functor.Additive] in
private theorem ordinary_hom_naturality
    (P P' I : ProEtale.AdicSheaf l Y) (p : P ⟶ P') :
    E₀.functor.map (((ordinaryIhomBifunctor l Y).map p.op).app I) ≫
        H.hom.app (op P, I) =
      H.hom.app (op P', I) ≫
        SheafOfModules.homObjMap (R := R) (E₀.functor.map p) (𝟙 _) := by
  have nh := H.hom.naturality
    (show (op P', I) ⟶ (op P, I) from (p.op, 𝟙 _))
  dsimp only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map,
    Functor.op_map, Functor.prod_obj, Functor.op_obj] at nh
  erw [((ordinaryIhomBifunctor l Y).obj (op P)).map_id I,
    Category.comp_id, E₀.functor.map_id I,
    ((SheafOfModules.homFunctor R).obj (op (E₀.functor.obj P))).map_id
      (E₀.functor.obj I), Category.comp_id] at nh
  exact nh

set_option linter.unusedSectionVars false in
private theorem parameter_adjunct_map
    (P Q P' Q' : ProEtale.AdicSheaf l Y) (p : P ⟶ P') (q : Q ⟶ Q') :
    (Mod.ihomAdjunction P).homEquiv Q _
        (((ordinaryTensorBifunctor l Y).map p).app Q ≫
          ((ordinaryTensorBifunctor l Y).obj P').map q) =
        q ≫ (Mod.ihomAdjunction P').homEquiv Q' _ (𝟙 _) ≫
          ((ordinaryIhomBifunctor l Y).map p.op).app
            (((ordinaryTensorBifunctor l Y).obj P').obj Q') := by
  let adj : ordinaryTensorBifunctor l Y ⊣₂ ordinaryIhomBifunctor l Y :=
    { adj := fun M ↦ Mod.ihomAdjunction M
      unit_whiskerRight_map := by
        intro M M' f
        apply NatTrans.ext
        funext N
        exact (unit_conjugateEquiv (Mod.ihomAdjunction M')
          (Mod.ihomAdjunction M) (Mod.tensorLeftMap f) N).symm }
  have h₁ := adj.homEquiv_naturality_one p
    (((ordinaryTensorBifunctor l Y).obj P').map q)
  simp only [ParametrizedAdjunction.homEquiv_eq] at h₁
  dsimp only [adj] at h₁
  refine h₁.trans ?_
  have ht := (Mod.ihomAdjunction P').homEquiv_naturality_left q
    (𝟙 (((ordinaryTensorBifunctor l Y).obj P').obj Q'))
  simpa only [ordinaryTensorBifunctor, ordinaryIhomBifunctor,
    Category.comp_id, Category.assoc] using
    congrArg (fun z ↦ z ≫ ((ordinaryIhomBifunctor l Y).map p.op).app
      (((ordinaryTensorBifunctor l Y).obj P').obj Q')) ht

set_option linter.unusedSectionVars false in
private theorem inverse_naturality
    (U : OrdinaryRingedTensorUnderivedData l Y J R E₀ H)
    (P Q P' Q' : ProEtale.AdicSheaf l Y) (p : P ⟶ P') (q : Q ⟶ Q') :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.symmetricCategory R
    (U.underived P Q).inv ≫
        E₀.functor.map (((ordinaryTensorBifunctor l Y).map p).app Q ≫
          ((ordinaryTensorBifunctor l Y).obj P').map q) =
      (E₀.functor.map q ⊗ₘ E₀.functor.map p) ≫
        (U.underived P' Q').inv := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let E : ProEtale.AdicSheaf l Y ⥤ SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) :=
    E₀.functor
  let c (P I : ProEtale.AdicSheaf l Y) :
      E.obj (((ordinaryIhomBifunctor l Y).obj (op P)).obj I) ⟶
        SheafOfModules.homObj (R := R) (E.obj P) (E.obj I) := H.hom.app (op P, I)
  let e (P Q : ProEtale.AdicSheaf l Y) :
      E.obj (((ordinaryTensorBifunctor l Y).obj P).obj Q) ≅ E.obj Q ⊗ E.obj P := U.underived P Q
  have hu (P Q I : ProEtale.AdicSheaf l Y) (f : ((ordinaryTensorBifunctor l Y).obj P).obj Q ⟶ I) :
      (e P Q).inv ≫ E.map f =
        (β_ (E.obj Q) (E.obj P)).hom ≫
          (SheafOfModules.tensorHomEquiv (R := R) (E.obj P) (E.obj Q) (E.obj I)).symm
            (E.map ((Mod.ihomAdjunction P).homEquiv Q I f) ≫ c P I) := by
    exact normalized_uncurry E₀ H U P Q I f
  have hi (P Q : ProEtale.AdicSheaf l Y) :
      (e P Q).inv =
        (β_ (E.obj Q) (E.obj P)).hom ≫
          (SheafOfModules.tensorHomEquiv (R := R) (E.obj P) (E.obj Q)
            (E.obj (((ordinaryTensorBifunctor l Y).obj P).obj Q))).symm
            (E.map ((Mod.ihomAdjunction P).homEquiv Q _ (𝟙 _)) ≫
              c P (((ordinaryTensorBifunctor l Y).obj P).obj Q)) := by
    have h := hu P Q _ (𝟙 _)
    rw [E.map_id, Category.comp_id] at h
    exact h
  rw [hu, hi P' Q', ← Category.assoc, braiding_naturality, Category.assoc]
  apply (cancel_epi (β_ (E.obj Q) (E.obj P)).hom).2
  apply (SheafOfModules.tensorHomEquiv (R := R) (E.obj P) (E.obj Q)
    (E.obj (((ordinaryTensorBifunctor l Y).obj P').obj Q'))).injective
  rw [Equiv.apply_symm_apply, MonoidalCategory.tensorHom_def, Category.assoc,
    SheafOfModules.tensorHomEquiv_whiskerRight_comp (R := R) (E.map p),
    SheafOfModules.tensorHomEquiv_whiskerLeft_comp (R := R) (E.obj P') (E.map q),
    Equiv.apply_symm_apply]
  have ha := parameter_adjunct_map P Q P' Q' p q
  have nh := ordinary_hom_naturality E₀ H P P' (((ordinaryTensorBifunctor l Y).obj P').obj Q') p
  change E.map (((ordinaryIhomBifunctor l Y).map p.op).app
      (((ordinaryTensorBifunctor l Y).obj P').obj Q')) ≫
      c P (((ordinaryTensorBifunctor l Y).obj P').obj Q') =
    c P' (((ordinaryTensorBifunctor l Y).obj P').obj Q') ≫
      SheafOfModules.homObjMap (R := R) (E.map p) (𝟙 _) at nh
  have hm : E.map (q ≫ (Mod.ihomAdjunction P').homEquiv Q' _ (𝟙 _) ≫
        ((ordinaryIhomBifunctor l Y).map p.op).app
          (((ordinaryTensorBifunctor l Y).obj P').obj Q')) =
      E.map q ≫ E.map ((Mod.ihomAdjunction P').homEquiv Q' _ (𝟙 _)) ≫
        E.map (((ordinaryIhomBifunctor l Y).map p.op).app
          (((ordinaryTensorBifunctor l Y).obj P').obj Q')) := by
    exact (E.map_comp q _).trans
      (congrArg (E.map q ≫ ·) (E.map_comp _ _))
  calc
    _ = E.map (q ≫ (Mod.ihomAdjunction P').homEquiv Q' _ (𝟙 _) ≫
        ((ordinaryIhomBifunctor l Y).map p.op).app
          (((ordinaryTensorBifunctor l Y).obj P').obj Q')) ≫
          c P (((ordinaryTensorBifunctor l Y).obj P').obj Q') :=
      congrArg (fun z ↦ E.map z ≫ c P (((ordinaryTensorBifunctor l Y).obj P').obj Q')) ha
    _ = (E.map q ≫ E.map ((Mod.ihomAdjunction P').homEquiv Q' _ (𝟙 _)) ≫
        E.map (((ordinaryIhomBifunctor l Y).map p.op).app
          (((ordinaryTensorBifunctor l Y).obj P').obj Q'))) ≫
          c P (((ordinaryTensorBifunctor l Y).obj P').obj Q') :=
      congrArg (· ≫ c P (((ordinaryTensorBifunctor l Y).obj P').obj Q')) hm
    _ = _ := compose_naturality (E.map q) (E.map ((Mod.ihomAdjunction P').homEquiv Q' _ (𝟙 _)))
      _ _ _ _ nh

private theorem quotient_naturality
    (b : ∀ P Q : ProEtale.AdicSheaf l Y,
      ((ordinaryTensorBifunctor l Y).obj P).obj Q ≅ Q ⊗ P)
    (hb : ∀ P Q, Mod.tensorπ Q P ≫ (b P Q).hom.hom = Mod.tensorObjπ Q P)
    (P Q P' Q' : ProEtale.AdicSheaf l Y) (p : P ⟶ P') (q : Q ⟶ Q') :
    (((ordinaryTensorBifunctor l Y).map p).app Q ≫
        ((ordinaryTensorBifunctor l Y).obj P').map q) ≫ (b P' Q').hom =
      (b P Q).hom ≫ (q ⊗ₘ p) := by
  have : IsIso (b P Q).hom.hom :=
    inferInstanceAs (IsIso ((Mod.forget _).map (b P Q).hom))
  have : Epi (Mod.tensorπ Q P ≫ (b P Q).hom.hom) := by
    rw [hb P Q]
    infer_instance
  have : Epi (Mod.tensorπ Q P) :=
    (epi_comp_iff_of_isIso _ (b P Q).hom.hom).1 inferInstance
  apply Mod.hom_ext
  apply (cancel_epi (Mod.tensorπ Q P)).1
  rw [MonoidalCategory.tensorHom_def']
  simp only [Mod.comp_hom', Category.assoc, ordinaryTensorBifunctor,
    Mod.tensorπ_tensorLeftMap_assoc, Mod.tensorπ_map_assoc, hb,
    reassoc_of% (hb P Q),
    Mod.tensorObjπ_whiskerLeft_assoc, Mod.tensorObjπ_whiskerRight]

end

/-- The mate-normalized underived comparison is natural in both tensor factors.
Source: Stacks 03EO and 0FPQ.
(blueprint: new-sf-ordinary-ringed-tensor-underived-naturality).

Proof: the quotient equation and epimorphic quotient maps give naturality of `b`.
Precomposition on ordinary internal Hom is the mate of the tensor map, so the
ordinary adjunction is natural in its parameter. Rewrite the inverse of `d` using
its uncurrying equation, and do the same for the identity of the target tensor.
Naturality of `H`, of braiding and of the ringed tensor-Hom equivalence identifies
the two transposes. Injectivity of that equivalence proves naturality of `d` in
both variables. The components `E(b(Q,P))⁻¹ ≫ d(Q,P)` therefore assemble into `ν`;
cancellation of `E(b)` with its inverse proves the quotient normalization.
-/
theorem ordinary_ringed_tensor_underived_naturality
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u + 1})
    (E : ProEtale.AdicSheaf l Y ≌ RingedTensorModules.{u + 1, u + 1, u + 1} J R)
    [E.functor.Additive]
    (H : Functor.uncurry.obj (ordinaryIhomBifunctor l Y) ⋙ E.functor ≅
      E.functor.op.prod E.functor ⋙
        Functor.uncurry.obj (SheafOfModules.homFunctor (R := R)))
    (d : OrdinaryRingedTensorUnderivedData l Y J R E H)
    (b : ∀ P Q : ProEtale.AdicSheaf l Y,
      ((ordinaryTensorBifunctor l Y).obj P).obj Q ≅ Q ⊗ P)
    (hb : ∀ P Q, Mod.tensorπ Q P ≫ (b P Q).hom.hom = Mod.tensorObjπ Q P) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    ∃ (ν : MonoidalCategory.tensor (ProEtale.AdicSheaf l Y) ⋙ E.functor ≅
        E.functor.prod E.functor ⋙ MonoidalCategory.tensor _),
      (∀ P Q, E.functor.map (b P Q).hom ≫ ν.hom.app (Q, P) =
        (d.underived P Q).hom) := by
  classical
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let e (P Q : ProEtale.AdicSheaf l Y) :=
    (E.functor.mapIso (b Q P)).symm ≪≫ d.underived Q P
  refine ⟨(NatIso.ofComponents (fun PQ ↦ (e PQ.1 PQ.2).symm) ?_).symm, ?_⟩
  · rintro ⟨P, Q⟩ ⟨P', Q'⟩ ⟨p, q⟩
    change (E.functor.map p ⊗ₘ E.functor.map q) ≫
        ((d.underived Q' P').inv ≫ E.functor.map (b Q' P').hom) =
      ((d.underived Q P).inv ≫ E.functor.map (b Q P).hom) ≫
        E.functor.map (p ⊗ₘ q)
    rw [← Category.assoc, ← inverse_naturality E H d Q P Q' P' q p,
      Category.assoc, ← E.functor.map_comp, quotient_naturality b hb,
      E.functor.map_comp, Category.assoc]
  · intro P Q
    change E.functor.map (b P Q).hom ≫
      (E.functor.map (b P Q).inv ≫ (d.underived P Q).hom) = _
    rw [← Category.assoc, ← E.functor.map_comp, Iso.hom_inv_id,
      E.functor.map_id, Category.id_comp]

end AlgebraicGeometry.ProEtaleWeilSheaf
