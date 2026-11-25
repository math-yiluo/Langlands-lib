/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.CompactProjectionFormula
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
public import WeilConjectures.Mathlib.CategoryTheory.Yoneda
public import WeilConjectures.Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# The Verdier exchange for Weil complexes

Let `f : X ⟶ Y` be a separated morphism of finite type of separated `k₀`-schemes of finite type
over a base `S`, with structure morphisms `a_X = f ≫ a_Y`, and let `G_X`, `G_Y` be right adjoints
of the direct images with compact support `Ra_{X,0}!`, `Ra_{Y,0}!` of Weil complexes. For a Weil
complex `Q` on `S` put `ω_X = G_X Q` and `ω_Y = G_Y Q`. Then, naturally in the Weil complex `M`
on `X`,

`RHom(Rf₀! M, ω_Y) ≅ Rf_* RHom(M, ω_X)`

(blueprint: `lemma-internal-adjunction-two-exchange-formulas--2`). The proof is the Yoneda argument
of `lemma-internal-adjunction-two-exchange-formulas--1`: for a test Weil complex `T` on `Y`,

`Hom(T, RHom(Rf₀! M, ω_Y)) = Hom(Rf₀! M ⊗ T, ω_Y) = Hom(Rf₀!(M ⊗ f^* T), ω_Y)`
`= Hom(Ra_{X,0}!(M ⊗ f^* T), Q) = Hom(M ⊗ f^* T, ω_X) = Hom(f^* T, RHom(M, ω_X))`
`= Hom(T, Rf_* RHom(M, ω_X))`,

all natural in `M` and `T`, using the tensor–hom adjunction of the native derived tensor product
(`AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison`), the compact-support
projection formula (`AlgebraicGeometry.WeilComplex.nonempty_nativeCompactProjectionLeft_iso`),
the composition law `Ra_{X,0}! ≅ Ra_{Y,0}! ∘ Rf₀!` and the adjunction `f^* ⊣ Rf_*`. In particular
no exceptional inverse image `Rf^!` along `f` is needed.

## Main statements

- `AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedTensorCurryYonedaIso` and
  `AlgebraicGeometry.WeilComplex.nativeConstructibleTensorCurryYonedaIso`: the tensor–hom
  adjunction, natural in both variables.
- `AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_op_comp_iso_of_adjunction`: the
  exchange, natural in `M`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite MonoidalCategory

namespace WeilConjectures.CoefficientClosedStructure

variable {D : Type*} [Category D] {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H)

/-- The tensor–hom transpose `Hom(T ⊗ P, Q) ≃ Hom(T, H(P, Q))` is natural in `P`. -/
lemma adjunction_homEquiv_whiskerLeft_comp {P P' : D} (f : P' ⟶ P) (T Q : D)
    (φ : (@tensorRight D _ S.monoidal P).obj T ⟶ Q) :
    (S.adjunction P').homEquiv T Q
        (@MonoidalCategoryStruct.whiskerLeft D _ S.monoidal.toMonoidalCategoryStruct T _ _ f ≫ φ) =
      (S.adjunction P).homEquiv T Q φ ≫ H.map (X := (op P, Q)) (Y := (op P', Q)) (f.op, 𝟙 Q) := by
  let := S.monoidal
  erw [Adjunction.homEquiv_apply_eq, Adjunction.homEquiv_counit]
  have h := S.evaluation_naturality P P' Q f
  erw [Functor.map_comp, Category.assoc, h]
  change _ = ((S.adjunction P).homEquiv T Q φ) ▷ P' ≫ H.obj (op P, Q) ◁ f ≫ _
  refine Eq.trans ?_ (whisker_exchange_assoc (X := H.obj (op P, Q))
    ((S.adjunction P).homEquiv T Q φ) f ((S.adjunction P).counit.app Q))
  congr 1
  have := (S.adjunction P).homEquiv_counit (g := (S.adjunction P).homEquiv T Q φ)
  simp only [Equiv.symm_apply_apply] at this
  exact this

variable (B : @BraidedCategory D _ S.monoidal)

/-- For a braided closed structure, `Hom(P ⊗ T, Q) ≃ Hom(T, H(P, Q))`. -/
def braidedHomEquiv (P T Q : D) :
    letI := S.monoidal
    letI := B
    (P ⊗ T ⟶ Q) ≃ (T ⟶ H.obj (op P, Q)) :=
  letI := S.monoidal
  letI := B
  { toFun φ := (S.adjunction P).homEquiv T Q ((β_ P T).inv ≫ φ)
    invFun ψ := (β_ P T).hom ≫ ((S.adjunction P).homEquiv T Q).symm ψ
    left_inv φ := by simp
    right_inv ψ := by
      dsimp only
      erw [Iso.inv_hom_id_assoc]
      exact Equiv.apply_symm_apply _ _ }

lemma braidedHomEquiv_whiskerLeft_comp {P T T' Q : D} (g : T' ⟶ T) :
    letI := S.monoidal
    letI := B
    ∀ φ : P ⊗ T ⟶ Q, S.braidedHomEquiv B P T' Q (P ◁ g ≫ φ) =
      g ≫ S.braidedHomEquiv B P T Q φ := by
  let := S.monoidal
  let := B
  intro φ
  change (S.adjunction P).homEquiv T' Q ((β_ P T').inv ≫ P ◁ g ≫ φ) =
    g ≫ (S.adjunction P).homEquiv T Q ((β_ P T).inv ≫ φ)
  rw [← BraidedCategory.braiding_inv_naturality_left_assoc]
  exact (S.adjunction P).homEquiv_naturality_left g _

lemma braidedHomEquiv_whiskerRight_comp {P P' T Q : D} (f : P' ⟶ P) :
    letI := S.monoidal
    letI := B
    ∀ φ : P ⊗ T ⟶ Q, S.braidedHomEquiv B P' T Q (f ▷ T ≫ φ) =
      S.braidedHomEquiv B P T Q φ ≫ H.map (X := (op P, Q)) (Y := (op P', Q)) (f.op, 𝟙 Q) := by
  let := S.monoidal
  let := B
  intro φ
  change (S.adjunction P').homEquiv T Q ((β_ P' T).inv ≫ f ▷ T ≫ φ) =
    (S.adjunction P).homEquiv T Q ((β_ P T).inv ≫ φ) ≫ _
  rw [← BraidedCategory.braiding_inv_naturality_right_assoc]
  exact S.adjunction_homEquiv_whiskerLeft_comp f T Q _

/-- For a braided closed structure, `Hom(P ⊗ T, Q) ≅ Hom(T, H(P, Q))`, naturally in `P` and
`T`. -/
def curryYonedaIso (Q : D) :
    Functor.curry.obj ((prodOpEquiv D).inverse ⋙ S.tensor.op ⋙ yoneda.obj Q) ≅
      (Prod.sectL Dᵒᵖ Q ⋙ H) ⋙ yoneda :=
  NatIso.ofComponents
    (fun P ↦ NatIso.ofComponents
      (fun T ↦ (S.braidedHomEquiv B P.unop T.unop Q).toIso) (fun {_ _} g ↦ by
        ext φ
        let := S.monoidal
        let := B
        have := S.braidedHomEquiv_whiskerLeft_comp B g.unop φ
        rw [← id_tensorHom] at this
        exact this))
    (fun {_ _} f ↦ by
      ext T φ
      let := S.monoidal
      let := B
      have := S.braidedHomEquiv_whiskerRight_comp B f.unop φ
      rw [← tensorHom_id] at this
      exact this)

end WeilConjectures.CoefficientClosedStructure

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace ProEtaleWeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **The tensor–hom adjunction for the derived internal hom, natural in both variables**
(blueprint: `prose-03-02`): `Hom(P ⊗ T, Q) ≅ Hom(T, RHom(P, Q))`,
naturally in `P` and `T`, the tensor product being the native derived tensor product. -/
noncomputable def nativeDerivedTensorCurryYonedaIso
    (Q : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
    Functor.curry.obj ((prodOpEquiv _).inverse ⋙ (nativeDerivedTensor k₀ l X).op ⋙
      yoneda.obj Q) ≅ derivedHom k₀ l X Q ⋙ yoneda :=
  (nativeDerivedClosedComparison k₀ l X).weilClosed.curryYonedaIso
      (nativeDerivedClosedComparison k₀ l X).weilSymmetry.toBraidedCategory Q ≪≫
    Functor.isoWhiskerRight ((nativeDerivedClosedComparison k₀ l X).homModels.nativeModel Q) yoneda

end ProEtaleWeilSheaf

namespace WeilComplex

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]

/-- **The tensor–hom adjunction on Weil complexes, natural in both variables**: if
`RHom(M, Q)` is a Weil complex for every Weil complex `M`, then
`Hom(M ⊗ T, Q) ≅ Hom(T, RHom(M, Q))`, naturally in the Weil complexes `M` and `T`. -/
noncomputable def nativeConstructibleTensorCurryYonedaIso (Q : WeilComplex k₀ l X)
    (h : ∀ K : WeilComplex k₀ l X, objectProperty k₀ l X
      ((ProEtaleWeilSheaf.derivedHom k₀ l X Q.obj).obj (op K.obj))) :
    Functor.curry.obj ((prodOpEquiv _).inverse ⋙ (nativeConstructibleTensor k₀ l X).op ⋙
      yoneda.obj Q) ≅
      (objectProperty k₀ l X).lift ((objectProperty k₀ l X).ι.op ⋙
        ProEtaleWeilSheaf.derivedHom k₀ l X Q.obj) (fun K ↦ h K.unop) ⋙ yoneda :=
  Functor.curry.mapIso (Functor.isoWhiskerLeft
      ((prodOpEquiv _).inverse ⋙ (nativeConstructibleTensor k₀ l X).op)
      ((objectProperty k₀ l X).fullyFaithfulι.opCompYonedaObjIso Q).symm) ≪≫
    Functor.curryObjProdComp (objectProperty k₀ l X).ι.op (objectProperty k₀ l X).ι.op
      ((prodOpEquiv _).inverse ⋙ (ProEtaleWeilSheaf.nativeDerivedTensor k₀ l X).op ⋙
        yoneda.obj Q.obj) ≪≫
    Functor.isoWhiskerLeft (objectProperty k₀ l X).ι.op
      (Functor.isoWhiskerRight (ProEtaleWeilSheaf.nativeDerivedTensorCurryYonedaIso Q.obj)
        ((Functor.whiskeringLeft _ _ _).obj (objectProperty k₀ l X).ι.op)) ≪≫
    Functor.isoWhiskerLeft ((objectProperty k₀ l X).lift ((objectProperty k₀ l X).ι.op ⋙
        ProEtaleWeilSheaf.derivedHom k₀ l X Q.obj) (fun K ↦ h K.unop))
      (objectProperty k₀ l X).fullyFaithfulι.compYonedaCompWhiskeringLeftIso

variable (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- **Verdier exchange, natural form** (blueprint:
`lemma-internal-adjunction-two-exchange-formulas--2`, with
`lemma-internal-adjunction-two-exchange-formulas--1`): let `a_X = f ≫ a_Y` be morphisms to a base
`S`, `G_X`, `G_Y` right adjoints of `Ra_{X,0}!` and `Ra_{Y,0}!`, and `Q` a Weil complex on `S`. If
`RHom(-, G_X Q)` and `RHom(-, G_Y Q)` send Weil complexes to Weil complexes, then
`RHom(Rf₀! M, G_Y Q) ≅ Rf_* RHom(M, G_X Q)`, naturally in the Weil complex `M`. -/
theorem nonempty_derivedLowerShriek_op_comp_iso_of_adjunction {S : Scheme.{u}}
    [S.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (S ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (S ↘ Spec (CommRingCat.of k₀))]
    (aX : X ⟶ S) (aY : Y ⟶ S) [aX.IsOver (Spec (CommRingCat.of k₀))]
    [aY.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated aX] [LocallyOfFiniteType aX]
    [QuasiCompact aX] [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (h : f ≫ aY = aX) {GX : WeilComplex k₀ l S ⥤ WeilComplex k₀ l X}
    {GY : WeilComplex k₀ l S ⥤ WeilComplex k₀ l Y}
    (adjX : derivedLowerShriek k₀ l aX ⊣ GX) (adjY : derivedLowerShriek k₀ l aY ⊣ GY)
    (Q : WeilComplex k₀ l S)
    (hX : ∀ K : WeilComplex k₀ l X, objectProperty k₀ l X
      ((ProEtaleWeilSheaf.derivedHom k₀ l X (GX.obj Q).obj).obj (op K.obj)))
    (hY : ∀ K : WeilComplex k₀ l Y, objectProperty k₀ l Y
      ((ProEtaleWeilSheaf.derivedHom k₀ l Y (GY.obj Q).obj).obj (op K.obj))) :
    Nonempty ((derivedLowerShriek k₀ l f).op ⋙
        (objectProperty k₀ l Y).lift ((objectProperty k₀ l Y).ι.op ⋙
          ProEtaleWeilSheaf.derivedHom k₀ l Y (GY.obj Q).obj) (fun K ↦ hY K.unop) ≅
      (objectProperty k₀ l X).lift ((objectProperty k₀ l X).ι.op ⋙
          ProEtaleWeilSheaf.derivedHom k₀ l X (GX.obj Q).obj) (fun K ↦ hX K.unop) ⋙
        derivedLowerStar f) := by
  subst h
  obtain ⟨π⟩ := nonempty_nativeCompactProjectionLeft_iso (k₀ := k₀) (l := l) f
  obtain ⟨c⟩ := nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) f aY
  let DX := (objectProperty k₀ l X).lift ((objectProperty k₀ l X).ι.op ⋙
    ProEtaleWeilSheaf.derivedHom k₀ l X (GX.obj Q).obj) (fun K ↦ hX K.unop)
  let DY := (objectProperty k₀ l Y).lift ((objectProperty k₀ l Y).ι.op ⋙
    ProEtaleWeilSheaf.derivedHom k₀ l Y (GY.obj Q).obj) (fun K ↦ hY K.unop)
  -- `P ↦ Hom(Rf₀! P, G_Y Q)` is `P ↦ Hom(P, G_X Q)`.
  let q : (derivedLowerShriek k₀ l f).op ⋙ yoneda.obj (GY.obj Q) ≅ yoneda.obj (GX.obj Q) :=
    Functor.isoWhiskerLeft (derivedLowerShriek k₀ l f).op (adjY.compYonedaIso.app Q) ≪≫
      Functor.isoWhiskerRight (NatIso.op c) (yoneda.obj Q) ≪≫ (adjX.compYonedaIso.app Q).symm
  -- `Hom(T, D_Y Rf₀! M) = Hom(Rf₀! M ⊗ T, ω_Y) = Hom(Rf₀!(M ⊗ f^* T), ω_Y)`
  -- `= Hom(M ⊗ f^* T, ω_X) = Hom(f^* T, D_X M) = Hom(T, Rf_* D_X M)`.
  let e : ((derivedLowerShriek k₀ l f).op ⋙ DY) ⋙ yoneda ≅ (DX ⋙ derivedLowerStar f) ⋙ yoneda :=
    Functor.isoWhiskerLeft (derivedLowerShriek k₀ l f).op
        (nativeConstructibleTensorCurryYonedaIso (GY.obj Q) hY).symm ≪≫
      (Functor.curryObjProdComp (derivedLowerShriek k₀ l f).op (𝟭 (WeilComplex k₀ l Y)).op
        ((prodOpEquiv _).inverse ⋙ (nativeConstructibleTensor k₀ l Y).op ⋙
          yoneda.obj (GY.obj Q))).symm ≪≫
      Functor.curry.mapIso (Functor.isoWhiskerLeft (prodOpEquiv _).inverse
        (Functor.isoWhiskerRight (NatIso.op π) (yoneda.obj (GY.obj Q)))).symm ≪≫
      Functor.curry.mapIso (Functor.isoWhiskerLeft ((prodOpEquiv _).inverse ⋙
        ((𝟭 (WeilComplex k₀ l X)).prod (upperStar f) ⋙ nativeConstructibleTensor k₀ l X).op) q) ≪≫
      Functor.curryObjProdComp (𝟭 (WeilComplex k₀ l X)).op (upperStar f).op
        ((prodOpEquiv _).inverse ⋙ (nativeConstructibleTensor k₀ l X).op ⋙
          yoneda.obj (GX.obj Q)) ≪≫
      Functor.isoWhiskerLeft (𝟭 (WeilComplex k₀ l X)).op
        (Functor.isoWhiskerRight (nativeConstructibleTensorCurryYonedaIso (GX.obj Q) hX)
          ((Functor.whiskeringLeft _ _ _).obj (upperStar f).op)) ≪≫
      Functor.isoWhiskerLeft DX (upperStarDerivedLowerStarAdjunction f).compYonedaIso.symm
  exact ⟨(Yoneda.fullyFaithful.whiskeringRight _).preimageIso e⟩

end WeilComplex

end AlgebraicGeometry
