/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityNativeHomSingle
public import WeilConjectures.WeilSheaf.BifunctorHomShift

/-!
# Shifting the source of native closed internal Hom

The signed Hom-complex comparison is natural in its target. The specified
native representative models descend this comparison to the derived category.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

noncomputable def traceHomTarget
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ ⥤
      CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ where
  obj I := CochainComplex.bifunctorHomObj (ihomBifunctor k₀ l X) P I
  map g := CochainComplex.bifunctorHomMapRight g
  map_id _ := CochainComplex.bifunctorHomMapRight_id
  map_comp _ _ := CochainComplex.bifunctorHomMapRight_comp _ _

noncomputable def traceHomTargetShift
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) (a b : ℤ) (h : a + b = 0) :
    traceHomTarget P ⋙ shiftFunctor _ b ≅ traceHomTarget (P⟦a⟧) :=
  NatIso.ofComponents
    (fun I ↦ CochainComplex.bifunctorHomShiftIso (ihomBifunctor k₀ l X) P I a b h)
    (fun g ↦ by
      ext n : 1
      apply CochainComplex.bifunctorHomObj_hom_ext
      intro p q hpq
      simp [traceHomTarget])

noncomputable abbrev traceKInjectiveQ :
    CochainComplex.KInjectives (ProEtaleWeilSheaf k₀ l X) ⥤
      DerivedCategory (ProEtaleWeilSheaf k₀ l X) :=
  CochainComplex.KInjectives.ι ⋙ DerivedCategory.Q

noncomputable def traceHomModelIso
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    traceKInjectiveQ ⋙ Prod.sectR (op (DerivedCategory.Q.obj P)) _ ⋙
        (nativeDerivedClosedComparison k₀ l X).homModels.weilHom ≅
      CochainComplex.KInjectives.ι ⋙ traceHomTarget P ⋙ DerivedCategory.Q :=
  NatIso.ofComponents
    (fun I ↦ (nativeDerivedClosedComparison k₀ l X).homModels.weilRepresentatives.model
      P I.obj I.property)
    (fun {I I'} g ↦ by
      change (nativeDerivedClosedComparison k₀ l X).homModels.weilHom.map
          (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P))) (DerivedCategory.Q.map g.hom)) ≫
            ((nativeDerivedClosedComparison k₀ l X).homModels.weilRepresentatives.model
              P I'.obj I'.property).hom =
        ((nativeDerivedClosedComparison k₀ l X).homModels.weilRepresentatives.model
          P I.obj I.property).hom ≫ DerivedCategory.Q.map
            (CochainComplex.bifunctorHomMapRight (H := ihomBifunctor k₀ l X) (K := P) g.hom)
      simpa only [CategoryTheory.Functor.map_id, op_id, CochainComplex.bifunctorHomMapLeft_id,
        Category.id_comp] using
        (nativeDerivedClosedComparison k₀ l X).homModels.weilRepresentatives.naturality
          P P I.obj I'.obj I.property I'.property (𝟙 P) g.hom)

noncomputable def traceHomShiftQIso
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) (a b : ℤ) (h : a + b = 0) :
    (Prod.sectR (op (DerivedCategory.Q.obj P)) _ ⋙
        (nativeDerivedClosedComparison k₀ l X).homModels.weilHom) ⋙ shiftFunctor _ b ≅
      Prod.sectR (op (DerivedCategory.Q.obj (P⟦a⟧))) _ ⋙
        (nativeDerivedClosedComparison k₀ l X).homModels.weilHom := by
  let C := ProEtaleWeilSheaf k₀ l X
  let e : CochainComplex.KInjectives.toHomotopyCategory ⋙
      HomotopyCategory.KInjectives.Qh (C := C) ≅
        traceKInjectiveQ (k₀ := k₀) (l := l) (X := X) :=
    Functor.isoWhiskerLeft CochainComplex.KInjectives.ι
      (DerivedCategory.quotientCompQhIso C)
  have : (traceKInjectiveQ (k₀ := k₀) (l := l) (X := X)).Full :=
    Functor.Full.of_iso e
  have : (traceKInjectiveQ (k₀ := k₀) (l := l) (X := X)).EssSurj :=
    Functor.essSurj_of_iso e
  apply (Functor.fullyFaithfulWhiskeringLeftOfFullEssSurj
    (traceKInjectiveQ (k₀ := k₀) (l := l) (X := X)) (DerivedCategory C)).preimageIso
  exact Functor.isoWhiskerRight (traceHomModelIso P) (shiftFunctor _ b) ≪≫
    Functor.isoWhiskerLeft (CochainComplex.KInjectives.ι ⋙ traceHomTarget P)
      (DerivedCategory.Q.commShiftIso b).symm ≪≫
    Functor.isoWhiskerLeft CochainComplex.KInjectives.ι
      (Functor.isoWhiskerRight (traceHomTargetShift P a b h) DerivedCategory.Q) ≪≫
    (traceHomModelIso (P⟦a⟧)).symm

/-- Changing the source of closed internal Hom along an isomorphism. -/
noncomputable def nativeHomSourceIso
    {P P' : DerivedCategory (ProEtaleWeilSheaf k₀ l X)} (e : P ≅ P') :
    Prod.sectR (op P) _ ⋙ (nativeDerivedClosedComparison k₀ l X).homModels.weilHom ≅
      Prod.sectR (op P') _ ⋙ (nativeDerivedClosedComparison k₀ l X).homModels.weilHom :=
  Functor.isoWhiskerRight
    (NatIso.ofComponents (fun _ ↦ e.symm.op.prod (Iso.refl _)) (fun _ ↦ by simp)) _

/-- Shifting the source of native internal Hom shifts its value by the opposite
degree, naturally in the target. -/
noncomputable def nativeHomSourceShiftIso
    (P : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) (a b : ℤ) (h : a + b = 0) :
    Prod.sectR (op (P⟦a⟧)) _ ⋙ (nativeDerivedClosedComparison k₀ l X).homModels.weilHom ≅
      (Prod.sectR (op P) _ ⋙ (nativeDerivedClosedComparison k₀ l X).homModels.weilHom) ⋙
        shiftFunctor _ b :=
  let Q := DerivedCategory.Q.objPreimage P
  let e : P ≅ DerivedCategory.Q.obj Q := (DerivedCategory.Q.objObjPreimageIso P).symm
  nativeHomSourceIso ((shiftFunctor _ a).mapIso e ≪≫
    ((DerivedCategory.Q.commShiftIso a).app Q).symm) ≪≫
    (traceHomShiftQIso Q a b h).symm ≪≫
    Functor.isoWhiskerRight (nativeHomSourceIso e).symm (shiftFunctor _ b)

end AlgebraicGeometry.ProEtaleWeilSheaf
