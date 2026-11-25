/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
public import WeilConjectures.WeilSheaf.DerivedHomSingleResolution
public import WeilConjectures.WeilSheaf.SmoothPurityWhiskering
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact

/-!
# The native closed internal Hom from a sheaf

The representative formulas identify the native closed internal Hom from a
sheaf with its right derived internal Hom, naturally in the target complex.
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

omit [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] in
private lemma singleProjection_right (A : ProEtaleWeilSheaf k₀ l X)
    {I I' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ} (g : I ⟶ I') :
    CochainComplex.bifunctorHomMapRight (H := ihomBifunctor k₀ l X)
        (K := (CochainComplex.singleFunctor _ 0).obj A) g ≫
        singleResolutionProjection A I' =
      singleResolutionProjection A I ≫
        ((ihomFunctor k₀ l X A).mapHomologicalComplex (.up ℤ)).map g := by
  apply HomologicalComplex.Hom.ext
  funext n
  dsimp only [HomologicalComplex.comp_f, singleResolutionProjection]
  rw [Category.assoc, CochainComplex.bifunctorHomMapRight_f_π_assoc]
  simp only [Functor.mapHomologicalComplex_map_f]
  exact congrArg (CochainComplex.bifunctorHomπ (ihomBifunctor k₀ l X)
    ((CochainComplex.singleFunctor _ 0).obj A) I n 0 n (zero_add n) ≫ ·)
    (((ihomBifunctor k₀ l X).map
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv.op).naturality (g.f n))

/-- The closed-model internal Hom from the localization of a single complex is
the right derived internal Hom of its sheaf, naturally in the target. -/
noncomputable def nativeHomSingleComplexIso (A : ProEtaleWeilSheaf k₀ l X) :
    Prod.sectR (op (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj A))) _ ⋙
        (nativeDerivedClosedComparison k₀ l X).homModels.weilHom ≅
      (ihomFunctor k₀ l X A).rightDerivedFunctor := by
  let C := ProEtaleWeilSheaf k₀ l X
  let H := (nativeDerivedClosedComparison k₀ l X).homModels.weilHom
  let M := (nativeDerivedClosedComparison k₀ l X).homModels.weilRepresentatives
  let P := (CochainComplex.singleFunctor C 0).obj A
  let F := ihomFunctor k₀ l X A
  let q := (CochainComplex.KInjectives.ι (C := C)) ⋙ DerivedCategory.Q
  let e : CochainComplex.KInjectives.toHomotopyCategory ⋙
      HomotopyCategory.KInjectives.Qh ≅ q :=
    Functor.isoWhiskerLeft CochainComplex.KInjectives.ι (DerivedCategory.quotientCompQhIso C)
  have : q.Full := Functor.Full.of_iso e
  have : q.EssSurj := Functor.essSurj_of_iso e
  let B : CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
    { obj I := CochainComplex.bifunctorHomObj (ihomBifunctor k₀ l X) P I
      map g := CochainComplex.bifunctorHomMapRight g
      map_id _ := CochainComplex.bifunctorHomMapRight_id
      map_comp _ _ := CochainComplex.bifunctorHomMapRight_comp _ _ }
  let a : q ⋙ Prod.sectR (op (DerivedCategory.Q.obj P)) _ ⋙ H ≅
      CochainComplex.KInjectives.ι ⋙ B ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun I ↦ M.model P I.obj I.property) (fun {I I'} g ↦ by
      change H.map (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P)))
          (DerivedCategory.Q.map g.hom)) ≫ (M.model P I'.obj I'.property).hom =
        (M.model P I.obj I.property).hom ≫ DerivedCategory.Q.map
          (CochainComplex.bifunctorHomMapRight (H := ihomBifunctor k₀ l X) (K := P) g.hom)
      simpa only [CategoryTheory.Functor.map_id, op_id, CochainComplex.bifunctorHomMapLeft_id,
        Category.id_comp] using M.naturality P P I.obj I'.obj I.property I'.property
          (𝟙 P) g.hom)
  let b : CochainComplex.KInjectives.ι ⋙ B ⋙ DerivedCategory.Q ≅
      CochainComplex.KInjectives.ι ⋙ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun I ↦ by
      have := I.property
      have := singleResolutionProjection_isIso A I.obj
      exact DerivedCategory.Q.mapIso (asIso (singleResolutionProjection A I.obj)))
      (fun {I I'} g ↦ by
        have := I.property
        have := I'.property
        have := singleResolutionProjection_isIso A I.obj
        have := singleResolutionProjection_isIso A I'.obj
        change DerivedCategory.Q.map
            (CochainComplex.bifunctorHomMapRight (H := ihomBifunctor k₀ l X) (K := P) g.hom) ≫
              DerivedCategory.Q.map (singleResolutionProjection A I'.obj) =
          DerivedCategory.Q.map (singleResolutionProjection A I.obj) ≫
            DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map g.hom)
        rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
          singleProjection_right])
  let c : CochainComplex.KInjectives.ι ⋙ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅
      q ⋙ F.rightDerivedFunctor :=
    NatIso.ofComponents (fun I ↦ by
      have := I.property
      exact (F.rightDerivedFunctorObjQIso I.obj).symm) (fun {I I'} g ↦ by
        have := I.property
        have := I'.property
        exact Functor.rightDerivedFunctor_map_Q_map_comp_objQIso_inv F g.hom)
  exact (Functor.fullyFaithfulWhiskeringLeftOfFullEssSurj q (DerivedCategory C)).preimageIso
    (a ≪≫ b ≪≫ c)

/-- The same comparison in the standard derived single-functor coordinates. -/
noncomputable def nativeHomSingleIso (A : ProEtaleWeilSheaf k₀ l X) :
    Prod.sectR (op ((DerivedCategory.singleFunctor _ 0).obj A)) _ ⋙
        (nativeDerivedClosedComparison k₀ l X).homModels.weilHom ≅
      (ihomFunctor k₀ l X A).rightDerivedFunctor :=
  Functor.isoWhiskerRight
    (NatIso.ofComponents (fun _ ↦
      (((DerivedCategory.singleFunctorIsoCompQ _ 0).app A).symm.op).prod (Iso.refl _))
      (fun _ ↦ by simp)) _ ≪≫ nativeHomSingleComplexIso A

end AlgebraicGeometry.ProEtaleWeilSheaf
