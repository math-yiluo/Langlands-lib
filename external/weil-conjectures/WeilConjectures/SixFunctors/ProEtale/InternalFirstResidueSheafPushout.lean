/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealization
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import all WeilConjectures.AlgebraicGeometry.IntegralModelsFlatResidue
import WeilConjectures.CategoryTheory.SectionwisePushout
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # The sheaf-level first-residue pushout -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint

private theorem ring_pushout_of_kernel
    {R B S : CommRingCat.{u}} (f : R ⟶ B) (q : R ⟶ S) (p : B ⟶ S)
    (h : f ≫ p = q) (hq : Function.Surjective q)
    (hk : RingHom.ker p.hom = Ideal.map f.hom (RingHom.ker q.hom)) :
    IsPushout f q p (𝟙 S) := by
  have hw : f ≫ p = q ≫ 𝟙 S := by simpa using h
  apply IsPushout.of_isColimit (c := PushoutCocone.mk p (𝟙 S) hw)
  apply PushoutCocone.IsColimit.mk hw (fun c ↦ c.inr)
  · intro c
    have hkill : RingHom.ker p.hom ≤ RingHom.ker c.inl.hom := by
      rw [hk, Ideal.map_le_iff_le_comap]
      intro a ha
      change c.inl (f a) = 0
      have hc := ConcreteCategory.congr_hom c.condition a
      change c.inl (f a) = c.inr (q a) at hc
      rw [show q a = 0 from ha, map_zero] at hc
      exact hc
    ext b
    obtain ⟨a, ha⟩ := hq (p b)
    have hf := ConcreteCategory.congr_hom h a
    change p (f a) = q a at hf
    have hb : b - f a ∈ RingHom.ker p.hom := by
      change p (b - f a) = 0
      rw [map_sub, hf, ha, sub_self]
    have hz : c.inl b = c.inl (f a) := by
      have hz := hkill hb
      change c.inl (b - f a) = 0 at hz
      simpa only [map_sub, sub_eq_zero] using hz
    have hc := ConcreteCategory.congr_hom c.condition a
    change c.inl (f a) = c.inr (q a) at hc
    change c.inr (p b) = c.inl b
    exact ((hz.trans hc).trans (congrArg c.inr ha)).symm
  · intro c
    simp only [Category.id_comp]
  · intro c m hm₁ hm₂
    simpa only [Category.id_comp] using hm₂

private theorem completion_pushout
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    IsPushout (ConstantCompletion.coefficientMap J A I)
      (ConstantCompletion.quotient J A I 0)
      (ConstantCompletion.projection J A I 0) (𝟙 _) := by
  have h : ConstantCompletion.coefficientMap J A I ≫
      ConstantCompletion.projection J A I 0 = ConstantCompletion.quotient J A I 0 :=
    limit.lift_π (ConstantCompletion.quotientCone J A I) (op 0)
  apply sheaf_isPushout_of_sectionwise J _ _ _ _
    (h.trans (Category.comp_id _).symm)
  intro U
  apply ring_pushout_of_kernel
  · exact congrArg (fun f ↦ f.hom.app U) h
  · exact ((ConstantCompletion.flat_and_quotients J A I).2.2 0 U.unop).1
  · rw [((ConstantCompletion.flat_and_quotients J A I).2.2 0 U.unop).2,
      Ideal.map_span, ← Set.range_comp']
    exact ((ConstantCompletion.flat_and_quotients J A I).2.1 0 U.unop).2

private theorem smallMap_comp (X : Scheme.{u})
    {R S T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [MonObj T]
    [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj T]
    (f : R ⟶ S) [IsMonHom f] (g : S ⟶ T) [IsMonHom g] :
    IntegralModelsStacks.smallMap X (f ≫ g) =
      IntegralModelsStacks.smallMap X f ≫ IntegralModelsStacks.smallMap X g := by
  unfold IntegralModelsStacks.smallMap
  rw [← Functor.map_comp]
  congr 1

private theorem smallMap_congr (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (f g : R ⟶ S) [IsMonHom f] [IsMonHom g] (h : f = g) :
    IntegralModelsStacks.smallMap X f = IntegralModelsStacks.smallMap X g := by
  subst g
  rfl

private theorem smallMap_id (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] :
    IntegralModelsStacks.smallMap X (𝟙 R) = 𝟙 _ := by
  unfold IntegralModelsStacks.smallMap
  have h : IntegralModelsStacks.sectionMap X (𝟙 R) = 𝟙 _ := by rfl
  rw [h]
  exact CategoryTheory.Functor.map_id _ _

private theorem scalar_pushout (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    ∃ p : IntegralModelsStacks.smallRing X
        (condensedRingObj (IntegralModelsStacks.integersObj l E) X) ⟶
        IntegralModelsStacks.smallRing X (condensedRingObj
          (IntegralModelsStacks.discreteObj (Padic.coefficientExtensionRing l E 1)) X),
      IsPushout (IntegralModelsStacks.smallMap X (IntegralModelsStacks.scalarMap l E X))
        (IntegralModelsStacks.smallMap X (IntegralModelsStacks.residueMap l E X)) p (𝟙 _) := by
  classical
  let A := IntegralConstantCompletion.integers l E
  let I := IntegralConstantCompletion.ideal l E
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
  let F := Scheme.CompletedConstantAlgebra.pushRing X
  let i := IntegralModelsStacks.discreteRingIso (Padic.coefficientExtensionIntegers l E) X
  let j := IntegralModelsStacks.discreteRingIso (Padic.coefficientExtensionRing l E 1) X
  let c := IntegralModelsStacks.sectionMap X (IntegralModelsStacks.scalarMap l E X)
  let q := IntegralModelsStacks.sectionMap X (IntegralModelsStacks.residueMap l E X)
  obtain ⟨e, he⟩ := IntegralModelsStacks.completedScalar_projection l E X
  let α := F.mapIso i.symm ≪≫ (Scheme.CompletedConstantAlgebra.constantsIso X).app
    (CommRingCat.of A)
  let β := F.mapIso e ≪≫ Scheme.CompletedConstantAlgebra.completionIso X I
  let γ := F.mapIso j.symm ≪≫ (Scheme.CompletedConstantAlgebra.constantsIso X).app
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1))) ≪≫
      (constantSheaf J CommRingCat.{u + 1}).mapIso
        (IntegralModelsStacks.residueLiftIso l E).symm
  have hscalar : F.map c ≫ β.hom = α.hom ≫
      ConstantCompletion.coefficientMap J A I := by
    apply (cancel_epi (F.map i.hom)).mp
    have h := Scheme.CompletedConstantAlgebra.coefficientMap_eq X I
      (i.hom ≫ c ≫ e.hom) he
    dsimp only [α, β, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    have hi : F.map i.hom ≫ F.map i.inv = 𝟙 _ := by
      rw [← F.map_comp, i.hom_inv_id, F.map_id]
    simp only [Category.assoc]
    rw [← Category.assoc (F.map i.hom) (F.map i.inv), hi, Category.id_comp]
    change F.map (i.hom ≫ c ≫ e.hom) ≫
      (Scheme.CompletedConstantAlgebra.completionIso X I).hom =
        ((Scheme.CompletedConstantAlgebra.constantsIso X).app (CommRingCat.of A)).hom ≫
          ConstantCompletion.coefficientMap J A I at h
    simpa only [F.map_comp, Category.assoc, Iso.app_hom] using h
  have hresidue : F.map q ≫ γ.hom = α.hom ≫
      ConstantCompletion.quotient J A I 0 := by
    apply (cancel_epi (F.map i.hom)).mp
    have hn := IntegralModelsStacks.discreteRingIso_naturality
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)) X
    have hq : i.hom ≫ q ≫ j.inv =
        (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
            ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)).comp
              ULift.ringEquiv.toRingHom))) := by
      change i.hom ≫ q = _ at hn
      erw [← Category.assoc, hn, Category.assoc, j.hom_inv_id, Category.comp_id]
    let g : CommRingCat.of A ⟶ CommRingCat.of
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1)) :=
      CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)).comp
          ULift.ringEquiv.toRingHom))
    have hm := (Scheme.CompletedConstantAlgebra.constantsIso X).hom.naturality g
    have hm' : F.map (i.hom ≫ q ≫ j.inv) ≫
        (Scheme.CompletedConstantAlgebra.constantsIso X).hom.app
          (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1))) =
      (Scheme.CompletedConstantAlgebra.constantsIso X).hom.app (CommRingCat.of A) ≫
        (constantSheaf J CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1)))) ≫
            (constantSheaf J CommRingCat.{u + 1}).map
              (IntegralModelsStacks.residueLiftIso l E).hom := by
      rw [hq]
      rw [← Functor.map_comp, IntegralModelsStacks.residueLiftIso_mk]
      exact hm
    dsimp only [α, γ, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    have h := congrArg (fun t ↦ t ≫
      (constantSheaf J CommRingCat.{u + 1}).map (IntegralModelsStacks.residueLiftIso l E).inv) hm'
    have hi : F.map i.hom ≫ F.map i.inv = 𝟙 _ := by
      rw [← F.map_comp, i.hom_inv_id, F.map_id]
    simp only [Category.assoc]
    rw [← Category.assoc (F.map i.hom) (F.map i.inv), hi, Category.id_comp]
    have heq : (constantSheaf J CommRingCat.{u + 1}).map
        (IntegralModelsStacks.residueLiftIso l E).hom ≫
        (constantSheaf J CommRingCat.{u + 1}).map
          (IntegralModelsStacks.residueLiftIso l E).inv = 𝟙 _ := by
      rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id]
    simp only [Category.assoc] at h
    rw [heq, Category.comp_id] at h
    change _ = _ ≫ ConstantCompletion.quotient J A I 0 at h
    simpa only [F.map_comp, Category.assoc, Iso.app_hom] using h
  let : IsNoetherianRing A := IntegralConstantCompletion.integers_noetherian l E
  let p := β.hom ≫ ConstantCompletion.projection J A I 0 ≫ γ.inv
  refine ⟨p, ?_⟩
  apply (completion_pushout J A I).of_iso' α β γ γ
  · exact hscalar.symm
  · exact hresidue.symm
  · simp only [p, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · exact (Category.id_comp γ.hom).symm

/-- The normalized first-residue square is a pushout of commutative ring sheaves.

Source: blueprint integral-models proof (1)--(2), Stacks Tags 093M and 099L.
(auxiliary; not a blueprint node).

Proof: identify the scalar and residue maps with the canonical maps of the
constant ring into its completion and first quotient. The kernel of the
completion projection is generated by the scalar images of the quotient kernel.
A compatible ring homomorphism therefore descends uniquely through that projection.
Transport this ring pushout through the normalized coefficient comparisons.
The commuting-square hypothesis fixes the normalization of the specified residue
isomorphism; an arbitrary residue automorphism does not give a commuting square.
-/
theorem internal_first_residue_sheaf_pushout
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (e : Mon.mk (DerivedNakayama.quotientRing l E 1) ≅
      Mon.mk (IntegralModelsStacks.discreteObj
        (Padic.coefficientExtensionRing l E 1)))
    (he : (IntegralModelsStacks.scalarMap l E X ≫
        coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X) ≫
        (AdicCompletion.quotient l E X 0 ≫ coefficientMap e.hom.hom X) =
      IntegralModelsStacks.residueMap l E X) :
    let a := IntegralModelsStacks.scalarMap l E X ≫
      coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X
    IsPushout (IntegralModelsStacks.smallMap X a)
      (IntegralModelsStacks.smallMap X (IntegralModelsStacks.residueMap l E X))
      (IntegralModelsStacks.smallMap X
        (AdicCompletion.quotient l E X 0 ≫ coefficientMap e.hom.hom X)) (𝟙 _) := by
  dsimp only
  obtain ⟨p₀, hp₀⟩ := scalar_pushout l E X
  let t := IntegralModelsStacks.smallMap X
    (coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X)
  let p := IntegralModelsStacks.smallMap X
    (AdicCompletion.quotient l E X 0 ≫ coefficientMap e.hom.hom X)
  have ht : IsIso t := by
    let ti := IntegralModelsStacks.smallMap X
      (coefficientMap (IntegralConstantModel.pointComparison l E).hom.hom X)
    refine ⟨⟨ti, ?_, ?_⟩⟩
    · rw [← smallMap_comp]
      have h : coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X ≫
          coefficientMap (IntegralConstantModel.pointComparison l E).hom.hom X = 𝟙 _ := by
        change (upperStarFromPoint X).map _ ≫ (upperStarFromPoint X).map _ = _
        rw [← Functor.map_comp]
        change (upperStarFromPoint X).map
          (((IntegralConstantModel.pointComparison l E).inv ≫
            (IntegralConstantModel.pointComparison l E).hom).hom) = _
        rw [Iso.inv_hom_id]
        exact CategoryTheory.Functor.map_id _ _
      exact (smallMap_congr X _ _ h).trans (smallMap_id X _)
    · rw [← smallMap_comp]
      have h : coefficientMap (IntegralConstantModel.pointComparison l E).hom.hom X ≫
          coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X = 𝟙 _ := by
        change (upperStarFromPoint X).map _ ≫ (upperStarFromPoint X).map _ = _
        rw [← Functor.map_comp]
        change (upperStarFromPoint X).map
          (((IntegralConstantModel.pointComparison l E).hom ≫
            (IntegralConstantModel.pointComparison l E).inv).hom) = _
        rw [Iso.hom_inv_id]
        exact CategoryTheory.Functor.map_id _ _
      exact (smallMap_congr X _ _ h).trans (smallMap_id X _)
  have hw : IntegralModelsStacks.smallMap X (IntegralModelsStacks.scalarMap l E X) ≫
      (t ≫ p) = IntegralModelsStacks.smallMap X (IntegralModelsStacks.residueMap l E X) := by
    rw [← smallMap_comp, ← smallMap_comp]
    apply smallMap_congr
    simpa only [Category.assoc] using he
  let d := hp₀.desc (t ≫ p) (𝟙 _) (by simpa using hw)
  have hd : d = 𝟙 _ := by simpa [d] using hp₀.inr_desc (t ≫ p) (𝟙 _) (by simpa using hw)
  have hp : p₀ = t ≫ p := by
    have h := hp₀.inl_desc (t ≫ p) (𝟙 _) (by simpa using hw)
    change p₀ ≫ d = t ≫ p at h
    simpa only [hd, Category.comp_id] using h
  apply hp₀.of_iso (Iso.refl _) (asIso t) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, asIso_hom, Category.id_comp]
    exact (smallMap_comp X _ _).symm
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simpa only [Iso.refl_hom, asIso_hom, Category.comp_id] using hp
  · simp only [Iso.refl_hom, Category.comp_id]

end AlgebraicGeometry.ProEtale
