/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ConstructibleExtContinuity
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimitHomSurjTransfer

/-!
# (Hom)-surjectivity of the cocone of bounded constructible categories

Let `ℓ` be a prime, `X` a topologically noetherian scheme and `E, F` finite subextensions of
`ℚ̄_ℓ`. Every morphism `f : T^X_{E,Ω} K ⟶ T^X_{F,Ω} L` from the extension of scalars of a bounded
constructible `E_X`-complex `K` to that of a bounded below `F_X`-complex `L` is of the form
`τ⁻¹ ≫ T^X_{H,Ω} g ≫ τ` for a finite subextension `H ⊇ E, F` and a morphism
`g : T^X_{E,H} K ⟶ T^X_{F,H} L` (`ProEtale.exists_derivedExtendScalarsToPadicAlgCl_map_eq`,
blueprint `proposition-dctf-x-qbar-2-colimit--3`).

Represent `L` by a complex `Y` of `F_X`-modules vanishing below some degree. By adjunction, `f`
corresponds to a morphism `K ⟶ D(Res_{E→Ω})(ℚ̄_ℓ,X ⊗_{F_X} Y)`, and
`Res_{E→Ω}(ℚ̄_ℓ,X ⊗_{F_X} Y) = colim_k Res_{E→k}(k_X ⊗_{F_X} Y)` is a filtered colimit of complexes
vanishing below the same degree (`ProEtale.isColimitSubfieldExtendScalarsCocone`). By the
continuity of `Hom` out of `K`
(`ProEtale.CondensedRing.constructibleExtContinuity_continuousMapRingObj`),
it factors through some `Res_{E→k}(k_X ⊗_{F_X} Y)`, which is identified with the adjoint transfer
of the transitivity isomorphisms (`ProEtale.compIsoTransfer_derivedExtendScalars_Qh`), and one
concludes by `CategoryTheory.Adjunction.eq_inv_app_comp_map_comp_hom_app`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory

/-- A morphism `f : K ⟶ B` such that `f ≫ β ≫ z⁻¹ = g ≫ S ι` for isomorphisms `β : B ≅ P`,
`z : S ≅ 𝟭` and a morphism `ι : Y ⟶ P` with `w ≫ ι = κ ≫ β` for an isomorphism `w : W ≅ Y`
factors through `κ : W ⟶ B`. -/
private lemma eq_comp_of_comp_shift_eq {C : Type*} [Category C] (S : C ⥤ C) (z : S ≅ 𝟭 C)
    {K W B Y P : C} (f : K ⟶ B) (κ : W ⟶ B) (ι : Y ⟶ P) (β : B ≅ P) (w : W ≅ Y)
    (hw : w.hom ≫ ι = κ ≫ β.hom) (g : K ⟶ S.obj Y) (hg : f ≫ β.hom ≫ z.inv.app P = g ≫ S.map ι) :
    f = (g ≫ z.hom.app Y ≫ w.inv) ≫ κ := by
  have h₁ : f = g ≫ S.map ι ≫ z.hom.app P ≫ β.inv := by
    rw [← reassoc_of% hg]
    simp
  have h₂ : κ = w.hom ≫ ι ≫ β.inv := by
    rw [reassoc_of% hw]
    simp
  rw [h₁, h₂]
  have h₃ := z.hom.naturality ι
  simp only [Functor.id_map] at h₃
  simp [reassoc_of% h₃]

/-- If `f ≫ Ψ' e = x ≫ Φ g ≫ τ'_{L'}` for an isomorphism `e : L ≅ L'` and `τ' : T' ⋙ Φ ≅ Ψ'`,
then `f = x ≫ Φ (g ≫ T' e⁻¹) ≫ τ'_L`. -/
private lemma Functor.eq_comp_map_comp_hom_app_of_iso {C D E : Type*} [Category C] [Category D]
    [Category E] {T' : C ⥤ D} {Φ : D ⥤ E} {Ψ' : C ⥤ E} (τ' : T' ⋙ Φ ≅ Ψ') {A : E} {B : D}
    {L L' : C} (e : L ≅ L') (f : A ⟶ Ψ'.obj L) (x : A ⟶ Φ.obj B) (g : B ⟶ T'.obj L')
    (h : f ≫ Ψ'.map e.hom = x ≫ Φ.map g ≫ τ'.hom.app L') :
    f = x ≫ Φ.map (g ≫ T'.map e.inv) ≫ τ'.hom.app L := by
  have h' := τ'.hom.naturality e.inv
  simp only [Functor.comp_map] at h'
  rw [Φ.map_comp, Category.assoc, h', ← reassoc_of% h, ← Ψ'.map_comp, Iso.hom_inv_id, Ψ'.map_id,
    Category.comp_id]

/-- Pasting an equation `x ≫ y ≫ q = κ ≫ d ≫ e` with a commutative square `q ≫ f = c ≫ i`. -/
private lemma comp_comp_comp_eq_of_eq {C : Type*} [Category C] {A B M N D D' P : C} {Cc : C}
    (x : A ⟶ B) (y : B ⟶ Cc) (c : Cc ⟶ D) (i : D ⟶ P) (q : Cc ⟶ D') (f : D' ⟶ P) (κ : A ⟶ M)
    (d : M ⟶ N) (e : N ⟶ D') (h : x ≫ y ≫ q = κ ≫ d ≫ e) (n : q ≫ f = c ≫ i) :
    x ≫ y ≫ c ≫ i = κ ≫ d ≫ e ≫ f := by
  rw [← n, reassoc_of% h]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The comparison `D(Res_{E→k}) T^X_{F,k} (Q Y) ≅ Q(Res_{E→k}(k_X ⊗_{F_X} Y))`, through the
counit of the derived extension of scalars and the factorization of `D(Res_{E→k})`. -/
noncomputable def derivedComapExtendScalarsQhIso {E F k : FiniteIntermediateField ℓ} (hE : E ≤ k)
    (hF : F ≤ k)
    (Y : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ F)) ℤ) :
    (Mod.comap (padicSubfieldRingObjMap X ℓ hE)).mapDerivedCategory.obj
      ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hF)).leftDerivedFunctor.obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj Y))) ≅
      DerivedCategory.Q.obj (((Mod.comap (padicSubfieldRingObjMap X ℓ hE)).mapHomologicalComplex
        _).obj (((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hF)).mapHomologicalComplex
          _).obj Y)) :=
  (Mod.comap (padicSubfieldRingObjMap X ℓ hE)).mapDerivedCategory.mapIso
    (asIso ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hF)).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ _).obj Y))) ≪≫
    (Mod.comap (padicSubfieldRingObjMap X ℓ hE)).mapDerivedCategoryFactorsh.app _ ≪≫
    (DerivedCategory.quotientCompQhIso _).app _

/-- The comparison `D(Res_{E→Ω}) T^X_{F,Ω} (Q Y) ≅ Q(Res_{E→Ω}(ℚ̄_ℓ,X ⊗_{F_X} Y))`, through the
counit of the derived extension of scalars and the factorization of `D(Res_{E→Ω})`. -/
noncomputable def derivedComapExtendScalarsToPadicAlgClQhIso (E F : FiniteIntermediateField ℓ)
    (Y : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ F)) ℤ) :
    (Mod.comap (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapDerivedCategory.obj
      ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ F)).leftDerivedFunctor.obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj Y))) ≅
      DerivedCategory.Q.obj (((Mod.comap
        (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapHomologicalComplex _).obj (((Mod.extendScalars
          (padicSubfieldRingObjToPadicAlgCl X ℓ F)).mapHomologicalComplex
          _).obj Y)) :=
  (Mod.comap (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapDerivedCategory.mapIso
    (asIso ((Mod.extendScalars
      (padicSubfieldRingObjToPadicAlgCl X ℓ F)).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ _).obj Y))) ≪≫
    (Mod.comap (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapDerivedCategoryFactorsh.app _ ≪≫
    (DerivedCategory.quotientCompQhIso _).app _

/-- The adjoint transfer, read through `derivedComapExtendScalarsQhIso` and
`derivedComapExtendScalarsToPadicAlgClQhIso`, is the image of the inclusion of the colimit cocone
`subfieldExtendScalarsCocone`. -/
lemma derivedComapExtendScalarsQhIso_hom_comp_Q_map {E F G : FiniteIntermediateField ℓ}
    (hE : E ≤ G) (hF : F ≤ G)
    (Y : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) ℤ)
    (k : PadicSubfieldAbove ℓ G) :
    (derivedComapExtendScalarsQhIso X ℓ (hE.trans k.property) (hF.trans k.property) Y).hom ≫
        DerivedCategory.Q.map ((subfieldExtendScalarsCocone X ℓ hE hF Y).ι.app k) =
      Adjunction.compIsoTransfer
        (Mod.derivedExtendMapDerivedCategoryAdjunction
          (padicSubfieldRingObjMap X ℓ (hE.trans k.property)))
        (Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldRingObjToPadicAlgCl X ℓ E))
        (derivedExtendScalarsCompIso X ℓ (hE.trans k.property))
        (derivedExtendScalarsCompIso X ℓ (hF.trans k.property))
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj Y)) ≫
        (derivedComapExtendScalarsToPadicAlgClQhIso X ℓ E F Y).hom := by
  have h := compIsoTransfer_derivedExtendScalars_Qh X ℓ hE hF Y k
  simp only [derivedComapExtendScalarsQhIso, derivedComapExtendScalarsToPadicAlgClQhIso,
    Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Iso.app_hom, Category.assoc]
  exact comp_comp_comp_eq_of_eq _ _ _ _ _ _ _ _ _ h
    (DerivedCategory.quotientCompQhIso_hom_naturality _)

/-- **(Hom)-surjectivity, for a complex vanishing below some degree**: every morphism
`T^X_{E,Ω} K ⟶ T^X_{F,Ω} (Q Y)` with `K` bounded constructible and `Y` strictly bounded below is
`τ⁻¹ ≫ T^X_{H,Ω} g ≫ τ` for some finite subextension `H ⊇ E, F`. -/
theorem exists_derivedExtendScalarsToPadicAlgCl_map_eq_of_isStrictlyGE
    [TopologicalSpace.NoetherianSpace X] {E F : FiniteIntermediateField ℓ}
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (hK : boundedConstructible (padicSubfieldRingObj X ℓ E) K)
    (Y : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) ℤ)
    (a : ℤ) [Y.IsStrictlyGE a]
    (f : (derivedExtendScalarsToPadicAlgCl X ℓ E).obj K ⟶
      (derivedExtendScalarsToPadicAlgCl X ℓ F).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj Y))) :
    ∃ (H : FiniteIntermediateField ℓ) (hE : E ≤ H) (hF : F ≤ H)
      (g : (derivedExtendScalarsSubfield X ℓ hE).obj K ⟶ (derivedExtendScalarsSubfield X ℓ hF).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj Y))),
      f = (derivedExtendScalarsCompIso X ℓ hE).inv.app K ≫
        (derivedExtendScalarsToPadicAlgCl X ℓ H).map g ≫
          (derivedExtendScalarsCompIso X ℓ hF).hom.app _ := by
  have hEG : E ≤ IsFiltered.max E F := leOfHom (IsFiltered.leftToMax E F)
  have hFG : F ≤ IsFiltered.max E F := leOfHom (IsFiltered.rightToMax E F)
  have hKj (k : PadicSubfieldAbove ℓ (IsFiltered.max E F)) :
      ((subfieldExtendScalarsDiagram X ℓ hEG hFG Y).obj k).IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact (Mod.comap (padicSubfieldRingObjMap X ℓ (hEG.trans k.property))).map_isZero
      ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ (hFG.trans k.property))).map_isZero
        (Y.isZero_of_isStrictlyGE a i hi))
  obtain ⟨k, g₀, hg₀⟩ := (CondensedRing.constructibleExtContinuity_continuousMapRingObj X ℓ E
    ⟨K, hK⟩ (subfieldExtendScalarsDiagram X ℓ hEG hFG Y) a hKj _
    (isColimitSubfieldExtendScalarsCocone X ℓ hEG hFG Y) 0).1
    ((Mod.derivedExtendMapDerivedCategoryAdjunction
      (padicSubfieldRingObjToPadicAlgCl X ℓ E)).homEquiv _ _ f ≫
        (derivedComapExtendScalarsToPadicAlgClQhIso X ℓ E F Y).hom ≫
        (shiftFunctorZero _ ℤ).inv.app _)
  exact ⟨k.obj, hEG.trans k.property, hFG.trans k.property, _,
    Adjunction.eq_inv_app_comp_map_comp_hom_app _ _ _ _ f _
      (eq_comp_of_comp_shift_eq _ (shiftFunctorZero _ ℤ) _ _ _
        (derivedComapExtendScalarsToPadicAlgClQhIso X ℓ E F Y)
        (derivedComapExtendScalarsQhIso X ℓ (hEG.trans k.property) (hFG.trans k.property) Y)
        (derivedComapExtendScalarsQhIso_hom_comp_Q_map X ℓ hEG hFG Y k) g₀ hg₀)⟩

/-- **(Hom)-surjectivity** (blueprint `proposition-dctf-x-qbar-2-colimit--3`): every morphism
`f : T^X_{E,Ω} K ⟶ T^X_{F,Ω} L` with `K` bounded constructible and `L` bounded constructible
(bounded below suffices) is `τ⁻¹ ≫ T^X_{H,Ω} g ≫ τ` for some finite subextension `H ⊇ E, F` and
some `g : T^X_{E,H} K ⟶ T^X_{F,H} L`. -/
theorem exists_derivedExtendScalarsToPadicAlgCl_map_eq [TopologicalSpace.NoetherianSpace X]
    {E F : FiniteIntermediateField ℓ}
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (hK : boundedConstructible (padicSubfieldRingObj X ℓ E) K)
    (L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)))
    (hL : boundedConstructible (padicSubfieldRingObj X ℓ F) L)
    (f : (derivedExtendScalarsToPadicAlgCl X ℓ E).obj K ⟶
      (derivedExtendScalarsToPadicAlgCl X ℓ F).obj L) :
    ∃ (H : FiniteIntermediateField ℓ) (hE : E ≤ H) (hF : F ≤ H)
      (g : (derivedExtendScalarsSubfield X ℓ hE).obj K ⟶
        (derivedExtendScalarsSubfield X ℓ hF).obj L),
      f = (derivedExtendScalarsCompIso X ℓ hE).inv.app K ≫
        (derivedExtendScalarsToPadicAlgCl X ℓ H).map g ≫
          (derivedExtendScalarsCompIso X ℓ hF).hom.app L := by
  obtain ⟨⟨a, b, hab⟩, -⟩ := (mem_boundedConstructible_iff _ L).1 hL
  have : L.IsGE a := (DerivedCategory.isGE_iff L a).2 fun i hi ↦ hab i (Or.inl hi)
  obtain ⟨Y, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE L a
  let e' : L ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj Y) :=
    e ≪≫ ((DerivedCategory.quotientCompQhIso _).app Y).symm
  obtain ⟨H, hE, hF, g, hg⟩ := exists_derivedExtendScalarsToPadicAlgCl_map_eq_of_isStrictlyGE X ℓ
    K hK Y a (f ≫ (derivedExtendScalarsToPadicAlgCl X ℓ F).map e'.hom)
  exact ⟨H, hE, hF, _, Functor.eq_comp_map_comp_hom_app_of_iso _ e' f _ g hg⟩

end AlgebraicGeometry.ProEtale
