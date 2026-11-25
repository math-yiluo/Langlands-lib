/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.OpenModuleDerivedSections
public import WeilConjectures.CategoryTheory.DerivedLimitRoosAbelianGroups
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import WeilConjectures.CategoryTheory.Triangulated.MilnorSequence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# Cohomology over an open and derived inverse limits

Source: literature/stacks-project/cohomology.tex, Tag 0D60, label
lemma-RGamma-commutes-with-Rlim (blueprint: lem-pc-ringed-space-rgamma-derived-limit).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RingedSpace

/-- The product argument of Stacks Tag 08U1 applies to modules on a ringed space.
The unit on K-injective representatives identifies the sectionwise product with its
image in the derived category of abelian groups, whose products are exact. -/
private theorem openModuleDerivedSections_preservesCountableProducts
    (X : RingedSpace.{u}) (U : TopologicalSpace.Opens X)
    [HasDerivedCategory.{v} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} AddCommGrpCat.{u}] :
    PreservesLimitsOfShape (Discrete ℕ) (openModuleDerivedSections X U) := by
  let F := openModuleSections X U
  have : PreservesLimitsOfShape (Discrete ℕ) F := by
    dsimp [F, openModuleSections]
    infer_instance
  classical
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let q := HomotopyCategory.quotient (SheafOfModules.{u} (moduleRings X)) (ComplexShape.up ℤ)
  let a : G ⋙ DerivedCategory.Q ≅
      q ⋙ (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
    Functor.isoWhiskerLeft G (DerivedCategory.quotientCompQhIso AddCommGrpCat).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors _).symm DerivedCategory.Qh ≪≫
      Functor.associator _ _ _
  let β : G ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    a.hom ≫ Functor.whiskerLeft q F.rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      (Functor.isoWhiskerRight
        (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (moduleRings X)))
        F.rightDerivedFunctor).hom
  have hβ (I : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) [I.IsKInjective] :
      IsIso (β.app I) := by
    dsimp [β, a]
    infer_instance
  obtain ⟨hP, hQ, _⟩ := derivedCategory_countableProducts_and_towerLimit AddCommGrpCat.{u}
  have : ∀ (I : ℕ → CochainComplex AddCommGrpCat.{u} ℤ),
      PreservesLimit (Discrete.functor I) DerivedCategory.Q := fun I ↦
    preservesLimit_of_preserves_limit_cone (limit.isLimit _) (hQ ℕ I).some
  have : PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.Q (C := AddCommGrpCat.{u})) :=
    preservesLimitsOfShape_of_discrete _
  have hfamily (K : ℕ → DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
      PreservesLimit (Discrete.functor K) F.rightDerivedFunctor := by
    have hex (n : ℕ) := DerivedCategory.exists_iso_Q_obj_of_isKInjective (K n)
    choose I hI he using hex
    let e (n : ℕ) := (Classical.choice (he n)).symm
    have : ∀ n, (I n).IsKInjective := hI
    let P := HomologicalComplex.coneOfHasLimitEval (Discrete.functor I)
    let qP := HomotopyCategory.quotient (SheafOfModules.{u} (moduleRings X)) (.up ℤ)
    let hqFan := HomotopyCategory.isLimitFanQuotient (SheafOfModules.{u} (moduleRings X)) (.up ℤ)
      (HomologicalComplex.isLimitConeOfHasLimitEval (Discrete.functor I))
    have hPI : CochainComplex.IsKInjective P.pt := by
      rw [CochainComplex.isKInjective_iff_rightOrthogonal]
      exact (HomotopyCategory.subcategoryAcyclic
        (SheafOfModules.{u} (moduleRings X))).rightOrthogonal.prop_of_isLimit
        hqFan (fun j ↦ CochainComplex.IsKInjective.rightOrthogonal (I j.as))
    have : CochainComplex.IsKInjective P.pt := hPI
    let hqP := (Fan.isLimitMapConeEquiv qP I P).symm hqFan
    let L := DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X))
    let pre (s : Cone ((Discrete.functor I ⋙ qP) ⋙ L)) :
        Cone (Discrete.functor I ⋙ qP) :=
      { pt := L.objPreimage s.pt
        π := Discrete.natTrans fun j ↦
          (Equiv.ofBijective _ (CochainComplex.IsKInjective.Qh_map_bijective
            (L.objPreimage s.pt) (I j.as))).symm
              ((L.objObjPreimageIso s.pt).hom ≫ s.π.app j) }
    have key (s : Cone ((Discrete.functor I ⋙ qP) ⋙ L)) (j : Discrete ℕ) :
        L.map ((pre s).π.app j) = (L.objObjPreimageIso s.pt).hom ≫ s.π.app j :=
      (Equiv.ofBijective _ (CochainComplex.IsKInjective.Qh_map_bijective
        (L.objPreimage s.pt) (I j.as))).apply_symm_apply _
    have hd : IsLimit (L.mapCone (qP.mapCone P)) := by
      refine
        { lift := fun s ↦ (L.objObjPreimageIso s.pt).inv ≫ L.map (hqP.lift (pre s))
          fac := ?_
          uniq := ?_ }
      · intro s j
        dsimp only [Functor.mapCone_π_app]
        have fac := hqP.fac (pre s) j
        dsimp only [Functor.mapCone_π_app] at fac
        rw [Category.assoc, ← L.map_comp, fac, key]
        simp
      · intro s m hm
        dsimp only [Functor.mapCone_π_app] at hm
        obtain ⟨m', hm'⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
          (L.objPreimage s.pt) P.pt).surjective ((L.objObjPreimageIso s.pt).hom ≫ m)
        have eq : m' = hqP.lift (pre s) := by
          apply hqP.uniq (pre s) m'
          intro j
          apply (CochainComplex.IsKInjective.Qh_map_bijective
            (L.objPreimage s.pt) (I j.as)).injective
          simp only [Functor.mapCone_π_app]
          rw [L.map_comp, hm', Category.assoc, hm j, key]
        rw [← eq, hm']
        simp
    have hPL : IsLimit (DerivedCategory.Q.mapCone P) :=
      IsLimit.mapConeEquiv
        (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (moduleRings X))) hd
    have hFPL := isLimitOfPreserves DerivedCategory.Q
      (isLimitOfPreserves G (HomologicalComplex.isLimitConeOfHasLimitEval (Discrete.functor I)))
    let α : Discrete.functor I ⋙ DerivedCategory.Q ≅ Discrete.functor K :=
      Discrete.natIso (fun (n : Discrete ℕ) ↦ e n.as)
    let c := (Cone.postcompose α.hom).obj (DerivedCategory.Q.mapCone P)
    have hc : IsLimit c := (IsLimit.postcomposeHomEquiv α _).symm hPL
    apply preservesLimit_of_preserves_limit_cone hc
    let αβ : (Discrete.functor I ⋙ G) ⋙ DerivedCategory.Q ≅
        (Discrete.functor I ⋙ DerivedCategory.Q) ⋙ F.rightDerivedFunctor :=
      Discrete.natIso (fun (n : Discrete ℕ) ↦ asIso (β.app (I n.as)))
    have hmap : IsLimit (F.rightDerivedFunctor.mapCone (DerivedCategory.Q.mapCone P)) :=
      (IsLimit.equivOfNatIsoOfIso αβ
        (DerivedCategory.Q.mapCone (G.mapCone P))
        (F.rightDerivedFunctor.mapCone (DerivedCategory.Q.mapCone P))
        (Cone.ext (asIso (β.app P.pt)) (fun n ↦ by
          simpa [αβ] using β.naturality (P.π.app n)))).1 hFPL
    exact (IsLimit.equivOfNatIsoOfIso (Functor.isoWhiskerRight α F.rightDerivedFunctor)
      (F.rightDerivedFunctor.mapCone (DerivedCategory.Q.mapCone P))
      (F.rightDerivedFunctor.mapCone c) (Cone.ext (Iso.refl _) (fun n ↦ by simp [c]))).1 hmap
  exact preservesLimitsOfShape_of_discrete _


-- Prove the product/triangle comparison abstractly, so rewriting does not unfold
-- the localization constructions of the source and target derived categories.
private theorem map_isDerivedLimitTriangle_of_preservesProduct
    {C D : Type*} [Category C] [Category D]
    [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
    [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (Φ : C ⥤ D) [Φ.Additive] [Φ.CommShift ℤ] [Φ.IsTriangulated]
    {K : ℕ → C} [HasProduct K] [HasProduct (fun n ↦ Φ.obj (K n))]
    [PreservesLimit (Discrete.functor K) Φ]
    (f : ∀ n, K (n + 1) ⟶ K n) (L : C)
    (p : L ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧)
    (h : IsDerivedLimitTriangle f L p δ) :
    ∃ e : Φ.obj (∏ᶜ K) ≅ ∏ᶜ (fun n ↦ Φ.obj (K n)),
      (∀ n, e.hom ≫ Pi.π _ n = Φ.map (Pi.π K n)) ∧
      IsDerivedLimitTriangle (fun n ↦ Φ.map (f n)) (Φ.obj L) (Φ.map p ≫ e.hom)
        (e.inv ≫ Φ.map δ ≫ (Φ.commShiftIso (1 : ℤ)).hom.app L) := by
  let e := PreservesProduct.iso Φ K
  have he (n : ℕ) : e.hom ≫ Pi.π _ n = Φ.map (Pi.π K n) := by
    simp [e]
  refine ⟨e, he, ?_⟩
  have ht : Φ.map (towerTransitionEndomorphism f) ≫ e.hom =
      e.hom ≫ towerTransitionEndomorphism (fun n ↦ Φ.map (f n)) := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, he, towerTransitionEndomorphism, towerProductShift,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
      Pi.lift_comp_π, Functor.map_sub]
    rw [← Category.assoc, he, ← Functor.map_comp]
    rw [← Functor.map_comp, Pi.lift_comp_π, Category.id_comp, Functor.map_comp]
  exact Pretriangulated.isomorphic_distinguished _ (Φ.map_distinguished _ h) _
    (Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm
      (by change (Φ.map p ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ Φ.map p; simp)
      (by
        change towerTransitionEndomorphism (fun n ↦ Φ.map (f n)) ≫ e.inv =
          e.inv ≫ Φ.map (towerTransitionEndomorphism f)
        apply (cancel_mono e.hom).1
        simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
          Iso.inv_hom_id_assoc] using congrArg (fun t ↦ e.inv ≫ t) ht.symm)
      (by
        change (e.inv ≫ Φ.map δ ≫ (Φ.commShiftIso (1 : ℤ)).hom.app L) ≫
          (shiftFunctor _ (1 : ℤ)).map (𝟙 _) =
            e.inv ≫ (Φ.map δ ≫ (Φ.commShiftIso (1 : ℤ)).hom.app L)
        simp))

/-- Derived sections over an open preserve Roos triangles and satisfy the Milnor
short exact sequence.  The functor `RΓ(U,-)` is represented by K-injective
resolutions of complexes of modules, via `openModuleDerivedSections`.
Source: literature/stacks-project/cohomology.tex, Tag 0D60, label
lemma-RGamma-commutes-with-Rlim (blueprint: lem-pc-ringed-space-rgamma-derived-limit).

Proof, following Tag 0D60:
1. The site of opens is small. K-injective resolutions exist by
   `prop-pur-kinjective-resolutions-exist`, and sections preserve limits by
   `situation-conventions`. The right derived functor
   is triangulated (`lem-pc-right-derived-functor-triangulated`). Products exist
   by the generic K-injective product construction and
   `lemma-reduction-derived-nakayama`, using exact products in abelian groups
   (`lem-pc-abelian-groups-exact-products`).
2. Resolve each tower term by a K-injective complex. Its termwise product is
   K-injective and represents the derived product
   (`lem-pc-ringed-space-product-kinjective`). Sections identify it with the
   product of the sections complexes; exact products of abelian groups identify
   this with the target derived product (`lemma-reduction-derived-nakayama`).
   The projection equations characterize the comparison. The triangulated
   functor sends the Roos triangle to the target Roos triangle
   by a triangle isomorphism. Its middle square follows after every product projection
   by functoriality and additivity (`def-weil-derived-limit`).
3. Apply `milnor_shortExact` (`lem-pc-derived-limit-milnor-sequence`) to the
   image tower and its specified Roos triangle. Its right-map projection equations
   become the claimed equations using the comparison projection equations and
   functoriality. The association of the three composed functors is normalized
   explicitly when checking these equations.
-/
theorem rgamma_derivedLimit (X : RingedSpace.{u}) (U : TopologicalSpace.Opens X)
    [HasDerivedCategory.{v} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} AddCommGrpCat.{u}]
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (L : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (p : L ⟶ ∏ᶜ (fun n : ℕ => K.obj (Opposite.op n)))
    (δ : (∏ᶜ (fun n : ℕ => K.obj (Opposite.op n))) ⟶ L⟦(1 : ℤ)⟧)
    (hK : IsDerivedLimitTriangle
      (fun n : ℕ => K.map (homOfLE (Nat.le_succ n)).op) L p δ) :
    (∃ e : (openModuleDerivedSections X U).obj (∏ᶜ (fun n : ℕ => K.obj (Opposite.op n))) ≅
        ∏ᶜ (fun n : ℕ => (openModuleDerivedSections X U).obj (K.obj (Opposite.op n))),
      (∀ n, e.hom ≫ Pi.π _ n = (openModuleDerivedSections X U).map (Pi.π _ n)) ∧
      IsDerivedLimitTriangle
        (fun n => (openModuleDerivedSections X U).map (K.map (homOfLE (Nat.le_succ n)).op))
        ((openModuleDerivedSections X U).obj L) ((openModuleDerivedSections X U).map p ≫ e.hom)
        (e.inv ≫ (openModuleDerivedSections X U).map δ ≫
          ((openModuleDerivedSections X U).commShiftIso (1 : ℤ)).hom.app L)) ∧
    (∀ m : ℤ, ∃ (a :
        (@Functor.rightDerived _ _ _ _ _
          (@InjectiveResolution.instHasInjectiveResolutions _ _ _
            roosTowerEnoughInjectives) _
          (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u})
          roosLimitAdditive 1).obj
          (K ⋙ (openModuleDerivedSections X U) ⋙
            DerivedCategory.homologyFunctor AddCommGrpCat.{u} (m - 1)) ⟶
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj
          ((openModuleDerivedSections X U).obj L))
      (b : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj
          ((openModuleDerivedSections X U).obj L) ⟶
        limit (K ⋙ (openModuleDerivedSections X U) ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} m)),
      ∃ hz : a ≫ b = 0,
        (ShortComplex.mk a b hz).ShortExact ∧
        ∀ n, b ≫ limit.π
            (K ⋙ (openModuleDerivedSections X U) ⋙
              DerivedCategory.homologyFunctor AddCommGrpCat.{u} m)
            (Opposite.op n) =
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map
            ((openModuleDerivedSections X U).map (p ≫ Pi.π _ n))) := by
  let f := fun n : ℕ => K.map (homOfLE (Nat.le_succ n)).op
  have hfirst : (∃ e : (openModuleDerivedSections X U).obj
      (∏ᶜ (fun n : ℕ => K.obj (Opposite.op n))) ≅
        ∏ᶜ (fun n : ℕ => (openModuleDerivedSections X U).obj (K.obj (Opposite.op n))),
      (∀ n, e.hom ≫ Pi.π _ n = (openModuleDerivedSections X U).map (Pi.π _ n)) ∧
      IsDerivedLimitTriangle
        (fun n => (openModuleDerivedSections X U).map (K.map (homOfLE (Nat.le_succ n)).op))
        ((openModuleDerivedSections X U).obj L) ((openModuleDerivedSections X U).map p ≫ e.hom)
        (e.inv ≫ (openModuleDerivedSections X U).map δ ≫
          ((openModuleDerivedSections X U).commShiftIso (1 : ℤ)).hom.app L)) := by
    have := openModuleDerivedSections_preservesCountableProducts X U
    exact map_isDerivedLimitTriangle_of_preservesProduct
      (openModuleDerivedSections X U) f L p δ hK
  obtain ⟨e, he, hT⟩ := hfirst
  refine ⟨⟨e, he, hT⟩, ?_⟩
  intro m
  obtain ⟨a, b, hab, _⟩ := CategoryTheory.milnor_shortExact.{u, w} m
  obtain ⟨⟨hz, hseq⟩, hb⟩ := hab (K ⋙ openModuleDerivedSections X U)
    ((openModuleDerivedSections X U).obj L)
    ((openModuleDerivedSections X U).map p ≫ e.hom)
    (e.inv ≫ (openModuleDerivedSections X U).map δ ≫
      ((openModuleDerivedSections X U).commShiftIso (1 : ℤ)).hom.app L) hT
  refine ⟨_, _, hz, hseq, ?_⟩
  intro n
  simpa only [Functor.comp, Category.assoc, he n, ← Functor.map_comp] using hb n

end AlgebraicGeometry.RingedSpace
