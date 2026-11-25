/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.PrincipalConeTower
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
import all WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
import WeilConjectures.Algebra.Homology.PrincipalConeExactEquivalence
import WeilConjectures.AlgebraicGeometry.PrincipalConeKoszulRoosComparison
import WeilConjectures.AlgebraicGeometry.PrincipalIdealLocalTestCriterion
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.NativeRingedRestrictionSlices
import WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
import all WeilConjectures.CategoryTheory.UnitPowerCompleteness

/-! # Reflection into internal principal cone outputs

Source: Stacks Project, Tags 099B, 0A0E and 0941.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory

attribute [local irreducible] CochainComplex.PrincipalCone.completion
  CochainComplex.PrincipalCone.unit principalKoszulRoosUnit roosF koszulTowerComplex
  koszulTensorTower

private theorem reflection_transport
    {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) [F.Full] [F.Faithful]
    {P C D : A} {P' C' D' : B} (η : P ⟶ C) (η' : P' ⟶ C')
    (p : F.obj P ≅ P') (c : F.obj C ≅ C') (d : F.obj D ≅ D')
    (hη : F.map η ≫ c.hom = p.hom ≫ η')
    (h : Function.Bijective (fun f : C' ⟶ D' ↦ η' ≫ f)) :
    Function.Bijective (fun f : C ⟶ D ↦ η ≫ f) := by
  constructor
  · intro f g hfg
    dsimp only at hfg
    apply F.map_injective
    apply (cancel_mono d.hom).mp
    apply (cancel_epi c.inv).mp
    apply h.1
    apply (cancel_epi p.hom).mp
    simp only [← Category.assoc, ← hη]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← F.map_comp_assoc, ← F.map_comp_assoc, hfg]
  · intro f
    obtain ⟨g, hg⟩ := h.2 (p.inv ≫ F.map f ≫ d.hom)
    dsimp only at hg
    obtain ⟨g', hg'⟩ := F.map_surjective (c.hom ≫ g ≫ d.inv)
    refine ⟨g', F.map_injective ?_⟩
    rw [F.map_comp, hg']
    rw [← Category.assoc (F.map η), hη]
    rw [Category.assoc, ← Category.assoc η', hg]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory in
private theorem internal_scalar_apply
    {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    [UnivLE.{max v w, u}] [HasSheafify J AddCommGrpCat.{u}]
    [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
    (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]
    (d : End (𝟙_ (Mod (Sheaf J AddCommGrpCat.{u}) R)))
    (M : Mod (Sheaf J AddCommGrpCat.{u}) R) (U : Cᵒᵖ)
    (x : ((InternalAbelianSheafModule.sectionModuleFunctor J R).obj M).val.obj U) :
    (((InternalAbelianSheafModule.sectionModuleFunctor J R).map
      ((λ_ M).inv ≫ d.asHom ▷ M ≫ (λ_ M).hom)).val.app U) x =
        @SMul.smul _ _
          (((InternalAbelianSheafModule.sectionModuleFunctor J R).obj M).val.obj U).isModule.toSMul
          ((((InternalAbelianSheafModule.sectionModuleFunctor J R).map d.asHom).val.app U)
            (1 : (InternalAbelianSheafModule.sectionRingSheaf J R).obj.obj U)) x := by
  let F := InternalAbelianSheafModule.sectionModuleFunctor J R
  let r : (InternalAbelianSheafModule.sectionRingSheaf J R).obj.obj U := 1
  let z := InternalAbelianSheafModule.comparison_internalTmul J R (𝟙_ _) M U r x
  have hz : ((F.map (λ_ M).hom).val.app U) z = x := by
    rw [InternalAbelianSheafModule.comparison_internalTmul_leftUnitor]
    exact one_smul _ _
  have hinv : ((F.map (λ_ M).inv).val.app U) x = z := by
    have hi : F.map (λ_ M).hom ≫ F.map (λ_ M).inv = 𝟙 _ := by
      rw [← F.map_comp, Iso.hom_inv_id, F.map_id]
    have he := congrArg (fun k : F.obj (𝟙_ _ ⊗ M) ⟶ F.obj (𝟙_ _ ⊗ M) ↦
      k.val.app U z) hi
    change ((F.map (λ_ M).inv).val.app U) (((F.map (λ_ M).hom).val.app U) z) = z at he
    rw [hz] at he
    exact he
  change ((F.map (λ_ M).hom).val.app U)
    (((F.map (d.asHom ▷ M)).val.app U) (((F.map (λ_ M).inv).val.app U) x)) = _
  rw [hinv]
  rw [← tensorHom_id]
  rw [InternalAbelianSheafModule.comparison_internalTmul_natural]
  rw [InternalAbelianSheafModule.comparison_internalTmul_leftUnitor]
  rfl

private theorem small_principal_reflection
    {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{v})
    [HasDerivedCategory.{w} (SheafOfModules.{v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.{v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{v}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    [HasExactLimitsOfShape (Discrete ℕ) (SheafOfModules.{v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (a : (R.obj ⋙ forget CommRingCat).sections)
    (P Q : CochainComplex (SheafOfModules.{v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (μ : End P) (ν : End Q)
    (hμ : ∀ (q : ℤ) (U : Cᵒᵖ) (x : (P.X q).val.obj U),
      (μ.asHom.f q).val.app U x = @SMul.smul (R.obj.obj U) ((P.X q).val.obj U)
        ((P.X q).val.obj U).isModule.toSMul
        (a.val U) x)
    (hν : ∀ (q : ℤ) (U : Cᵒᵖ) (x : (Q.X q).val.obj U),
      (ν.asHom.f q).val.app U x = @SMul.smul (R.obj.obj U) ((Q.X q).val.obj U)
        ((Q.X q).val.obj U).isModule.toSMul
        (a.val U) x) :
    Function.Bijective (fun f :
      DerivedCategory.Q.obj (CochainComplex.PrincipalCone.completion μ) ⟶
      DerivedCategory.Q.obj (CochainComplex.PrincipalCone.completion ν) ↦
      DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ) ≫ f) := by
  let := principalLocalTestSliceDerived R
  let I := image (ringedKoszulScalar R a).asHom
  let ι := image.ι (ringedKoszulScalar R a).asHom
  obtain ⟨D, hC, hbij, _, _⟩ := ringedKoszulCompletionReflector R 1 (fun _ ↦ a)
    I ι (principal_generators R a)
  let b : (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections := ⟨a.val, a.property⟩
  obtain ⟨cP, hcP⟩ := principalConeKoszulRoosComparison R P a μ hμ
  obtain ⟨cQ, _⟩ := principalConeKoszulRoosComparison R Q a ν hν
  obtain ⟨dP, hdP⟩ := principalKoszulRoos_presentation_comparison R b P D
  obtain ⟨dQ, _⟩ := principalKoszulRoos_presentation_comparison R b Q D
  apply reflection_transport (𝟭 _) _ (D.unit (DerivedCategory.Q.obj P))
    (Iso.refl _) (cP ≪≫ dP) (cQ ≪≫ dQ)
  · simp only [Functor.id_map, Iso.trans_hom, Iso.refl_hom, Category.id_comp]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f ↦ f ≫ dP.hom) hcP).trans hdP)
  · exact hbij _ _ (hC _)

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.AdicCompletion

attribute [local irreducible] upperStarFromPoint
attribute [local instance] ringMonoidalObject ringCommutative modulesMonoidal
  modulesDerived modulesProducts complexProducts

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

private abbrev sectionEquiv :=
  InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (ring l E X)

private abbrev sectionRing :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (ring l E X)

private abbrev smallDown := AsSmall.down.{u, u + 1, u + 1} (C := X.ProEt)

private theorem smallDown_isEquivalence : (smallDown X).IsEquivalence :=
  (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).isEquivalence_inverse

attribute [local instance] smallDown_isEquivalence

private abbrev smallTopology := (smallDown X).inducedTopology (Scheme.ProEt.topology X)

private abbrev sectionRestriction :=
  NativeRestriction.restrictModules.{u + 1, u + 1, u + 1, u, u + 1}
    (K := smallTopology X) (smallDown X) (sectionRing l E X)

private theorem sectionRestriction_isEquivalence : (sectionRestriction l E X).IsEquivalence :=
  NativeRestriction.globalModulesEquivalence _ _

attribute [local instance] sectionRestriction_isEquivalence

private abbrev smallSectionRing :=
  NativeRestriction.restrictedCommRing.{u + 1, u + 1, u + 1, u, u + 1}
    (K := smallTopology X) (smallDown X) (sectionRing l E X)

private def sectionTransport := (sectionEquiv l E X).functor ⋙ sectionRestriction l E X

private theorem sectionTransport_additive : (sectionTransport l E X).Additive := by
  let : (sectionEquiv l E X).functor.Additive :=
    InternalAbelianSheafModule.comparison_additive.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) (ring l E X)
  dsimp only [sectionTransport]
  infer_instance

attribute [local instance] sectionTransport_additive

private theorem sectionTransport_isEquivalence : (sectionTransport l E X).IsEquivalence := by
  dsimp only [sectionTransport]
  infer_instance

attribute [local instance] sectionTransport_isEquivalence

private def scalarAtUnit (d : End (Mod.regular (DerivedNakayama.integerRing l E))) :
    End (𝟙_ (Modules l E X)) :=
  .of ((DerivedNakayama.regularPullbackIso l E X).inv ≫
    (DerivedNakayama.pullback l E X).map d.asHom ≫
      (DerivedNakayama.regularPullbackIso l E X).hom)

private def scalarSection (d : End (Mod.regular (DerivedNakayama.integerRing l E))) :
    ((sectionRing l E X).obj ⋙ forget CommRingCat).sections where
  val U := (((sectionEquiv l E X).functor.map (scalarAtUnit l E X d).asHom).val.app U)
    (1 : (sectionRing l E X).obj.obj U)
  property {U V} f := by
    have h := NatTrans.naturality_apply
      ((PresheafOfModules.toPresheaf _).map
        ((sectionEquiv l E X).functor.map (scalarAtUnit l E X d).asHom).val) f
      (1 : (sectionRing l E X).obj.obj U)
    have h' := h.symm
    change (sectionRing l E X).obj.map f
      ((((sectionEquiv l E X).functor.map (scalarAtUnit l E X d).asHom).val.app U)
        (1 : (sectionRing l E X).obj.obj U)) =
        (((sectionEquiv l E X).functor.map (scalarAtUnit l E X d).asHom).val.app V)
          ((sectionRing l E X).obj.map f (1 : (sectionRing l E X).obj.obj U)) at h'
    exact h'.trans (congrArg
      (fun x : (sectionRing l E X).obj.obj V ↦
        (((sectionEquiv l E X).functor.map (scalarAtUnit l E X d).asHom).val.app V) x)
      ((sectionRing l E X).obj.map f).hom.map_one)

private def smallScalarSection
    (d : End (Mod.regular (DerivedNakayama.integerRing l E))) :
    ((smallSectionRing l E X).obj ⋙ forget CommRingCat).sections where
  val U := (scalarSection l E X d).val ((smallDown X).op.obj U)
  property f := (scalarSection l E X d).property ((smallDown X).op.map f)

private theorem scalar_section_apply
    (d : End (Mod.regular (DerivedNakayama.integerRing l E)))
    (P : CochainComplex (Modules l E X) ℤ)
    (q : ℤ) (U : (AsSmall.{u + 1} X.ProEt)ᵒᵖ)
    (x : (((sectionTransport l E X).obj (P.X q)).val.obj U)) :
    (((sectionTransport l E X).map
      ((DerivedNakayama.scalarOnComplex l E X d P).f q)).val.app U) x =
      @SMul.smul _ _ (((sectionTransport l E X).obj (P.X q)).val.obj U).isModule.toSMul
        ((smallScalarSection l E X d).val U) x := by
  exact internal_scalar_apply _ _ (scalarAtUnit l E X d) (P.X q)
    ((smallDown X).op.obj U) x

attribute [local irreducible] CochainComplex.PrincipalCone.completion
  CochainComplex.PrincipalCone.unit sectionTransport

/-- Maps into a principal cone completion extend uniquely across the principal cone unit.
Source: Stacks 099B (derived completion is a reflection), 0A0E (Koszul computation),
and 0941 (Roos computation of the strict derived limit).
(auxiliary; not a blueprint node).

Proof: reconstruct section modules by the exact tensor equivalence. The scalar d is
multiplication by the constant uniformizer, as follows by the displayed test on every
continuous function and every point. The two-term principal cone tower therefore becomes
the singleton negative Koszul tower, with transitions (pi,1) and degree-zero inclusions.
The equivalence preserves products and mapping cocones. Exact countable products on the
pro-etale site identify this Roos complex with total derived inverse limit, preserving
the strict zero-homotopy unit. The singleton Koszul reflector has locally complete output
for Q and its unit on P induces a Hom bijection into every locally complete object.
Apply that bijection to the output for Q and transport back through the fully faithful
derived section equivalence. Finite free Koszul factors preserve quasi-isomorphisms,
so neither P nor Q needs K-flatness, boundedness, or termwise flatness. -/
theorem internal_principal_cone_hom_reflection
    (d : End (Mod.regular (DerivedNakayama.integerRing l E)))
    (hd : ∀ (S : Profinite.{u}ᵒᵖ) (f : (DerivedNakayama.integerRing l E).obj.obj S)
      (s : S.unop), ((d.asHom.hom.hom.app S) f).down s =
        Padic.coefficientExtensionUniformizer l E * f.down s)
    (P Q : CochainComplex (Modules l E X) ℤ) :
    Function.Bijective (fun f :
      DerivedCategory.Q.obj (CochainComplex.PrincipalCone.completion
        (End.of (DerivedNakayama.scalarOnComplex l E X d P))) ⟶
      DerivedCategory.Q.obj (CochainComplex.PrincipalCone.completion
        (End.of (DerivedNakayama.scalarOnComplex l E X d Q))) ↦
      DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit
        (End.of (DerivedNakayama.scalarOnComplex l E X d P))) ≫ f) := by
  have _ := hd
  clear hd
  let R := smallSectionRing l E X
  let A := SheafOfModules.{u + 1}
    ((sheafCompose (smallTopology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let := HasDerivedCategory.standard A
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ A)
  let (U : AsSmall.{u + 1} X.ProEt) := HasDerivedCategory.standard
    (SheafOfModules.{u + 1}
      (((sheafCompose (smallTopology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over U))
  let H := sectionTransport l E X
  let G := H.mapHomologicalComplex (.up ℤ)
  let μ := End.of (DerivedNakayama.scalarOnComplex l E X d P)
  let ν := End.of (DerivedNakayama.scalarOnComplex l E X d Q)
  let μ' := End.of (G.map μ.asHom)
  let ν' := End.of (G.map ν.asHom)
  let : CountableAB4Star (Modules l E X) := modules_countableAB4Star l E X
  let : HasExactLimitsOfShape (Discrete ℕ) A :=
    HasExactLimitsOfShape.of_codomain_equivalence (Discrete ℕ) H.asEquivalence
  have hμ : ∀ (q : ℤ) (U : (AsSmall.{u + 1} X.ProEt)ᵒᵖ)
      (x : ((G.obj P).X q).val.obj U),
      (μ'.asHom.f q).val.app U x = @SMul.smul _ _ (((G.obj P).X q).val.obj U).isModule.toSMul
        ((smallScalarSection l E X d).val U) x := scalar_section_apply l E X d P
  have hν : ∀ (q : ℤ) (U : (AsSmall.{u + 1} X.ProEt)ᵒᵖ)
      (x : ((G.obj Q).X q).val.obj U),
      (ν'.asHom.f q).val.app U x = @SMul.smul _ _ (((G.obj Q).X q).val.obj U).isModule.toSMul
        ((smallScalarSection l E X d).val U) x := scalar_section_apply l E X d Q
  obtain ⟨cP, hcP⟩ := CochainComplex.principalCompletionMap H μ
  obtain ⟨cQ, _⟩ := CochainComplex.principalCompletionMap H ν
  let eP := H.mapDerivedCategoryFactors.app P
  let eC := H.mapDerivedCategoryFactors.app (CochainComplex.PrincipalCone.completion μ) ≪≫
    DerivedCategory.Q.mapIso cP
  let eD := H.mapDerivedCategoryFactors.app (CochainComplex.PrincipalCone.completion ν) ≪≫
    DerivedCategory.Q.mapIso cQ
  apply reflection_transport H.mapDerivedCategory _
    (DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ')) eP eC eD
  · change H.mapDerivedCategory.map (DerivedCategory.Q.map
        (CochainComplex.PrincipalCone.unit μ)) ≫
        H.mapDerivedCategoryFactors.hom.app _ ≫ DerivedCategory.Q.map cP.hom =
      H.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ')
    rw [← Category.assoc, H.mapDerivedCategoryFactors_hom_naturality, Category.assoc]
    have hmap := congrArg
      (fun f : G.obj P ⟶ CochainComplex.PrincipalCone.completion μ' ↦
        DerivedCategory.Q.map f) hcP
    rw [Functor.map_comp] at hmap
    exact congrArg (fun f ↦ H.mapDerivedCategoryFactors.hom.app P ≫ f) hmap
  · exact small_principal_reflection R (smallScalarSection l E X d)
      (G.obj P) (G.obj Q) μ' ν' hμ hν

end AlgebraicGeometry.ProEtale.AdicCompletion
