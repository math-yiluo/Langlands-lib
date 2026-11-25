/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.TerminalScalarRealization
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
import WeilConjectures.Algebra.Homology.Scalar.ScalarLocalizationCoefficientAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Additive

/-! K-flat quasi-isomorphism preservation of the terminal scalar realization.

Source: Hemo--Richarz--Scholbach, Lemma 4.1(1), Remark 3.2.
(blueprint: new-lem-zl-contractible-realization-kflat-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.CondensedRing.Evaluation

open scoped ChangeOfRings ZeroObject

section PresheafExtension

variable {C : Type (u + 1)} [Category.{u} C]
  {R S : Cᵒᵖ ⥤ CommRingCat.{u + 1}} (φ : R ⟶ S)

-- The bottom topology lets us reuse the existing tensor construction on presheaves.
private def bottomRing (R : Cᵒᵖ ⥤ CommRingCat.{u + 1}) :
    Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u + 1} :=
  ⟨R, Presheaf.isSheaf_bot _⟩

private def bottomModule
    (M : PresheafOfModules.{u + 1} (R ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) :
    SheafOfModules.{u + 1} ((sheafCompose (⊥ : GrothendieckTopology C)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (bottomRing R)) :=
  ⟨M, Presheaf.isSheaf_bot _⟩

private def bottomMap : bottomRing R ⟶ bottomRing S := ⟨φ⟩

private def sectionExtension :
    PresheafOfModules.{u + 1} (R ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⥤
      PresheafOfModules.{u + 1} (S ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) where
  obj M := SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
    (J := ⊥) (bottomMap φ) (bottomModule M)
  map {M N} f :=
    { app X := (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (φ.app X).hom).map (f.app X)
      naturality := SheafOfModules.changeOfRingsHom_naturalityOfUniverses.{u, u + 1, u + 1, u + 1}
        (J := ⊥) (bottomMap φ) (bottomModule M) (N := bottomModule N) ⟨f⟩ }
  map_id M := by
    ext X : 1
    exact (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (φ.app X).hom).map_id _
  map_comp f g := by
    ext X : 1
    exact (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (φ.app X).hom).map_comp _ _

private theorem sectionExtension_map_tmul
    (M : PresheafOfModules.{u + 1} (R ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (s : S.obj X) (m : M.obj X) :
    ((sectionExtension φ).obj M).map f (s ⊗ₜ[R.obj X, (φ.app X).hom] m) =
      S.map f s ⊗ₜ[R.obj Y, (φ.app Y).hom] (show M.obj Y from M.map f m) :=
  SheafOfModules.changeOfRingsMap_tmulOfUniverses.{u, u + 1, u + 1, u + 1} (J := ⊥)
    (bottomMap φ) (bottomModule M) f s m

private def sectionScalarAdjunction (X : Cᵒᵖ) :
    ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (φ.app X).hom ⊣
      ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (φ.app X).hom :=
  ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} (φ.app X).hom

private theorem extension_lift_one (X : Cᵒᵖ) (M : ModuleCat.{u + 1} (R.obj X))
    (N : ModuleCat.{u + 1} (S.obj X))
    (g : M ⟶ (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (φ.app X).hom).obj N) (m : M) :
    (((sectionScalarAdjunction φ X).homEquiv _ _).symm g)
      ((1 : S.obj X) ⊗ₜ[R.obj X, (φ.app X).hom] m) = g m :=
  congrArg (fun f ↦ f m)
    (((sectionScalarAdjunction φ X).homEquiv _ _).apply_symm_apply g)

private def sectionHomEquiv
    (M : PresheafOfModules.{u + 1} (R ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
    (N : PresheafOfModules.{u + 1} (S ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) :
    ((sectionExtension φ).obj M ⟶ N) ≃
      (M ⟶ (PresheafOfModules.restrictScalars
        (Functor.whiskerRight φ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))).obj N) where
  toFun f :=
    { app X := (sectionScalarAdjunction φ X).homEquiv _ _ (f.app X)
      naturality := by
        intro X Y i
        ext m
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj X) ⊗ₜ[R.obj X, (φ.app X).hom] m)
        change f.app Y ((1 : S.obj Y) ⊗ₜ[R.obj Y, (φ.app Y).hom] M.map i m) =
          N.map i (f.app X ((1 : S.obj X) ⊗ₜ[R.obj X, (φ.app X).hom] m))
        simpa only [sectionExtension_map_tmul, map_one] using h }
  invFun g :=
    { app X := ((sectionScalarAdjunction φ X).homEquiv _ _).symm
        (g.app X)
      naturality := by
        intro X Y i
        apply ModuleCat.ExtendScalars.hom_ext
        intro m
        have h := PresheafOfModules.naturality_apply g i m
        change (((sectionScalarAdjunction φ Y).homEquiv _ _).symm
          (g.app Y)) (((sectionExtension φ).obj M).map i
            ((1 : S.obj X) ⊗ₜ[R.obj X, (φ.app X).hom] m)) =
          N.map i ((((sectionScalarAdjunction φ X).homEquiv _ _).symm
            (g.app X)) ((1 : S.obj X) ⊗ₜ[R.obj X, (φ.app X).hom] m))
        rw [sectionExtension_map_tmul, map_one]
        erw [extension_lift_one, extension_lift_one]
        exact h }
  left_inv f := by
    ext X : 1
    exact Equiv.symm_apply_apply _ _
  right_inv g := by
    ext X : 1
    exact Equiv.apply_symm_apply _ _

private def sectionAdjunction : sectionExtension φ ⊣
    PresheafOfModules.restrictScalars
      (Functor.whiskerRight φ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := sectionHomEquiv φ
      homEquiv_naturality_left_symm := by
        intro M M' N f g
        ext X : 1
        exact (sectionScalarAdjunction φ X).homEquiv_naturality_left_symm
          (f.app X) (g.app X)
      homEquiv_naturality_right := by
        intro M N N' f g
        ext X : 1
        exact (sectionScalarAdjunction φ X).homEquiv_naturality_right
          (f.app X) (g.app X) }

private instance sectionExtension_additive : (sectionExtension φ).Additive :=
  (sectionAdjunction φ).left_adjoint_additive

end PresheafExtension

private theorem presheaf_exact_of_evaluation
    {C : Type (u + 1)} [Category.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u + 1}}
    (S : ShortComplex (PresheafOfModules.{u + 1} R))
    (h : ∀ X, (S.map (PresheafOfModules.evaluation R X)).Exact) : S.Exact := by
  rw [S.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  ext X : 1
  have hz : IsZero ((PresheafOfModules.evaluation R X).obj S.homology) :=
    ((S.map (PresheafOfModules.evaluation R X)).exact_iff_isZero_homology.mp (h X)).of_iso
      (S.mapHomologyIso (PresheafOfModules.evaluation R X)).symm
  exact hz.eq_of_src _ _

section Presentation

attribute [local instance] SheafOfModules.siteTensor_identity_locallyInjective
  SheafOfModules.siteTensor_identity_locallySurjective

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {A : Type (u + 1)} [CommRing A]
  {B : Sheaf J CommRingCat.{u + 1}} (α : realizationRing J A ⟶ B)

private theorem scalarPresentation :
    Nonempty (siteConstantModulePresheafGeneral (C := C) A ⋙
        (sectionExtension
          (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)) ≫ α.hom) ⋙
          PresheafOfModules.sheafification
            (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B).obj)) ≅
      SheafOfModules.flatScalarRealization J α) := by
  let η := realizationRingUnit J A
  let := (realizationRingUnit_locallyBijective J A).1
  let := (realizationRingUnit_locallyBijective J A).2
  let β := toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)) ≫ α.hom
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (realizationRing J A)
  let S := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B
  let r := SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map α)
  let E := SheafOfModules.flatScalarExtension J α
  obtain ⟨_, _, h⟩ := SheafOfModules.scalarLocalizationCoefficientAdjunctionOfUniverses α
  obtain ⟨a, _⟩ := h E (fun _ ↦ rfl) (by
    intro M N f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl)
  -- Both left adjoints have the same scalar-restriction right adjoint.
  let a₁ := (sectionAdjunction β).comp
    (PresheafOfModules.sheafificationAdjunction (𝟙 S.obj))
  let a₂ := (PresheafOfModules.sheafificationAdjunction η).comp a
  let a₁' : sectionExtension β ⋙ PresheafOfModules.sheafification (𝟙 S.obj) ⊣
      r ⋙ (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars η) :=
    a₁.ofNatIsoRight (Iso.refl _)
  refine ⟨?_⟩
  exact Functor.isoWhiskerLeft (siteConstantModulePresheafGeneral (C := C) A)
      (a₁'.leftAdjointUniq a₂) ≪≫
    (Functor.associator (siteConstantModulePresheafGeneral (C := C) A)
      (PresheafOfModules.sheafification η) E).symm

private theorem scalarRealization_acyclic
    (K : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (hk : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat K) (ha : K.Acyclic) :
    (((SheafOfModules.flatScalarRealization J α).mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
  let P := siteConstantModulePresheafGeneral (C := C) A
  let β := toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)) ≫ α.hom
  let T := sectionExtension β
  let S := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B
  let L := PresheafOfModules.sheafification (𝟙 S.obj)
  let : P.Additive := ⟨by intro M N f g; ext X : 1; rfl⟩
  let : T.Additive := sectionExtension_additive β
  let : L.Additive := Functor.additive_of_preserves_binary_products L
  have hz : QuasiIso (0 : (0 : CochainComplex (ModuleCat.{u + 1} A) ℤ) ⟶ K) := by
    rw [quasiIso_iff]
    intro n
    exact (quasiIsoAt_iff_exactAt _ n
      (HomologicalComplex.acyclic_of_isZero _ (isZero_zero _) n)).2 (ha n)
  -- Evaluation turns this into ordinary extension of scalars of the original complex.
  have hp : (((P ⋙ T).mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
    intro n
    apply presheaf_exact_of_evaluation
    intro X
    let ρ : A →+* B.obj.obj X := (β.app X).hom
    let E := ModuleCat.extendScalars.{u + 1, u + 1, u + 1} ρ
    let : E.Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} ρ).left_adjoint_additive
    let : E.PreservesKFlatQuasiIso := ModuleCat.extendScalars_preservesKFlatQuasiIso ρ
    have hm := E.quasiIso_mapHomologicalComplex_map_of_kFlat
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat.prop_zero hk
      (0 : (0 : CochainComplex (ModuleCat.{u + 1} A) ℤ) ⟶ K)
    have he : ((E.mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
      intro i
      exact (exactAt_iff_of_quasiIsoAt
        ((E.mapHomologicalComplex (.up ℤ)).map
          (0 : (0 : CochainComplex (ModuleCat.{u + 1} A) ℤ) ⟶ K)) i).1
        (HomologicalComplex.acyclic_of_isZero _
          ((E.mapHomologicalComplex (.up ℤ)).map_isZero (isZero_zero _)) i)
    exact he n
  -- Exact sheafification and the natural presentation transfer acyclicity.
  have hs := hp.map L
  obtain ⟨i⟩ := scalarPresentation J α
  exact hs.of_iso ((NatIso.mapHomologicalComplex i (.up ℤ)).app K)

end Presentation

/-- The terminal scalar realization `L` preserves quasi-isomorphisms between categorical
K-flat complexes.

Source: Hemo--Richarz--Scholbach, Lemma 4.1(1), Remark 3.2.
(blueprint: new-lem-zl-contractible-realization-kflat-data).

Proof: write `A = O_sec(U)` and `E` for the internal/section module equivalence. As in
the braided-data node, `E L(M)` is naturally the sheafification of
`P_M : V ↦ O_sec(V) ⊗_A M`. Let `f : K → K'` be a quasi-isomorphism between K-flat
complexes of `A`-modules. Its cone is acyclic by the cone criterion and K-flat by the
triangulated closure of K-flat complexes. The change-of-rings lemma for `A → O_sec(V)`,
applied to `0 → Cone f`, shows that `O_sec(V) ⊗_A Cone f` is acyclic for every `V`.
Hence `P_{Cone f}` is acyclic sectionwise, and by exactness of module sheafification
its sheafification is acyclic. The presentation is natural, so it holds termwise for
the cone, and `E L(Cone f)` is acyclic; `E` reflects acyclicity, so `L(Cone f)` is
acyclic. As `L` is additive, `L(Cone f) ≅ Cone(L f)`, and the cone criterion shows
that `L f` is a quasi-isomorphism. -/
theorem contractible_realization_kflat_data
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (O : Sheaf J Ab.{u + 1}) [MonObj O] [IsCommMonObj O]
    (U : C) (hU : IsTerminal U) :
    Nonempty (terminalScalarRealization J O U hU).PreservesKFlatQuasiIso := by
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J O
  let : e.inverse.Additive := Functor.additive_of_preserves_binary_products e.inverse
  refine ⟨Functor.PreservesKFlatQuasiIso.mk' _ ?_⟩
  intro K hk ha
  exact (scalarRealization_acyclic J (scalarMap J O U hU) K hk ha).map e.inverse

end AlgebraicGeometry.ProEtale.CondensedRing.Evaluation
